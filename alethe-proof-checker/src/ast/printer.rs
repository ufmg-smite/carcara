use crate::ast::*;
use std::{fmt, io};

pub fn print_proof(proof: &Proof) -> io::Result<()> {
    let mut stdout = io::stdout();
    (AlethePrinter { inner: &mut stdout }).write_proof(proof)
}

fn get_premise_index<'a>(
    (depth, command_index): (usize, usize),
    commands_stack: &[(usize, &'a [ProofCommand])],
) -> &'a str {
    commands_stack[depth].1[command_index].index()
}

trait PrettyPrint {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()>;
}

struct AlethePrinter<'a> {
    inner: &'a mut dyn io::Write,
}

impl<'a> PrettyPrint for AlethePrinter<'a> {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()> {
        // This iterates through the commands in a proof in a similar way as the checker, using an
        // explicit stack
        let mut commands_stack = vec![(0, proof.commands.as_slice())];
        while let Some(&(i, commands)) = commands_stack.last() {
            if i == commands.len() {
                commands_stack.pop();
                continue;
            }
            match &commands[i] {
                ProofCommand::Assume { index, term } => {
                    write!(self.inner, "(assume {} {})", index, term)?
                }
                ProofCommand::Step(s) => self.write_step(s, &commands_stack)?,
                ProofCommand::Subproof {
                    commands: inner_commands,
                    assignment_args,
                    variable_args,
                } => {
                    let end_step_index = inner_commands
                        .last()
                        .and_then(|s| match s {
                            ProofCommand::Step(s) => Some(s.index.clone()),
                            _ => None,
                        })
                        .unwrap();
                    write!(self.inner, "(anchor :step {}", end_step_index)?;

                    if !variable_args.is_empty() || !assignment_args.is_empty() {
                        write!(self.inner, " :args (")?;
                        let mut is_first = true;
                        for (name, sort) in variable_args {
                            if !is_first {
                                write!(self.inner, " ")?
                            }
                            is_first = false;
                            write!(self.inner, "({} {})", name, sort)?
                        }
                        for (name, value) in assignment_args {
                            if !is_first {
                                write!(self.inner, " ")?
                            }
                            is_first = false;
                            write!(self.inner, "(:= ({} {}) {})", name, value.sort(), value)?;
                        }
                        write!(self.inner, ")")?;
                    }
                    writeln!(self.inner, ")")?;

                    // We increment this layer's index so when we comeback from the subproof and
                    // pop the top layer, we are already on the next command after the subproof
                    commands_stack.last_mut().unwrap().0 += 1;
                    commands_stack.push((0, inner_commands));
                    continue;
                }
            }
            writeln!(self.inner)?;
            commands_stack.last_mut().unwrap().0 += 1;
        }

        Ok(())
    }
}

impl<'a> AlethePrinter<'a> {
    fn write_step(
        &mut self,
        step: &ProofStep,
        commands_stack: &[(usize, &[ProofCommand])],
    ) -> io::Result<()> {
        write!(self.inner, "(step {} (cl", step.index)?;

        for t in &step.clause {
            write!(self.inner, " {}", t)?;
        }
        write!(self.inner, ")")?;

        write!(self.inner, " :rule {}", step.rule)?;

        if let [head, tail @ ..] = step.premises.as_slice() {
            let head = get_premise_index(*head, commands_stack);
            write!(self.inner, " :premises ({}", head)?;
            for premise in tail {
                let premise = get_premise_index(*premise, commands_stack);
                write!(self.inner, " {}", premise)?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.args.as_slice() {
            write!(self.inner, " :args (")?;
            self.write_proof_arg(head)?;
            for arg in tail {
                write!(self.inner, " ")?;
                self.write_proof_arg(arg)?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.discharge.as_slice() {
            write!(self.inner, " :discharge ({}", head)?;
            for index in tail {
                write!(self.inner, " {}", index)?;
            }
            write!(self.inner, ")")?;
        }

        write!(self.inner, ")")?;
        Ok(())
    }

    fn write_proof_arg(&mut self, arg: &ProofArg) -> io::Result<()> {
        match arg {
            ProofArg::Term(t) => write!(self.inner, "{}", t),
            ProofArg::Assign(name, value) => {
                write!(self.inner, "(:= {} {})", name, value)
            }
        }
    }
}

fn write_s_expr<H, T>(f: &mut fmt::Formatter, head: H, tail: &[T]) -> fmt::Result
where
    H: fmt::Display,
    T: fmt::Display,
{
    write!(f, "({}", head)?;
    for e in tail {
        write!(f, " {}", e)?;
    }
    write!(f, ")")
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> fmt::Result {
        match self {
            Term::Terminal(t) => write!(f, "{}", t),
            Term::App(func, args) => write_s_expr(f, func, args),
            Term::Op(op, args) => write_s_expr(f, op, args),
            Term::Sort(sort) => write!(f, "{}", sort),
            Term::Quant(quantifier, bindings, term) => {
                write!(f, "({} {} {})", quantifier, bindings, term)
            }
            Term::Choice((symbol, sort), term) => {
                write!(f, "(choice (({} {})) {})", symbol, sort, term)
            }
            Term::Let(bindings, term) => {
                write!(f, "(let {} {})", bindings, term)
            }
        }
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Integer(i) => write!(f, "{}", i),
            Terminal::Real(r) => {
                let float_value = r.numer().to_f64().unwrap() / r.denom().to_f64().unwrap();

                // We use the `Debug` (that is, "{:?}") representation because it sets a minimum
                // precision of 1 digit. That means we always print 1.0 as "1.0", instead of as "1"
                write!(f, "{:?}", float_value)
            }
            Terminal::String(s) => write!(f, "\"{}\"", s),
            Terminal::Var(iden, _) => write!(f, "{}", iden),
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Simple(s) => write!(f, "{}", s),
            Identifier::Indexed(s, indices) => write_s_expr(f, format!("_ {}", s), indices),
        }
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Index::Numeral(n) => write!(f, "{}", n),
            Index::Symbol(s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for Quantifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            }
        )
    }
}

impl fmt::Display for BindingList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.as_slice() {
            [] => write!(f, "()"),
            [head, tail @ ..] => {
                write!(f, "(({} {})", head.0, head.1)?;
                for (var, term) in tail {
                    write!(f, " ({} {})", var, term)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Function sorts should never be displayed, so the exact format we use is of little
            // importance
            Sort::Function(args) => write_s_expr(f, "Func", args),
            Sort::Atom(name, args) => match args.len() {
                0 => write!(f, "{}", name),
                _ => write_s_expr(f, name, args),
            },
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
            Sort::Array(x, y) => write_s_expr(f, "Array", &[x, y]),
        }
    }
}
