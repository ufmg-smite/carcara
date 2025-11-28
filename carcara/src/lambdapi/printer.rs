use super::*;
use pretty::RcDoc;
use std::io::{self};

pub const DEFAULT_WIDTH: usize = 120;
pub const DEFAULT_INDENT: isize = 4;

pub const WHITE_SPACE: &'static str = " ";
const LBRACE: &'static str = "{";
const RBRACE: &'static str = "}";
const COMMA: &'static str = ",";
const CLAUSE_NIL: &'static str = "▩";

const NIL: &'static str = "⧈";

macro_rules! concat {
    ($l:expr => $( $r:expr ) => * ) => { $l$(.append($r))* };
}

pub trait PrettyPrint {
    fn to_doc(&self) -> RcDoc<'_, ()>;

    fn to_pretty_with_width(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }

    fn to_pretty(&self) -> String {
        self.to_pretty_with_width(DEFAULT_WIDTH)
    }

    fn render(&self, f: &mut impl io::Write) -> io::Result<()> {
        let doc = self.to_doc();
        doc.render(DEFAULT_WIDTH, f)
    }

    fn render_fmt(&self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
        let doc = self.to_doc();
        doc.render_fmt(DEFAULT_WIDTH, f)
    }
}

pub trait PrettyHelper<'a, T: 'a>: Sized {
    fn surround(self, pre: &'a str, post: &'a str) -> Self;

    fn surround_doc(self, pre: RcDoc<'a, T>, post: RcDoc<'a, T>) -> Self;

    fn semicolon(self) -> Self;

    fn begin_end(self) -> Self {
        self.surround_doc(
            RcDoc::line().append(RcDoc::text("begin").append(RcDoc::line())),
            RcDoc::line().append(RcDoc::text("end")),
        )
    }

    fn parens(self) -> Self {
        self.surround("(", ")")
    }

    fn braces(self) -> Self {
        self.surround(LBRACE, RBRACE)
    }

    fn spaces(self) -> Self {
        self.surround(WHITE_SPACE, WHITE_SPACE)
    }
}

impl<'a, A> PrettyHelper<'a, A> for RcDoc<'a, A> {
    fn surround(self, l: &'a str, r: &'a str) -> Self {
        RcDoc::text(l).append(self).append(RcDoc::text(r))
    }

    fn surround_doc(self, pre: RcDoc<'a, A>, post: RcDoc<'a, A>) -> Self {
        pre.append(self).append(post)
    }

    fn semicolon(self) -> Self {
        self.append(RcDoc::text(";"))
    }
}

#[inline]
fn arrow<'a>() -> RcDoc<'a, ()> {
    RcDoc::text("→")
}

#[inline]
fn semicolon<'a>() -> RcDoc<'a, ()> {
    RcDoc::text(";")
}

#[inline]
fn symbol<'a>() -> RcDoc<'a, ()> {
    RcDoc::text("symbol")
}

#[inline]
fn is<'a>() -> RcDoc<'a, ()> {
    text("≔").spaces()
}

#[inline]
fn space<'a>() -> RcDoc<'a, ()> {
    RcDoc::space()
}

#[inline]
fn text<'a>(s: &'a str) -> RcDoc<'a, ()> {
    RcDoc::text(s)
}

#[inline]
fn colon<'a>() -> RcDoc<'a, ()> {
    text(":")
}

#[inline]
fn implicit<'a, T: PrettyPrint>(x: &'a Option<Box<T>>) -> RcDoc<'a, ()> {
    x.as_ref().map_or(text("_"), |x| x.to_doc())
}

#[inline]
fn tab<'a>() -> RcDoc<'a, ()> {
    RcDoc::text(" ".repeat(DEFAULT_INDENT as usize))
}

#[inline]
fn line<'a>() -> RcDoc<'a, ()> {
    RcDoc::line()
}

impl PrettyPrint for BuiltinSort {
    fn to_doc(&self) -> RcDoc<'_,()> {
        match self {
            BuiltinSort::Bool => text("o"),
            BuiltinSort::Int => text("int"),
            BuiltinSort::Arrow(a, b) => concat! {
                a.to_doc()
                => text("⤳").spaces()
                => b.to_doc()
            },
        }
    }
}

impl PrettyPrint for Term {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            Term::Alethe(term) => term.to_doc(),
            Term::TermId(id) => text(id),
            Term::Underscore => text("_"),
            Term::Sort(sort) => sort.to_doc(),
            Term::Terms(terms) => {
                RcDoc::intersperse(terms.iter().map(|term| term.to_doc()), space()).parens()
            }
            Term::Function(terms) => {
                RcDoc::intersperse(terms.iter().map(|term| term.to_doc()), arrow().spaces())
            }
            Term::Nat(n) => RcDoc::text(format!("(to_nat {})", n)), //FIXME: Lambdapi builtin of Nat conflict with Int
            Term::Int(i) => {
                if i.is_negative() {
                    RcDoc::text(format!("(— {})", i.clone().abs())) //FIXME: Carcara should use Operator::Minus insteand of Int with a negative value
                } else {
                    RcDoc::text(format!("{}", i))
                }
            }
        }
    }
}

impl PrettyPrint for Modifier {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            Modifier::Constant => text("constant"),
            Modifier::Opaque => text("opaque"),
        }
    }
}

impl PrettyPrint for SortedTerm {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        self.0.to_doc().append(space()).append(self.1.to_doc())
    }
}

impl PrettyPrint for VecN {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        // Take the last element because we will reverse the list latter so: last l = first (rev l)
        let (first, elems) = self.0.split_last().expect("distinct should not be empty");

        // Generate the root of the vector: (cons _  term1 □)
        let first_doc = concat! {
            text("cons") // constructor
            => first.to_doc().spaces() // element
            => text(NIL)
        }
        .parens();

        // Generate a vector (cons _  term_n ... (cons _  term2 (cons _  term1 □))

        elems.iter().fold(first_doc, |acc, elem| {
            concat! {
                text("cons") // constructor
                => elem.to_doc().spaces() // element
                => acc // rest of the vector
            }
            .parens()
        })
    }
}

impl PrettyPrint for List {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        self.0.iter().fold(text("□"), |acc, elem| {
            concat! {
                elem.to_doc().clone()
                => text("⸬").spaces()
                => acc
            }
        })
    }
}

impl PrettyPrint for LTerm {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            LTerm::True => text("⊤"),
            LTerm::False => text("⊥"),
            LTerm::NAnd(terms) => RcDoc::intersperse(
                terms.into_iter().map(|term| term.to_doc()),
                text("∧").spaces(),
            )
            .parens(),
            LTerm::NOr(terms) => RcDoc::intersperse(
                terms.into_iter().map(|term| term.to_doc()),
                text("∨").spaces(),
            )
            .parens(),
            LTerm::Neg(Some(term)) => text("¬")
                .append(space())
                .append(term.to_doc().parens())
                .parens(),
            LTerm::Neg(None) => text("¬"),
            LTerm::Proof(term) => text("π̇").append(space()).append(term.to_doc()),
            LTerm::ClassicProof(term) => text("π").append(space()).append(term.to_doc()),
            LTerm::Clauses(terms) => {
                if terms.is_empty() {
                    text(CLAUSE_NIL)
                } else {
                    RcDoc::intersperse(
                        terms.into_iter().map(|term| term.to_doc()),
                        line().append(text("⟇").spaces()),
                    )
                    .append(line().append(text("⟇").append(space()).append(text(CLAUSE_NIL))))
                    .group()
                    .parens()
                    .nest(DEFAULT_INDENT)
                }
            }
            LTerm::Eq(l, r) => l
                .to_doc()
                .append(text("=").spaces())
                .append(r.to_doc())
                .parens(),
            LTerm::Iff(l, r) => l
                .to_doc()
                .append(text("⇔").spaces())
                .append(r.to_doc())
                .parens(),
            LTerm::Implies(l, r) => l
                .to_doc()
                .parens()
                .append(space().append(text("⇒")).append(space()))
                .append(r.to_doc().parens())
                .parens(),
            LTerm::Exist(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    text("`∃")
                        .append(space())
                        .append(
                            b.0.to_doc()
                                .append(text(":").spaces().append(b.1.to_doc()))
                                .parens(),
                        )
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(term.to_doc())
            .parens(),
            LTerm::Forall(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    text("`∀")
                        .append(space())
                        .append(
                            b.0.to_doc()
                                .append(text(":").spaces().append(b.1.to_doc()))
                                .parens(),
                        )
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(space())
            .append(term.to_doc())
            .parens(),
            LTerm::Resolution(flag, pivot, a, b, hyp_pivot_a, hyp_pivot_b) => flag
                .then(|| text("resolutionₗ"))
                .unwrap_or(text("resolutionᵣ"))
                .append(space())
                .append(RcDoc::intersperse(
                    [
                        implicit(pivot),
                        implicit(a),
                        implicit(b),
                        hyp_pivot_a.to_doc(),
                        hyp_pivot_b.to_doc(),
                    ],
                    space(),
                )),
            LTerm::Distinct(v) => concat! {
                text("distinct")
                => v.to_doc()
            }
            .parens(),
            LTerm::List(l) => l.to_doc().parens(),
            LTerm::Choice(bindings, p) => concat!(
                RcDoc::intersperse(bindings.0.iter().map(|b| {
                    text("`ϵ")
                        .append(space())
                        .append(b.0.to_doc())
                        .append(COMMA)
                }), space())
                => space()
                => p.to_doc()
            )
            .parens(),
        }
    }
}

impl PrettyPrint for Param {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        text(self.0.as_str())
            .append(colon().spaces())
            .append(self.1.to_doc())
    }
}

impl PrettyPrint for ProofStep {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            ProofStep::Admit => RcDoc::text("admit").append(semicolon()),
            ProofStep::Apply(t, subproofs) => RcDoc::text("apply")
                .append(space())
                .append(t.to_doc())
                .append(subproofs.0.is_some().then(|| space()))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .into_iter()
                            .map(|p| {
                                line()
                                    .append(text(LBRACE).append(line()))
                                    .append(tab()) //FIXME: we append a tab because `assume` is not incremented (hack)
                                    .append(p.to_doc().nest(4))
                                    .append(line().append(RBRACE))
                            })
                            .collect_vec(),
                        RcDoc::nil(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Assume(params) => text("assume")
                .append(space())
                .append(RcDoc::intersperse(params.iter().map(|p| text(p)), space()))
                .append(semicolon()),
            ProofStep::Have(name, r#type, steps) => text("have")
                .append(space())
                .append(text(name))
                .append(colon().spaces())
                .append(r#type.to_doc())
                .append(space())
                .append(LBRACE)
                .append(line())
                .append(RcDoc::intersperse(
                    steps.into_iter().map(|s| s.to_doc()),
                    line(),
                ))
                .append(line())
                .nest(DEFAULT_INDENT)
                .append(text(RBRACE))
                .append(semicolon()),
            ProofStep::Change(t) => text("change")
                .append(space())
                .append(t.to_doc())
                .semicolon(),
            ProofStep::Reflexivity => text("reflexivity").append(semicolon()),
            ProofStep::Refine(func, subproofs) => text("refine")
                .append(space())
                .append(func.to_doc())
                .append(space())
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .into_iter()
                            .map(|p| RcDoc::braces(p.to_doc()))
                            .collect_vec(),
                        line(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Try(t) => text("try").append(space()).append(t.to_doc()),
            ProofStep::Rewrite(flag, pattern, h, args, subproofs) => text("rewrite")
                .append(flag.then(|| text("left").spaces()).unwrap_or(text("")))
                .append(space())
                .append(pattern.as_ref().map_or(text(""), |pattern| {
                    text(".").append(text(pattern.as_str())).append(space())
                }))
                .append(
                    h.to_doc()
                        .append(args.is_empty().then(|| RcDoc::nil()).unwrap_or(space()))
                        .append(RcDoc::intersperse(
                            args.iter().map(|a| a.to_doc().parens()),
                            space(),
                        )), //.spaces(),
                )
                .append(subproofs.0.is_some().then(|| space()))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .into_iter()
                            .map(|p| {
                                line()
                                    .append(text(LBRACE).append(line()))
                                    .append(tab()) //FIXME: we append a tab because `assume` is not incremented (hack)
                                    .append(p.to_doc().nest(4))
                                    .append(line().append(RBRACE))
                            })
                            .collect_vec(),
                        RcDoc::nil(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Symmetry => text("symmetry").append(semicolon()),
            ProofStep::Simplify(ss) if ss.is_empty() => text("simplify").append(semicolon()),
            ProofStep::Simplify(ss) => ss.into_iter().fold(RcDoc::nil(), |acc, s| {
                // We have to generate one simplify per term because Lambdapi does not support multiple arguments for simplify
                acc.append(text("simplify").append(space()).append(text(s)))
                    .append(semicolon())
            }),
            ProofStep::Set(name, def) => text("set").append(space()).append(
                text(name)
                    .append(is())
                    .append(def.to_doc())
                    .append(semicolon()),
            ),
            ProofStep::Varmap(name, list) => text("set").append(space()).append(
                text(name)
                    .append(is())
                    .append(
                        RcDoc::intersperse(
                            list.into_iter().map(|term| term.to_doc()),
                            text("⸬").spaces(),
                        )
                        .append(text("⸬").spaces())
                        .append(NIL),
                    )
                    .append(semicolon()),
            ),
            ProofStep::Why3 => text("why3").append(semicolon()),
            ProofStep::Eval(t) => text("eval").append(t.to_doc().spaces()).append(semicolon()),
        }
    }
}

impl PrettyPrint for Proof {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::intersperse(self.0.iter().map(|step| step.to_doc()), line())
    }
}

impl PrettyPrint for Command {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        match self {
            Command::RequireOpen(path) => text("require open")
                .append(space())
                .append(text(path))
                .semicolon(),
            Command::Symbol(modifier, name, params, r#text, proof) => modifier
                .as_ref()
                .map(|m| m.to_doc().append(space()))
                .unwrap_or(RcDoc::nil())
                .append(symbol())
                .append(space())
                .append(name)
                .append(params.is_empty().then(|| RcDoc::nil()).unwrap_or(
                    RcDoc::intersperse(params.into_iter().map(|p| p.to_doc()), space()).spaces(),
                ))
                .append(colon().spaces())
                .append(r#text.to_doc())
                .append(
                    proof
                        .as_ref()
                        .map_or(RcDoc::nil(), |p| is().append(p.to_doc().begin_end())),
                )
                .append(semicolon()),
            Command::Definition(name, params, r#type, definition) => symbol()
                .append(space())
                .append(text(name))
                .append(params.is_empty().then(|| RcDoc::nil()).unwrap_or(
                    RcDoc::intersperse(params.into_iter().map(|p| p.to_doc()), space()).spaces(),
                ))
                .append(
                    r#type
                        .as_ref()
                        .map_or(RcDoc::nil(), |ty| colon().spaces().append(ty.to_doc())),
                )
                .append(
                    definition
                        .as_ref()
                        .map_or(RcDoc::nil(), |def| is().append(def.to_doc())),
                )
                .append(semicolon()),
            Command::Rule(l, r) => text("rule")
                .append(space())
                .append(l.to_doc())
                .append(text("↪").spaces())
                .append(r.to_doc())
                .append(semicolon()),
        }
    }
}

impl<'a> PrettyPrint for ProofFile {
    fn to_doc(&self) -> RcDoc<'_, ()> {
        RcDoc::intersperse(
            self.requires
                .iter()
                .chain(self.definitions.iter())
                .chain(self.content.iter())
                .map(|cmd| cmd.to_doc()),
            line().append(line()),
        )
    }
}

pub trait PrettyPrintAx {
    fn to_ax(&self) -> RcDoc<'_, ()>;

    fn to_pretty_with_width(&self, width: usize) -> String {
        let mut w: Vec<u8> = Vec::new();
        self.to_ax().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }

    fn to_pretty(&self) -> String {
        self.to_pretty_with_width(DEFAULT_WIDTH)
    }

    fn render_ax(&self, f: &mut impl io::Write) -> io::Result<()> {
        let doc = self.to_ax();
        doc.render(DEFAULT_WIDTH, f)
    }
}

impl PrettyPrintAx for Command {
    fn to_ax(&self) -> RcDoc<'_, ()> {
        match self {
            Command::RequireOpen(path) => text("require open")
                .append(space())
                .append(text(path))
                .semicolon(),
            Command::Symbol(modifier, name, params, r#text, ..) => modifier
                .as_ref()
                .map(|m| match m {
                    Modifier::Constant => m.to_doc().append(space()),
                    Modifier::Opaque => RcDoc::nil(),
                })
                .unwrap_or(RcDoc::nil())
                .append(symbol())
                .append(space())
                .append(name)
                .append(params.is_empty().then(|| RcDoc::nil()).unwrap_or(
                    RcDoc::intersperse(params.into_iter().map(|p| p.to_doc()), space()).spaces(),
                ))
                .append(colon().spaces())
                .append(r#text.to_doc())
                .append(semicolon()),
            Command::Definition(name, params, r#type, definition) => symbol()
                .append(space())
                .append(text(name))
                .append(params.is_empty().then(|| RcDoc::nil()).unwrap_or(
                    RcDoc::intersperse(params.into_iter().map(|p| p.to_doc()), space()).spaces(),
                ))
                .append(
                    r#type
                        .as_ref()
                        .map_or(RcDoc::nil(), |ty| colon().spaces().append(ty.to_doc())),
                )
                .append(
                    definition
                        .as_ref()
                        .map_or(RcDoc::nil(), |def| is().append(def.to_doc())),
                )
                .append(semicolon()),
            Command::Rule(l, r) => text("rule")
                .append(space())
                .append(l.to_doc())
                .append(text("↪").spaces())
                .append(r.to_doc())
                .append(semicolon()),
        }
    }
}

impl<'a> PrettyPrintAx for AxiomsFile {
    fn to_ax(&self) -> RcDoc<'_, ()> {
        RcDoc::intersperse(
            self.requires
                .iter()
                .chain(self.content.iter())
                .map(|cmd| cmd.to_ax()),
            line().append(line()),
        )
    }
}
