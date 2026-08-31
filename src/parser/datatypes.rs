use super::{Parser, ParserError, Reserved, Token};
use crate::{
    CarcaraResult,
    ast::{
        MatchCase, MatchPattern, Rc, Sort, Term,
        pool::{Datatype, DatatypeConstructor},
    },
};
use indexmap::IndexMap;

impl<'p, 's> Parser<'p, 's> {
    /// Parses a `declare-datatype` command.
    ///
    /// Inserts the datatype as a sort definition in the parser state.
    pub(super) fn parse_declare_datatype(&mut self) -> CarcaraResult<()> {
        let name = self.expect_symbol()?;

        // To allow for recursive datatypes, we rely on `parse_datatype_declaration` to declare the
        // datatype, after having parsed the sort parameters
        let dt = self.parse_datatype_declaration(Some(&name))?;

        self.expect_token(Token::CloseParen)?;
        self.register_constructors(&name, &dt);
        self.pool.add_datatype(name, dt);
        Ok(())
    }

    /// Parses a `declare-datatypes` command.
    ///
    /// Inserts all datatype as a sort definitions in the parser state.
    pub(super) fn parse_declare_datatypes(&mut self) -> CarcaraResult<()> {
        let start_pos = self.current_position;
        self.expect_token(Token::OpenParen)?;
        let declarations = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let arity_pos = p.current_position;
                let arity = p.expect_numeral()?;
                let arity = arity
                    .to_usize()
                    .ok_or(p.err(ParserError::InvalidSortArity(arity), arity_pos))?;
                p.state.datatype_declarations.insert(name.clone(), arity);
                p.expect_token(Token::CloseParen)?;
                Ok((name, arity))
            },
            true,
        )?;

        self.expect_token(Token::OpenParen)?;
        let datatypes = self.parse_sequence(
            |p| {
                let pos = p.current_position;
                let dt = p.parse_datatype_declaration(None)?;
                Ok((pos, dt))
            },
            true,
        )?;
        if datatypes.len() != declarations.len() {
            let err =
                ParserError::WrongNumberOfDatatypeDeclarations(declarations.len(), datatypes.len());
            return Err(self.err(err, start_pos));
        }

        for ((name, arity), (pos, dt)) in declarations.into_iter().zip(datatypes) {
            if dt.params.len() != arity {
                let err = ParserError::WrongNumberOfDatatypeParams(arity, dt.params.len());
                return Err(self.err(err, pos));
            }
            self.register_constructors(&name, &dt);
            self.pool.add_datatype(name, dt);
        }
        self.expect_token(Token::CloseParen)?;
        Ok(())
    }

    /// Parses a datatype declaration, either `(<constructor>+)` or `(par (<symbol>+)
    /// (<constructor>+))`.
    ///
    /// Returns the datatype's parameters and constructors. If `late_declare` is `Some`, declare
    /// the datatype into the parser state `datatype_declarations`, with the given name and parsed
    /// arity. This is required for recursive datatypes in the `declared-datatype` command. In these
    /// cases, we must declare the datatype before parsing its constructors but after knowing its
    /// arity, which can only be done after parsing the sort parameters.
    fn parse_datatype_declaration(
        &mut self,
        late_declare: Option<&str>,
    ) -> CarcaraResult<Datatype> {
        self.expect_token(Token::OpenParen)?;
        let params = if self.current_token == Token::ReservedWord(Reserved::Par) {
            self.next_token()?;
            self.state.symbol_table.push_scope();
            self.expect_token(Token::OpenParen)?;
            let params = self.parse_sequence(
                |p| {
                    let name = p.expect_symbol()?;
                    let sort = p.pool.add_sort(Sort::Type);
                    p.declare_symbol(name.clone(), sort);
                    Ok(name)
                },
                true,
            )?;
            self.expect_token(Token::OpenParen)?;
            params
        } else {
            Vec::new()
        };

        // If `late_declare` is provided, declare the datatype after knowing its arity.
        if let Some(name) = late_declare {
            self.state
                .datatype_declarations
                .insert(name.to_owned(), params.len());
        }

        let constructors: IndexMap<_, _> = self
            .parse_sequence(Self::parse_datatype_constructor, true)?
            .into_iter()
            .collect();
        if !params.is_empty() {
            self.expect_token(Token::CloseParen)?;
            self.state.symbol_table.pop_scope();
        }
        Ok(Datatype { params, constructors })
    }

    /// Register each constructor from a datatype into the symbol table, with the appropriate type.
    ///
    /// The sort of each constructor will be a parametric sort that takes the datatype's sort
    /// parameters (if any), and returns a function sort that takes the constructor's selector sorts
    /// (if any) and finally returns the datatype sort. In the general case, the sort will be:
    /// `(par (<params>...) (-> <args>... <datatype>))`
    ///
    /// For example, the `some` constructor of `(Option T)` will have sort:
    /// `(par (T) (-> T (Option T)))`.
    ///
    /// If there are no sort parameters, the `par` construction is omitted; if there are no
    /// selectors, the `->` construction is omitted.
    fn register_constructors(&mut self, datatype_name: &str, datatype: &Datatype) {
        let return_sort = Sort::Datatype {
            name: datatype_name.to_owned().into_boxed_str(),
            args: datatype
                .params
                .iter()
                .map(|param| self.pool.add_sort(Sort::Var(param.clone())))
                .collect(),
        };
        let return_sort = self.pool.add_sort(return_sort);
        for (name, cons) in &datatype.constructors {
            let inner_sort = if cons.selectors.is_empty() {
                return_sort.clone()
            } else {
                let sorts: Vec<_> = cons
                    .selectors
                    .iter()
                    .map(|(_, sort)| sort.clone())
                    .chain([return_sort.clone()])
                    .collect();
                self.pool.add_sort(Sort::Function(sorts))
            };
            let sort = if datatype.params.is_empty() {
                inner_sort
            } else {
                self.pool
                    .add_sort(Sort::Par(datatype.params.clone(), inner_sort))
            };
            self.declare_symbol(name.clone(), sort);

            // If we are supporting legacy tester syntax, register a function symbol named
            // `is-<cons>`, that serves the same purpose as the newer `(_ is <cons>)`.
            if self.config.allow_legacy_tester_syntax {
                let sort =
                    Sort::Function(vec![return_sort.clone(), self.pool.add_sort(Sort::Bool)]);
                let sort = self.pool.add_sort(sort);
                self.declare_symbol(format!("is-{}", name), sort);
            }

            self.register_selectors(cons, &return_sort, &datatype.params);
        }
    }

    /// Register each selector from the given constructor into the symbol table, with the
    /// appropriate type.
    ///
    /// The sort of each selector function will be a parametric sort that takes the datatype's sort
    /// parameters (if any), and returns a function sort that takes the datatype sort and returns
    /// the selector sort. In the general case, the sort will be:
    /// `(par (<params>...) (-> <datatype> <selector_sort>))`
    ///
    /// For example, the `value` selector of the `some` constructor of `(Option T)` will have sort:
    /// `(par (T) (-> (Option T) T))`.
    ///
    /// If there are no sort parameters, the `par` construction is omitted.
    fn register_selectors(
        &mut self,
        constructor: &DatatypeConstructor,
        datatype_sort: &Rc<Sort>,
        sort_params: &[String],
    ) {
        for (name, selector_sort) in &constructor.selectors {
            let inner_sort = self.pool.add_sort(Sort::Function(vec![
                datatype_sort.clone(),
                selector_sort.clone(),
            ]));
            let sort = if sort_params.is_empty() {
                inner_sort
            } else {
                self.pool
                    .add_sort(Sort::Par(sort_params.to_vec(), inner_sort))
            };
            self.declare_symbol(name.clone(), sort);
        }
    }

    /// Parses a datatype constructor, of the form `(<symbol> (<symbol> <sort>)*)`.
    fn parse_datatype_constructor(&mut self) -> CarcaraResult<(String, DatatypeConstructor)> {
        self.expect_token(Token::OpenParen)?;
        let name = self.expect_symbol()?;
        let selectors = self.parse_sequence(Self::parse_sorted_var, false)?;
        Ok((name, DatatypeConstructor { selectors }))
    }

    /// Parses a `match` term. This method assumes that the `(` and `match` tokens were already
    /// consumed.
    pub(super) fn parse_match(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        let matched_term = self.parse_term()?;
        let sort = self.pool.sort(&matched_term);
        let Sort::Datatype { name, .. } = sort.as_ref() else {
            return Err(self.err(ParserError::ExpectedDatatypeSort(sort.clone()), head_pos));
        };
        let datatype = self.pool.get_datatype(name).clone();

        // Parse cases
        self.expect_token(Token::OpenParen)?;
        let cases =
            self.parse_sequence(|p| p.parse_match_case(&sort, &datatype.constructors), true)?;

        self.expect_token(Token::CloseParen)?;

        // Check that all case bodies have the same sort
        for w in cases.windows(2) {
            let sorts = [0, 1].map(|i| self.pool.sort(&w[i].body));
            self.check_sort_eq(&sorts[0], &sorts[1])
                .map_err(|e| self.err(e, head_pos))?;
        }

        // Check that patterns are exhaustive
        let is_exhaustive = 'block: {
            let mut covered_constructors: IndexMap<_, _> = datatype
                .constructors
                .iter()
                .map(|(name, _)| (name, false))
                .collect();
            for case in &cases {
                match &case.pattern {
                    MatchPattern::Wildcard | MatchPattern::Variable(_) => break 'block true,
                    MatchPattern::Cons(cons, _) => covered_constructors[cons] = true,
                }
            }
            covered_constructors.values().all(|covered| *covered)
        };
        if !is_exhaustive {
            return Err(self.err(ParserError::NonExhaustivePatterns, head_pos));
        }

        Ok(self.pool.add(Term::Match(matched_term, cases)))
    }

    fn parse_match_case(
        &mut self,
        sort: &Rc<Sort>,
        constructors: &IndexMap<String, DatatypeConstructor>,
    ) -> CarcaraResult<MatchCase> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();

        let pattern = self.parse_match_pattern(sort, constructors)?;
        for (var, sort) in pattern.bindings() {
            self.declare_symbol(var.clone(), sort.clone());
        }

        let body = self.parse_term()?;
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(MatchCase { pattern, body })
    }

    fn parse_match_pattern(
        &mut self,
        sort: &Rc<Sort>,
        constructors: &IndexMap<String, DatatypeConstructor>,
    ) -> CarcaraResult<MatchPattern> {
        let head_pos = self.current_position;
        match self.next_token()? {
            // `_` wildcard
            (Token::ReservedWord(Reserved::Underscore), _) => Ok(MatchPattern::Wildcard),

            // Nullary constructor
            (Token::Symbol(s), _) if constructors.get(&s).is_some() => {
                let n = constructors.get(&s).unwrap().selectors.len();
                if n == 0 {
                    Ok(MatchPattern::Cons(s.clone(), Vec::new()))
                } else {
                    let e = ParserError::WrongNumberOfArgs(n.into(), 0);
                    Err(self.err(e, head_pos))
                }
            }
            // Single variable
            (Token::Symbol(s), _) => Ok(MatchPattern::Variable((s.clone(), sort.clone()))),

            // n-ary constructor
            (Token::OpenParen, _) => {
                let cons_name = self.expect_symbol()?;

                // Note: the SMT-LIB spec says that nullary constructors in patterns must not be
                // parenthesised, such that any pattern that begins with the `(` token must have at
                // least one selector. In practice though, we see proofs where a nullary constructor
                // has extra parentheses around it, so we must handle this here. For our purposes,
                // this means that the following sequence can be empty.
                let args = self.parse_sequence(Self::expect_symbol, false)?;
                match constructors.get(&cons_name) {
                    Some(cons) if cons.selectors.len() == args.len() => {
                        let args: Vec<_> = args
                            .iter()
                            .zip(&cons.selectors)
                            .map(|(var, (_, sort))| (var.clone(), sort.clone()))
                            .collect();

                        Ok(MatchPattern::Cons(cons_name, args))
                    }
                    Some(cons) => Err(self.err(
                        ParserError::WrongNumberOfArgs(cons.selectors.len().into(), args.len()),
                        head_pos,
                    )),
                    None => Err(self.err(ParserError::UnknownConstructor(cons_name), head_pos)),
                }
            }
            (other, pos) => Err(self.err(ParserError::UnexpectedToken(other), pos)),
        }
    }
}
