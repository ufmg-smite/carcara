use nom::{
    bytes::complete::tag,
    character::complete::{alpha1, char, digit1, multispace0, multispace1},
    combinator::{map, map_res, recognize, verify},
    multi::{many0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated},
    IResult, Parser,
};
use std::str::FromStr;

use super::Automaton;

fn identifier(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        alpha1,
        nom::bytes::complete::take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
    ))
    .parse(input)
}

fn number(input: &str) -> IResult<&str, u32> {
    map_res(digit1, FromStr::from_str).parse(input)
}

fn initial_state(input: &str) -> IResult<&str, &str> {
    preceded(
        terminated(tag("init"), multispace1),
        terminated(recognize(identifier), char(';')),
    )
    .parse(input)
}

fn accepting_states(input: &str) -> IResult<&str, Vec<&str>> {
    preceded(
        terminated(tag("accepting"), multispace1),
        terminated(
            separated_list1(
                preceded(multispace0, char(',')),
                preceded(multispace0, identifier),
            ),
            char(';'),
        ),
    )
    .parse(input)
}

fn char_range(input: &str) -> IResult<&str, (u32, u32)> {
    delimited(
        char('['),
        verify(
            separated_pair(
                preceded(multispace0, number),
                preceded(multispace0, char(',')),
                preceded(multispace0, number),
            ),
            |(start, end)| start <= end,
        ),
        char(']'),
    )
    .parse(input)
}

fn transition(input: &str) -> IResult<&str, (&str, &str, (u32, u32))> {
    map(
        (
            terminated(identifier, preceded(multispace0, tag("->"))),
            preceded(multispace0, identifier),
            preceded(multispace0, terminated(char_range, char(';'))),
        ),
        |(from, to, range)| (from, to, range),
    )
    .parse(input)
}

/// Parses a textual definition into an `Automaton` using `nom` combinators.
pub fn parse_automaton(input: &str) -> IResult<&str, Automaton> {
    map(
        terminated(
            (
                preceded(
                    terminated(tag("automaton"), multispace1),
                    terminated(identifier, multispace0),
                ),
                delimited(
                    char('{'),
                    (
                        preceded(multispace0, initial_state),
                        many0(preceded(multispace0, transition)),
                        preceded(multispace0, accepting_states),
                    ),
                    preceded(multispace0, char('}')),
                ),
            ),
            char(';'),
        ),
        |(name, (initial_state, transitions, accepting_states))| {
            Automaton::new(name, initial_state, transitions, accepting_states)
        },
    )
    .parse(input)
}

#[cfg(test)]
mod tests {
    use crate::automata::Trigger;

    use super::*;

    #[test]
    fn test_parses_simple_automaton() {
        let input = r#"automaton value_0 { init s0; s0 -> s1 [97, 97]; s1 -> s1 [97, 97]; accepting s1; };"#;
        let result = parse_automaton(input);

        assert!(result.is_ok());

        let (rest, automaton) = result.unwrap();
        assert!(rest.trim().is_empty());

        assert_eq!(automaton.name, "value_0");
        assert_eq!(automaton.all_states.len(), 2);
        assert_eq!(automaton.initial_state, 0);
        assert!(automaton.is_nfa());
    }

    #[test]
    fn test_parses_state_ids_and_accepting() {
        let input = r#"automaton a { init s0; s0 -> s1 [97, 97]; accepting s1; };"#;
        let (_, automaton) = parse_automaton(input).unwrap();

        let s0 = &automaton.all_states[0];
        let s1 = &automaton.all_states[1];

        assert_eq!(s0.id, "s0");
        assert!(!s0.accept);

        assert_eq!(s1.id, "s1");
        assert!(s1.accept);
    }

    #[test]
    fn test_parses_range_transition() {
        let input = r#"automaton a { init s0; s0 -> s1 [97, 122]; accepting s1; };"#;
        let (_, automaton) = parse_automaton(input).unwrap();
        let s0 = &automaton.all_states[0];

        assert_eq!(s0.transitions.len(), 1);

        let transition = s0.transitions.iter().next().unwrap();
        assert_eq!(transition.to, 1);

        match transition.trigger {
            Trigger::Range((l, r)) => {
                assert_eq!(l, 97);
                assert_eq!(r, 122);
            }
            Trigger::Epsilon => panic!("expected Trigger::Range"),
        }
    }

    #[test]
    fn test_parses_multiple_transitions() {
        let input =
            r#"automaton a { init s0; s0 -> s1 [97, 97]; s0 -> s2 [98, 98]; accepting s2; };"#;

        let (_, automaton) = parse_automaton(input).unwrap();
        let s0 = &automaton.all_states[0];

        assert_eq!(s0.transitions.len(), 2);
    }

    #[test]
    fn test_fails_on_invalid_syntax() {
        let input = r#"
            automaton a {
                init s0
                s0 -> s1 [97, 97];
                accepting s1;
            };
        "#;

        assert!(parse_automaton(input).is_err());
    }

    #[test]
    fn test_fails_without_initial_state() {
        let input = r#"automaton a { s0 -> s1 [97, 97]; accepting s1; };"#;
        assert!(parse_automaton(input).is_err());
    }

    #[test]
    fn test_fails_on_invalid_range() {
        let input = r#"automaton a { init s0; s0 -> s1 [100, 97]; accepting s1; };"#;
        assert!(parse_automaton(input).is_err());
    }

    #[test]
    fn test_fails_on_trailing_garbage() {
        let input = r#"automaton a { init s0; accepting s0; }; garbage"#;
        let result = parse_automaton(input);
        assert!(result.is_err() || !result.unwrap().0.trim().is_empty());
    }
}
