use std::collections::HashSet;

#[derive(Debug)]
pub enum RegexErrorType {
    UnmatchedOpenningParenthesis,
    UnmatchedClosingParenthesis,
    UnmatchedOpenningSquareBracket,
    UnmatchedClosingSquareBracket,
    NoCharacterToEscape,
    InvalidInterval
}

#[derive(Debug)]
pub struct RegexError {
    pub error_type: RegexErrorType,
    expression: String,
}

impl RegexError {
    pub fn new(error_type: RegexErrorType, expr: &Vec<char>, start: usize, end: usize) -> RegexError {
        let mut expression = String::new();
        for ch in &expr[..start] {
            expression.push(*ch);
        }
        expression.push_str("\x1b[1;31m");
        for ch in &expr[start..=end] {
            expression.push(*ch);
        }
        expression.push_str("\x1b[0m");
        for ch in &expr[(end + 1)..expr.len()] {
            expression.push(*ch);
        }
        RegexError { error_type, expression }
    }
}


impl std::fmt::Display for RegexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.error_type {
            RegexErrorType::UnmatchedOpenningParenthesis => {
                write!(f, "Pattern doesn't have a matching ( for )\n\t{}", self.expression)
            },
            RegexErrorType::UnmatchedClosingParenthesis => {
                write!(f, "Pattern doesn't have a matching ) for (\n\t{}", self.expression)
            },
            RegexErrorType::UnmatchedOpenningSquareBracket => {
                write!(f, "Pattern doesn't have a matching ] for [\n\t{}", self.expression)
            },
            RegexErrorType::UnmatchedClosingSquareBracket => {
                write!(f, "Pattern doesn't have a matching [ for ]\n\t{}", self.expression)
            },
            RegexErrorType::NoCharacterToEscape => {
                write!(f, "Pattern doesn't have a character to be escaped by \\\n\n\t{}", self.expression)
            },
            RegexErrorType::InvalidInterval => {
                write!(f, "Interval must be of the form a-b where a <= b\\\n\t{}", self.expression)
            },
        }
    }
}

#[derive(Debug)]
pub enum RegexOp<T> {
    Char(char),
    Or((T, T)),
    Concat((T, T)),
    KleeneClosure(T)
}


pub trait IRegexAstView<'a> {
    fn apply<T, F: Fn(RegexOp<T>) -> T>(self: Self, f: &F) -> T;
}

pub trait IRegexAst {
    fn concat(self: Self, other: Self) -> Self;
    fn or(self: Self, other: Self) -> Self;
    fn kleene_closure(self: Self) -> Self;
    fn root(self: &Self) -> impl IRegexAstView;
}

pub struct RegexAst {
    storage: Vec<RegexOp<usize>>,
    head: usize
}

impl IRegexAst for RegexAst {
    fn concat(mut self: Self, mut other: RegexAst) -> RegexAst {
        if self.storage.is_empty() {
            return other
        }
        if other.storage.is_empty() {
            return self
        }
        let n = self.storage.len();
        if n > 0 {
            other.storage = other.storage.into_iter().map(|x| match x {
                RegexOp::Or((fst, snd)) => RegexOp::Or((fst + n, snd + n)),
                RegexOp::Concat((fst, snd)) => RegexOp::Concat((fst + n, snd + n)),
                RegexOp::KleeneClosure(fst) => RegexOp::KleeneClosure(fst + n),
                RegexOp::Char(c) => RegexOp::Char(c)
            }).collect();
            self.storage.append(&mut other.storage);
            other.head += n;
            self.storage.push(RegexOp::Concat((self.head, other.head)));
            self.head = self.storage.len() - 1;
        } else {
            self = other;
        }
        self
    }

    fn or(mut self: Self, mut other: RegexAst) -> RegexAst {
        if self.storage.is_empty() {
            return other
        }
        if other.storage.is_empty() {
            return self
        }
        let n = self.storage.len();
        other.storage = other.storage.into_iter().map(|x| match x {
            RegexOp::Or((fst, snd)) => RegexOp::Or((fst + n, snd + n)),
            RegexOp::Concat((fst, snd)) => RegexOp::Concat((fst + n, snd + n)),
            RegexOp::KleeneClosure(fst) => RegexOp::KleeneClosure(fst + n),
            RegexOp::Char(c) => RegexOp::Char(c)
        }).collect();
        self.storage.append(&mut other.storage);
        other.head += n;
        self.storage.push(RegexOp::Or((self.head, other.head)));
        self.head = self.storage.len() - 1;
        self
    }

    fn kleene_closure(mut self: Self) -> RegexAst {
        self.storage.push(RegexOp::KleeneClosure(self.head));
        self.head = self.storage.len() - 1;
        self
    }


    fn root(self: &Self) -> RegexAstSubtree {
        RegexAstSubtree {
            storage: &self.storage,
            head: self.head
        }
    }
}

impl RegexAst {
    pub fn new(pattern: &str) -> Result<RegexAst, RegexError> {
        let chars = pattern.chars().collect::<Vec<char>>();
        Self::parse(&chars, 0, chars.len() - 1)
    }

    fn parse(pattern: &Vec<char>, start: usize, end: usize) -> Result<RegexAst, RegexError> {
        let mut result = RegexAst { storage: Vec::<RegexOp<usize>>::new(), head: 0 };
        let mut idx = start;
        while idx <= end {
            if pattern[idx] == '|' {
                return Ok(result.or(Self::parse(pattern, idx + 1, end)?));
            }
            if pattern[idx] == '(' {
                let start_subpattern = idx + 1;
                let mut subpatterns = 1;
                while subpatterns > 0 {
                    idx += 1;
                    if idx > end {
                        return Err(
                            RegexError::new(
                                RegexErrorType::UnmatchedOpenningParenthesis,
                                pattern,
                                start_subpattern - 1,
                                start_subpattern - 1
                            )
                        );
                    }
                    if pattern[idx] == '\\' {
                        idx += 1;
                        continue;
                    }
                    if pattern[idx] == '(' {
                        subpatterns += 1;
                        continue;
                    }
                    if pattern[idx] == ')' {
                        subpatterns -= 1;
                    }
                }
                let new = Self::parse(pattern, start_subpattern, idx - 1)?;
                if idx <= end - 1 && pattern[idx + 1] == '*' {
                    result = result.concat(new.kleene_closure());
                    idx += 2;
                } else {
                    result = result.concat(new);
                    idx += 1;
                }
                continue;
            }
            if pattern[idx] == '[' {
                let start_options = idx + 1;
                while pattern[idx] != ']' {
                    idx += 1;
                    if idx > end {
                        return Err(
                            RegexError::new(
                                RegexErrorType::UnmatchedOpenningSquareBracket,
                                pattern,
                                start_options - 1,
                                start_options - 1
                            )
                        );
                    }
                    if pattern[idx] == '\\' {
                        idx += 1;
                        continue;
                    }
                }
                let new = Self::parse_options(pattern, start_options, idx - 1)?;
                if idx + 1 <= end && pattern[idx + 1] == '*' {
                    result = result.concat(new.kleene_closure());
                    idx += 2;
                } else {
                    result = result.concat(new);
                    idx += 1;
                }
                continue;
            }
            if pattern[idx] == ')' {
                return Err(
                    RegexError::new(
                        RegexErrorType::UnmatchedClosingParenthesis,
                        pattern,
                        idx,
                        idx
                    )
                );
            }
            if  pattern[idx] == ']' {
                return Err(
                    RegexError::new(
                        RegexErrorType::UnmatchedClosingSquareBracket,
                        pattern,
                        idx,
                        idx
                    )
                );
            }
            if pattern[idx] == '\\' {
                if idx + 1 > end {
                    return Err(
                        RegexError::new(
                            RegexErrorType::NoCharacterToEscape,
                            pattern,
                            end,
                            end
                        )
                    );
                }
                result = result.concat(RegexAst { storage: vec![RegexOp::Char(pattern[idx + 1])], head: 0 });
                idx += 2;
                continue;
            }
            let mut new = match pattern[idx] {
                '.' => (0u8..=255u8).map(|val| RegexAst { storage: vec![RegexOp::Char(char::from(val))], head: 0 })
                    .fold(RegexAst { storage: Vec::<RegexOp<usize>>::new(), head: 0 }, |acc, x| acc.or(x)),
                ch => RegexAst { storage: vec![RegexOp::Char(ch)], head: 0 }
            };
            if idx + 1 <= end && pattern[idx + 1] == '*' {
                new = new.kleene_closure();
                idx += 1;
            } 
            result = result.concat(new);
            idx += 1;
        }
        Ok(result)
    }

    fn parse_options(pattern: &Vec<char>, start: usize, end: usize) -> Result<RegexAst, RegexError> {
        let mut result = RegexAst { storage: Vec::<RegexOp<usize>>::new(), head: 0 };
        let mut idx = start;
        while idx <= end {
            if pattern[idx] == '\\' {
                result = result.or(RegexAst { storage: vec![RegexOp::Char(pattern[idx + 1])], head: 0 });
                idx += 2;
                continue;
            }
            if idx + 2 <= end && pattern[idx + 1] == '-' {
                if pattern[idx + 2] != '\\' {
                    if pattern[idx + 2] < pattern[idx + 1] {
                        return Err(
                            RegexError::new(
                                RegexErrorType::InvalidInterval,
                                pattern,
                                idx,
                                idx + 2
                            )
                        );
                    }
                    result = (pattern[idx]..=pattern[idx + 2])
                        .map(|ch| RegexAst { storage: vec![RegexOp::Char(ch)], head: 0 })
                        .fold(result, |acc, x| acc.or(x));
                    idx += 3;
                    continue;
                } else if idx + 3 <= end {
                    if pattern[idx + 3] < pattern[idx + 1] {
                        return Err(
                            RegexError::new(
                                RegexErrorType::InvalidInterval,
                                pattern,
                                idx,
                                idx + 3
                            )
                        );
                    }
                    result = (pattern[idx]..=pattern[idx + 3])
                        .map(|ch| RegexAst { storage: vec![RegexOp::Char(ch)], head: 0 })
                        .fold(result, |acc, x| acc.or(x));
                    idx += 4;
                    continue;
                }
            }
            let new = RegexAst { storage: vec![RegexOp::Char(pattern[idx])], head: 0 };
            result = result.or(new);
            idx += 1;
        }
        Ok(result)
    }
}

pub struct RegexAstSubtree<'a> {
    storage: &'a Vec<RegexOp<usize>>,
    head: usize
}

impl<'a> IRegexAstView<'a> for RegexAstSubtree<'a> {
    // Post order
    fn apply<T, F: Fn(RegexOp<T>) -> T>(self: Self, f: &F) -> T {
        match self.storage[self.head] {
            RegexOp::Char(c) => f(RegexOp::Char(c)),
            RegexOp::KleeneClosure(idx) => {
                let subtree = RegexAstSubtree { storage: self.storage, head: idx };
                let operand = subtree.apply(f);
                f(RegexOp::KleeneClosure(operand))
            },
            RegexOp::Or((fst, snd)) => {
                let fst_subtree = RegexAstSubtree { storage: self.storage, head: fst };
                let fst_operand = fst_subtree.apply(f);
                let snd_subtree = RegexAstSubtree { storage: self.storage, head: snd };
                let snd_operand = snd_subtree.apply(f);
                f(RegexOp::Or((fst_operand, snd_operand)))
            }
            RegexOp::Concat((fst, snd)) => {
                let fst_subtree = RegexAstSubtree { storage: self.storage, head: fst };
                let fst_operand = fst_subtree.apply(f);
                let snd_subtree = RegexAstSubtree { storage: self.storage, head: snd };
                let snd_operand = snd_subtree.apply(f);
                f(RegexOp::Concat((fst_operand, snd_operand)))
            }
        }
    }
}


impl std::fmt::Display for RegexAst {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let to_str = |op| {
            match op {
                RegexOp::<Vec<(usize, HashSet<usize>, bool, bool, String)>>::Char(ch) => {
                    vec![(0, HashSet::new(), false, true, format!("Char('{}')", ch))]
                },
                RegexOp::<Vec<(usize, HashSet<usize>, bool, bool, String)>>::KleeneClosure(mut operand) => {
                    let end = operand.len() - 1;
                    operand[end].3 = false;
                    operand.push((operand[end].0 + 1, operand[end].1.clone(), true, true, format!("KleeneClosure")));
                    operand
                },
                RegexOp::<Vec<(usize, HashSet<usize>, bool, bool, String)>>::Or((mut fst_operand, mut snd_operand)) => {
                    let n1 = fst_operand.len();
                    let n2 = snd_operand.len();
                    if snd_operand[n2 - 1].0 < fst_operand[n1 - 1].0 {
                        let diff = fst_operand[n1 - 1].0 - snd_operand[n2 - 1].0;
                        for (t, vert, _, _, _) in snd_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    } else {
                        let diff = snd_operand[n2 - 1].0 - fst_operand[n1 - 1].0;
                        for (t, vert, _, _, _) in fst_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    }
                    fst_operand[n1 - 1].3 = false;
                    let max = fst_operand[n1 - 1].0;
                    for (_, vert, _, _, _) in snd_operand.iter_mut() {
                        vert.insert(max);
                    }
                    fst_operand.append(&mut snd_operand);
                    let end = fst_operand.len() - 1;
                    fst_operand.push((fst_operand[end].0 +  1, HashSet::new(), true, true, format!("Or")));
                    fst_operand
                },
                RegexOp::<Vec<(usize, HashSet<usize>, bool, bool, String)>>::Concat((mut fst_operand, mut snd_operand)) => {
                    let n1 = fst_operand.len();
                    let n2 = snd_operand.len();
                    if snd_operand[n2 - 1].0 < fst_operand[n1 - 1].0 {
                        let diff = fst_operand[n1 - 1].0 - snd_operand[n2 - 1].0;
                        for (t, vert, _, _, _) in snd_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    } else {
                        let diff = snd_operand[n2 - 1].0 - fst_operand[n1 - 1].0;
                        for (t, vert, _, _, _) in fst_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    }
                    fst_operand[n1 - 1].3 = false;
                    let max = fst_operand[n1 - 1].0;
                    for (_, vert, _, _, _) in snd_operand.iter_mut() {
                        vert.insert(max);
                    }
                    fst_operand.append(&mut snd_operand);
                    let end = fst_operand.len() - 1;
                    fst_operand.push((fst_operand[end].0 + 1, HashSet::new(), true, true, format!("Concat")));
                    fst_operand
                }
            }
        };
        let vals = self.root().apply(&to_str).into_iter().rev().collect::<Vec<(usize, HashSet<usize>, bool, bool, String)>>();
        let max_val = vals.iter().map(|(i, _, _, _, _)| *i).fold(0, std::cmp::max);
        let str = vals.into_iter().map(|(i, verts, has_operands, middle, s)| {
            let mut spacing = String::new();
            for idx in 0..(max_val - i) {
                if verts.contains(&(max_val - idx)) {
                    spacing.push_str("\u{2503}   ");
                    continue;
                }
                spacing.push_str("    ");
            }
            std::iter::repeat("  ".to_string()).take(max_val - i).collect::<Vec<String>>().join("");
            match (has_operands, middle) {
                (true, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, s),
                (true, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, s),
                (false, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, s),
                (false, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, s)
            }
        }).collect::<Vec<String>>().join("\r\n");
        write!(f, "{}", str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl From<RegexError> for String {
        fn from(err: RegexError) -> String {
            format!("{}", err)
        }
    }

    pub fn build_matcher(op: RegexOp<std::boxed::Box<dyn Fn(&str) -> (bool, &str)>>) -> std::boxed::Box<dyn Fn(&str) -> (bool, &str)> {
        match op {
            RegexOp::Char(c) => std::boxed::Box::new(move |s: &str| {
                match s.chars().last().is_some_and(|ch| ch == c) {
                    true => (true, &s[..(s.len() - 1)]),
                    false => (false, s)
                }
            }),
            RegexOp::KleeneClosure(match_operand) => {
                std::boxed::Box::new(move |s: &str| {
                    let (mut matched, mut current) = match_operand(s);
                    while matched {
                        (matched, current) = match_operand(current);
                    }
                    (true, current)
                })
            },
            RegexOp::Or((fst, snd)) => {
                std::boxed::Box::new(move |s: &str| {
                    let (matched, state) = snd(s);
                    match matched {
                        true => (matched, state),
                        false => fst(state)
                    }
                })
            },
            RegexOp::Concat((fst, snd)) => {
                std::boxed::Box::new(move |s: &str| {
                    let (matched, state) = snd(s);
                    match matched {
                        true => fst(state),
                        false => (false, s)
                    }
                })
            },
        }
    }

    #[test]
    fn properly_matches_strings() -> Result<(), RegexError>{
        let regex_match = RegexAst::new("((hello)|(ab(cd)*))cd.cdef[a-d]")?.root().apply(&build_matcher);
        let should_pass = [
            "hellocd'cdefa",
            "hellocd\"cdefb",
            "hellocd/cdefc",
            "hellocd|cdefd",
            "abcd=cdefa",
            "abcd-cdefb",
            "abcd+cdefc",
            "abcd]cdefd",
            "abcdcd[cdefa",
            "abcdcd(cdefb",
            "abcdcd)cdefc",
            "abcdcd!cdefd",
            "abcdcdcd@cdefa",
            "abcdcdcd#cdefb",
            "abcdcdcd$cdefc",
            "abcdcdcd%cdefd",
            "abcdcdcdcd&cdefa",
            "abcdcdcdcd cdefb",
            "abcdcdcdcd2cdefc",
            "abcdcdcdcd8cdefd",
            "abcdcdcdkcdefa",
            "abcdcdcdhcdefb",
            "abcdcdcdmcdefc",
            "abcdcdcdhcdefd",
            "abcdcdcdcd8cdefa",
            "abcdcdcdcd\ncdefb",
            "abcdcdcdcd\ncdefc",
            "abcdcdcdcd\ncdefd",
        ];
        let shouldnt_pass = [
            "helfhdkasllocdcdef",
            "abcdcdfhdkfdsklhkl\\asef",
            "ab cdcd cd .odfahifan ef",
            "af",
            "",
        ];
        for case in should_pass {
            let (matched, _) = regex_match(case);
            if !matched {
                println!("{}", case);
            }
            assert!(matched);
        }
        for case in shouldnt_pass {
            let (matched, _) = regex_match(case);
            if matched {
                println!("{}", case);
            }
            assert!(!matched);
        }
        Ok(())
    }

    #[test]
    fn returns_error_for_non_closed_parenthesis() {
        let result = RegexAst::new("((hello)|(ab(cd)*)cdcdef[a-d]");
        assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedOpenningParenthesis)));
    }

    #[test]
    fn returns_error_for_non_closed_square_bracket() {
        let result = RegexAst::new("((hello)|(ab(cd)*))cdcdef[a-d");
        assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedOpenningSquareBracket)));
    }

    #[test]
    fn returns_error_for_non_opened_parenthesis() {
        let result = RegexAst::new("((hello))|(ab(cd)*))cdcdef[a-d]");
        assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedClosingParenthesis)));
    }

    #[test]
    fn returns_error_for_non_opened_square_bracket() {
        let result = RegexAst::new("((hello)|(ab(cd)*))cdcdef[a-d]]");
        assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedClosingSquareBracket)));
    }
}
