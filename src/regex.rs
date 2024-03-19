#[derive(Debug)]
pub enum RegexOp {
    Char(char),
    Or((usize, usize)),
    Concat((usize, usize)),
    KleeneClosure(usize)
}

#[derive(Debug)]
pub enum RegexRealizedOp<T> {
    Char(char),
    Or((T, T)),
    Concat((T, T)),
    KleeneClosure(T)
}

#[derive(Debug)]
pub struct RegexAst {
    storage: Vec<RegexOp>,
    head: usize
}

impl<'a> RegexAst {
    pub fn new(pattern: &str) -> Result<RegexAst, String> {
        let chars = pattern.chars().collect::<Vec<char>>();
        Self::parse(&chars[..])
    }

    fn parse(pattern: &[char]) -> Result<RegexAst, String> {
        let mut result = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
        let n = pattern.len();
        let mut idx = 0;
        while idx < n {
            if pattern[idx] == '|' {
                return Ok(result.or(Self::parse(&pattern[(idx + 1)..])?));
            }
            if pattern[idx] == '(' {
                let start = idx + 1;
                let mut subpatterns = 1;
                while subpatterns > 0 {
                    idx += 1;
                    if idx >= n {
                        return Err("Pattern doesn't have a matching ) for (".to_string());
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
                let new = Self::parse(&pattern[start..idx])?;
                if idx < n - 1 && pattern[idx + 1] == '*' {
                    result = result.concat(new.kleene_closure());
                    idx += 2;
                } else {
                    result = result.concat(new);
                    idx += 1;
                }
                continue;
            }
            if pattern[idx] == '[' {
                let start = idx + 1;
                while pattern[idx] != ']' {
                    idx += 1;
                    if idx >= n {
                        return Err("Pattern doesn't have a matching ] for [".to_string());
                    }
                    if pattern[idx] == '\\' {
                        idx += 1;
                        continue;
                    }
                }
                let new = Self::parse_options(&pattern[start..idx])?;
                if idx + 1 < n && pattern[idx + 1] == '*' {
                    result = result.concat(new.kleene_closure());
                    idx += 2;
                } else {
                    result = result.concat(new);
                    idx += 1;
                }
                continue;
            }
            if pattern[idx] == ')' {
                return Err("Pattern doesn't have a matching ( for )".to_string());
            }
            if  pattern[idx] == ']' {
                return Err("Pattern doesn't have a matching [ for ]".to_string());
            }
            if pattern[idx] == '\\' {
                if idx + 1 >= n {
                    return Err("Pattern doesn't have a character to be escaped by \\".to_string());
                }
                result = result.concat(RegexAst { storage: vec![RegexOp::Char(pattern[idx + 1])], head: 0 });
                idx += 2;
                continue;
            }
            let mut new = match pattern[idx] {
                '.' => (0u8..=255u8).map(|val| RegexAst { storage: vec![RegexOp::Char(char::from(val))], head: 0 })
                    .fold(RegexAst { storage: Vec::<RegexOp>::new(), head: 0 }, |acc, x| acc.or(x)),
                ch => RegexAst { storage: vec![RegexOp::Char(ch)], head: 0 }
            };
            if idx + 1 < n && pattern[idx + 1] == '*' {
                new = new.kleene_closure();
                idx += 1;
            } 
            result = result.concat(new);
            idx += 1;
        }
        Ok(result)
    }

    fn parse_options(pattern: &[char]) -> Result<RegexAst, String> {
        let mut result = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
        let n = pattern.len();
        let mut idx = 0;
        while idx < n {
            if pattern[idx] == '\\' {
                if idx + 1 >= n {
                    return Err("Pattern doesn't have a character to be escaped by \\".to_string());
                }
                result = result.or(RegexAst { storage: vec![RegexOp::Char(pattern[idx + 1])], head: 0 });
                idx += 2;
                continue;
            }
            if idx + 2 < n && pattern[idx + 1] == '-' {
                if pattern[idx + 2] != '\\' {
                    if pattern[idx + 2] < pattern[idx + 1] {
                        return Err("".to_string())
                    }
                    result = (pattern[idx]..=pattern[idx + 2])
                        .map(|ch| RegexAst { storage: vec![RegexOp::Char(ch)], head: 0 })
                        .fold(result, |acc, x| acc.or(x));
                    idx += 3;
                    continue;
                } else if idx + 3 < n {
                    if pattern[idx + 3] < pattern[idx + 1] {
                        return Err("".to_string())
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

    pub fn kleene_closure(mut self: Self) -> RegexAst {
        self.storage.push(RegexOp::KleeneClosure(self.head));
        self.head = self.storage.len() - 1;
        self
    }

    pub fn concat(mut self: Self, mut other: RegexAst) -> RegexAst {
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

    pub fn or(mut self: Self, mut other: RegexAst) -> RegexAst {
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

    pub fn root(self: &'a Self) -> RegexAstSubtree<'a> {
        RegexAstSubtree {
            storage: &self.storage,
            head: self.head
        }
    }
}

pub struct RegexAstSubtree<'a> {
    storage: &'a Vec<RegexOp>,
    head: usize
}

impl<'a> RegexAstSubtree<'a> {
    pub fn apply<T, F: Fn(RegexRealizedOp<T>) -> T>(self: &Self, f: &F) -> T {
        match self.storage[self.head] {
            RegexOp::Char(c) => f(RegexRealizedOp::Char(c)),
            RegexOp::KleeneClosure(idx) => {
                let subtree = RegexAstSubtree { storage: self.storage, head: idx };
                let operand = subtree.apply(f);
                f(RegexRealizedOp::KleeneClosure(operand))
            },
            RegexOp::Or((fst, snd)) => {
                let fst_subtree = RegexAstSubtree { storage: self.storage, head: fst };
                let fst_operand = fst_subtree.apply(f);
                let snd_subtree = RegexAstSubtree { storage: self.storage, head: snd };
                let snd_operand = snd_subtree.apply(f);
                f(RegexRealizedOp::Or((fst_operand, snd_operand)))
            }
            RegexOp::Concat((fst, snd)) => {
                let fst_subtree = RegexAstSubtree { storage: self.storage, head: fst };
                let fst_operand = fst_subtree.apply(f);
                let snd_subtree = RegexAstSubtree { storage: self.storage, head: snd };
                let snd_operand = snd_subtree.apply(f);
                f(RegexRealizedOp::Concat((fst_operand, snd_operand)))
            }
        }
    }
}


impl std::fmt::Display for RegexAst {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let to_str = |op| {
            match op {
                RegexRealizedOp::Char(ch) => {
                    match ch {
                        '(' => format!("\\("),
                        ')' => format!("\\)"),
                        '[' => format!("\\["),
                        ']' => format!("\\]"),
                        '\\' => format!("\\\\"),
                        '*' => format!("\\*"),
                        '|' => format!("\\|"),
                        c => format!("{}", c)
                    }
                },
                RegexRealizedOp::KleeneClosure(operand) => {
                    format!("({})*", operand)
                },
                RegexRealizedOp::Or((fst_operand, snd_operand)) => {
                    format!("({})|({})", fst_operand, snd_operand)
                },
                RegexRealizedOp::Concat((fst_operand, snd_operand)) => {
                    format!("{}{}", fst_operand, snd_operand)
                }
            }
        };
        let str = self.root().apply(&to_str);
        write!(f, "{str}")
    }
}
