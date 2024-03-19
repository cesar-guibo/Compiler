
#[derive(Debug)]
pub enum RegexToken {
    OpenSubpattern,
    CloseSubpattern,
    OpenOptions,
    CloseOptions,
    Escape,
    KleeneClosureOperator,
    OrOperator,
    Char(char),
}

#[derive(Debug)]
pub enum RegexRule {
    Expressions,
    Or,
    SingleExpression,
    ExpressionItem,
    Options,
    OptionsItem,
    SubpatternExpressions,
    SubpatternOr,
    SubpatternSingleExpression,
    SubpatternExpressionItem,
    Escape
}

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
        let tokens = pattern.chars().map(|ch| match ch {
            '(' => RegexToken::OpenSubpattern,
            ')' => RegexToken::CloseSubpattern,
            '[' => RegexToken::OpenOptions,
            ']' => RegexToken::CloseOptions,
            '\\' => RegexToken::Escape,
            '*' => RegexToken::KleeneClosureOperator,
            '|' => RegexToken::OrOperator,
            ch => RegexToken::Char(ch),
        }).rev().collect::<Vec<RegexToken>>();
        let (result, tks) = Self::parse(RegexRule::Expressions, tokens)?;
        if !tks.is_empty() {
            return Err("(0)".to_string())
        }
        Ok(result)
    }

    fn parse(rule: RegexRule, mut tokens: Vec<RegexToken>) -> Result<(RegexAst, Vec<RegexToken>), String> {
        if let Some(token) = tokens.pop() {
            return match (rule, &token) {
                (
                    RegexRule::Expressions,
                    RegexToken::OpenSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::Escape
                        | RegexToken::OrOperator
                        | RegexToken::Char(_)
                ) => {
                    tokens.push(token);
                    let (mut ast, mut tks) = Self::parse(RegexRule::SingleExpression, tokens)?;
                    let acc = ast;
                    (ast, tks) = Self::parse(RegexRule::Or, tks)?;
                    Ok((acc.or(ast), tks))
                },
                (RegexRule::Expressions, RegexToken::CloseSubpattern) => {
                    Err("Pattern doesn't have a matching ( for ) (1)".to_string())
                },
                (RegexRule::Expressions, RegexToken::CloseOptions) => {
                    Err("Pattern doesn't have a matching [ for ]".to_string())
                },
                (RegexRule::Expressions, RegexToken::KleeneClosureOperator) => {
                    Err("Pattern can't start with *".to_string())
                },


                (
                    RegexRule::Or,
                    RegexToken::OrOperator
                 ) => {
                    Self::parse(RegexRule::Expressions, tokens)
                },
                (
                    RegexRule::Or,
                    RegexToken::OpenSubpattern
                        | RegexToken::CloseSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::CloseOptions
                        | RegexToken::Escape
                        | RegexToken::KleeneClosureOperator
                        | RegexToken::Char(_)
                ) => {
                    panic!("The state ({:?}, {:?}) shouldn't be reachable", RegexRule::Or, &token);
                },


                (
                    RegexRule::SingleExpression,
                    RegexToken::Char(_)
                        | RegexToken::OpenSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::Escape
                ) => {
                    tokens.push(token);
                    let (mut ast, mut tks) = Self::parse(RegexRule::ExpressionItem, tokens)?;
                    let mut acc = ast;
                    if tks.pop().is_some_and(|tkn| matches!(tkn, RegexToken::KleeneClosureOperator)) {
                        acc.storage.push(RegexOp::KleeneClosure(acc.head));
                        acc.head = acc.storage.len() - 1;
                    }
                    (ast, tks) = Self::parse(RegexRule::SingleExpression, tks)?;
                    Ok((acc.concat(ast), tks))
                },
                (RegexRule::SingleExpression, RegexToken::OrOperator) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::SingleExpression, RegexToken::CloseSubpattern) => {
                    Err("Pattern doesn't have a matching ( for ) (2)".to_string())
                },
                (RegexRule::SingleExpression, RegexToken::CloseOptions) => {
                    Err("Pattern doesn't have a matching [ for ]".to_string())
                },
                (RegexRule::SingleExpression, RegexToken::KleeneClosureOperator) => {
                    Err("Pattern can't start with *".to_string())
                },


                (RegexRule::ExpressionItem, RegexToken::Char(ch)) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(*ch)], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::ExpressionItem, RegexToken::OpenSubpattern) => {
                    let (ast, mut tks) = Self::parse(RegexRule::SubpatternExpressions, tokens)?;
                    if tks.pop().is_some_and(|token| matches!(token, RegexToken::CloseSubpattern)) {
                        Ok((ast, tks))
                    } else {
                        panic!("Unreachable state");
                    }
                },
                (RegexRule::ExpressionItem, RegexToken::OpenOptions) => {
                    let (ast, mut tks) = Self::parse(RegexRule::Options, tokens)?;
                    if tks.pop().is_some_and(|token| matches!(token, RegexToken::CloseOptions)) {
                        Ok((ast, tks))
                    } else {
                        panic!("Unreachable state");
                    }
                },
                (RegexRule::ExpressionItem, RegexToken::Escape) => {
                    Self::parse(RegexRule::Escape, tokens)
                },
                (
                    RegexRule::ExpressionItem,
                    RegexToken::CloseSubpattern
                        | RegexToken::CloseOptions
                        | RegexToken::KleeneClosureOperator
                        | RegexToken::OrOperator
                ) => {
                    Err("(1)".to_string())
                },


                (
                    RegexRule::Options,
                    RegexToken::OpenSubpattern
                        | RegexToken::CloseSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::KleeneClosureOperator
                        | RegexToken::OrOperator
                        | RegexToken::Char(_)
                        | RegexToken::Escape
                ) => {
                    tokens.push(token);
                    let (mut ast, mut tks) = Self::parse(RegexRule::OptionsItem, tokens)?;
                    let acc = ast;
                    (ast, tks) = Self::parse(RegexRule::Options, tks)?;
                    Ok((acc.or(ast), tks))
                },
                (RegexRule::Options, RegexToken::CloseOptions) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },


                (RegexRule::OptionsItem, RegexToken::OpenSubpattern) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('(')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::CloseSubpattern) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(')')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::OpenOptions) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('[')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::Escape) => {
                    Self::parse(RegexRule::Escape, tokens)
                },
                (RegexRule::OptionsItem, RegexToken::KleeneClosureOperator) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('*')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::OrOperator) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('|')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::Char(ch)) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(*ch)], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::OptionsItem, RegexToken::CloseOptions) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },



                (
                    RegexRule::SubpatternExpressions,
                    RegexToken::OpenSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::Escape
                        | RegexToken::OrOperator
                        | RegexToken::Char(_)
                ) => {
                    tokens.push(token);
                    let (mut ast, mut tks) = Self::parse(RegexRule::SubpatternSingleExpression, tokens)?;
                    let acc = ast;
                    (ast, tks) = Self::parse(RegexRule::SubpatternOr, tks)?;
                    Ok((acc.or(ast), tks))
                },
                (RegexRule::SubpatternExpressions, RegexToken::CloseSubpattern) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::SubpatternExpressions, RegexToken::CloseOptions) => {
                    Err("Pattern has no matching ] for [".to_string())
                }
                (RegexRule::SubpatternExpressions, RegexToken::KleeneClosureOperator) => {
                    Err("There is no character to apply *".to_string())
                },


                (
                    RegexRule::SubpatternOr,
                    RegexToken::OrOperator
                 ) => {
                    Self::parse(RegexRule::SubpatternExpressions, tokens)
                },
                (
                    RegexRule::SubpatternOr,
                    RegexToken::OpenSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::CloseOptions
                        | RegexToken::Escape
                        | RegexToken::KleeneClosureOperator
                        | RegexToken::Char(_)
                ) => {
                    panic!("The state ({:?}, {:?}) shouldn't be reachable", RegexRule::SubpatternOr, &token);
                },
                (RegexRule::SubpatternOr, RegexToken::CloseSubpattern) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },


                (
                    RegexRule::SubpatternSingleExpression,
                    RegexToken::Char(_)
                        | RegexToken::OpenSubpattern
                        | RegexToken::OpenOptions
                        | RegexToken::Escape
                ) => {
                    tokens.push(token);
                    let (mut ast, mut tks) = Self::parse(RegexRule::SubpatternExpressionItem, tokens)?;
                    let mut acc = ast;
                    if tks.pop().is_some_and(|tkn| matches!(tkn, RegexToken::KleeneClosureOperator)) {
                        acc.storage.push(RegexOp::KleeneClosure(acc.head));
                        acc.head = acc.storage.len() - 1;
                    }
                    (ast, tks) = Self::parse(RegexRule::SubpatternSingleExpression, tks)?;
                    Ok((acc.concat(ast), tks))
                },
                (
                    RegexRule::SubpatternSingleExpression,
                    RegexToken::CloseSubpattern
                        | RegexToken::OrOperator
                ) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::SubpatternSingleExpression, RegexToken::CloseOptions) => {
                    Err("Pattern has no matching ] for [".to_string())
                }
                (RegexRule::SubpatternSingleExpression, RegexToken::KleeneClosureOperator) => {
                    Err("There is no character to apply *".to_string())
                },


                (RegexRule::SubpatternExpressionItem, RegexToken::Char(ch)) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(*ch)], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::SubpatternExpressionItem, RegexToken::OpenSubpattern) => {
                    let (ast, mut tks) = Self::parse(RegexRule::SubpatternExpressions, tokens)?;
                    if tks.pop().is_some_and(|token| matches!(token, RegexToken::CloseSubpattern)) {
                        Ok((ast, tks))
                    } else {
                        panic!("Unreachable state");
                    }
                },
                (RegexRule::SubpatternExpressionItem, RegexToken::OpenOptions) => {
                    let (ast, mut tks) = Self::parse(RegexRule::Options, tokens)?;
                    if tks.pop().is_some_and(|token| matches!(token, RegexToken::CloseOptions)) {
                        Ok((ast, tks))
                    } else {
                        panic!("Unreachable state");
                    }
                },
                (RegexRule::SubpatternExpressionItem, RegexToken::Escape) => {
                    Self::parse(RegexRule::Escape, tokens)
                },
                (
                    RegexRule::SubpatternExpressionItem,
                    RegexToken::KleeneClosureOperator
                        | RegexToken::OrOperator
                        | RegexToken::CloseSubpattern
                ) => {
                    tokens.push(token);
                    let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::SubpatternExpressionItem, RegexToken::CloseOptions) => {
                    Err("Pattern has no matching ] for [".to_string())
                }
               

                (RegexRule::Escape, RegexToken::OpenSubpattern) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('(')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::CloseSubpattern) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(')')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::OpenOptions) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('[')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::CloseOptions) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(']')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::Escape) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('\\')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::KleeneClosureOperator) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('*')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::OrOperator) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char('|')], head: 0 };
                    Ok((ast, tokens))
                },
                (RegexRule::Escape, RegexToken::Char(ch)) => {
                    let ast = RegexAst { storage: vec![RegexOp::Char(*ch)], head: 0 };
                    Ok((ast, tokens))
                },
            }
        }
        match rule {
            RegexRule::Expressions => {
                let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                Ok((ast, tokens))
            },
            RegexRule::Or => {
                let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                Ok((ast, tokens))
            },
            RegexRule::SingleExpression => {
                let ast = RegexAst { storage: Vec::<RegexOp>::new(), head: 0 };
                Ok((ast, tokens))
            },
            RegexRule::Escape => {
                Err("Pattern missing the character that should be escaped after \\".to_string())
            },
            RegexRule::SubpatternOr
                | RegexRule::SubpatternSingleExpression 
                | RegexRule::SubpatternExpressionItem
                | RegexRule::SubpatternExpressions => {
                Err("Pattern doesn't have a matching ) for (".to_string())
            },
            RegexRule::OptionsItem | RegexRule::Options => {
                Err("Pattern missing matching ] for [".to_string())
            },
            RegexRule::ExpressionItem => {
                panic!("Unreachable state");
            }
        }
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
