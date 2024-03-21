use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

mod regex;

use regex::{IRegexAst, IRegexAstView,RegexOp};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    Word(String),
    Number(u32),
}

pub trait TokenBuilder<T> : std::fmt::Debug {
    fn to_token(self: &Self, str: String) -> T;
}

pub struct WordBuilder;
impl TokenBuilder<Token> for WordBuilder {
    fn to_token(self: &Self, str: String) -> Token {
        Token::Word(str)
    }
}
impl std::fmt::Debug for WordBuilder {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "WordBuilder")
    }
}

pub struct NumberBuilder;

impl TokenBuilder<Token> for NumberBuilder {
    fn to_token(self: &Self, str: String) -> Token {
        Token::Number(u32::from_str_radix(&str, 10).unwrap())
    }
}

impl std::fmt::Debug for NumberBuilder {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "NumberBuilder")
    }
}

#[derive(Clone, Debug)]
struct Node<T> {
    nexts: HashMap<char, usize>,
    symbol: Option<Rc<dyn TokenBuilder<T>>>
}


#[derive(Clone, Debug)]
pub struct Lexer<T> {
    storage: Vec<Node<T>>,
    fst: usize
}

pub struct TokenIter<'a, T> {
    next_ch: Option<char>,
    chars: std::vec::IntoIter<char>,
    lexer: &'a Lexer<T>,
}

impl<'a, T> std::iter::Iterator for TokenIter<'a, T> {
    type Item = Result<T, String>;

    fn next(self: &mut Self) -> Option<Self::Item> {
        if self.next_ch.is_none() {
            return None;
        }
        let mut current = &self.lexer.storage[self.lexer.fst];
        let mut state = Vec::<char>::new();
        while self.next_ch.is_some_and(|ch| ch == ' ') {
            self.next_ch = self.chars.next();
        }
        while let Some(ch) = self.next_ch {
            if let Some(next_node) = current.nexts.get(&ch) {
                state.push(ch);
                self.next_ch = self.chars.next();
                current = &self.lexer.storage[*next_node];
            } else {
                break;
            }
        }
        let s = state.into_iter().collect::<String>();
        return match current.symbol.as_ref() {
            Some(builder) => Some(Ok(builder.to_token(s))),
            None => Some(Err(format!("Failed to tokenize string \"{}\"", s)))
        };
    }
}

impl<T> Lexer<T> {
    pub fn tokenize(self: &Self, s: String) -> TokenIter<T> {
        let mut chars = s.chars().collect::<Vec<char>>().into_iter();
        TokenIter {
            next_ch: chars.next(),
            chars,
            lexer: self,
        }
    }
}


#[derive(Clone, Debug)]
struct LazyNode<T> {
    nexts: HashMap<char, usize>,
    epsilons: Vec<usize>,
    symbol: Option<Rc<dyn TokenBuilder<T>>>
}


#[derive(Clone, Debug)]
pub struct LazyLexer<T> {
    storage: Vec<LazyNode<T>>,
    fst: usize,
    last: usize
}

impl<T> LazyLexer<T> {
    pub fn new<U: IRegexAst>(pattern: U, symbol: Rc<dyn TokenBuilder<T>>) -> Self {
        let mut result = pattern.root().apply(&|op: RegexOp<Self>| match op {
            RegexOp::Char(ch) => {
                let storage = vec![
                    LazyNode { nexts: HashMap::from([(ch, 1)]), epsilons: Vec::new(), symbol: None },
                    LazyNode { nexts: HashMap::new(), epsilons: Vec::new(), symbol: None }
                ];
                LazyLexer { storage, fst: 0, last: 1 }
            },
            RegexOp::Concat((fst, snd)) => fst.append(snd),
            RegexOp::Or((fst, snd)) => fst.or(snd),
            RegexOp::KleeneClosure(operand) => operand.kleene_closure(),
        });
        result.storage[result.last].symbol = Some(symbol.clone());
        result
    }

    pub fn append(mut self: Self, mut snd: Self) -> Self {
        let self_n = self.storage.len();
        snd.fst += self_n;
        snd.last += self_n;
        for node in snd.storage.iter_mut() {
            for (_, val) in node.nexts.iter_mut() {
                *val += self_n;
            }
            for epsilon in node.epsilons.iter_mut() {
                *epsilon += self_n;
            }
        }
        self.storage.append(&mut snd.storage);
        self.storage[self.last].epsilons.push(snd.fst);
        self.last = snd.last;
        self
    }

    pub fn or(mut self: Self, mut snd: Self) -> Self {
        let self_original_n = self.storage.len();

        snd.fst += self_original_n;
        snd.last += self_original_n;
        for node in snd.storage.iter_mut() {
            for (_, val) in node.nexts.iter_mut() {
                *val += self_original_n;
            }
            for epsilon in node.epsilons.iter_mut() {
                *epsilon += self_original_n;
            }
        }
        self.storage.append(&mut snd.storage);

        let new_fst = LazyNode {
            nexts: HashMap::new(),
            epsilons: vec![self.fst, snd.fst],
            symbol: None
        };
        self.fst = self.storage.len();
        self.storage.push(new_fst);

        let new_last = LazyNode {
            nexts: HashMap::new(),
            epsilons: Vec::<usize>::new(),
            symbol: None
        };
        let new_last_idx = self.storage.len();
        self.storage.push(new_last);
        self.storage[self.last].epsilons.push(new_last_idx);
        self.storage[snd.last].epsilons.push(new_last_idx);
        self.last = new_last_idx;

        self
    }

    pub fn kleene_closure(mut self: Self) -> Self {
        let new_last = LazyNode {
            nexts: HashMap::new(),
            epsilons: Vec::new(),
            symbol: None
        };
        self.storage.push(new_last);
        let n = self.storage.len() - 1;
        self.storage[self.last].epsilons.push(self.fst);
        self.storage[self.last].epsilons.push(n);
        self.last = n;

        let new_fst = LazyNode {
            nexts: HashMap::new(),
            epsilons: vec![self.storage.len() - 1, self.fst],
            symbol: None
        };
        self.storage.push(new_fst);
        self.fst = self.storage.len() - 1;

        self
    }

    pub fn realize(self: Self) -> Lexer<T> {
        let mut queue = VecDeque::from([self.fst]);
        let mut states = HashSet::<usize>::new();
        while let Some(curr) = queue.pop_front() {
            states.insert(curr);
            for epsilon in self.storage[curr].epsilons.iter() {
                queue.push_back(*epsilon);
            }
        }
        let symbol = states.iter()
            .fold(None, |acc, idx| acc.or(self.storage[*idx].symbol.clone()));
        let mut key = states.iter()
            .map(|s| format!("{}", s))
            .collect::<Vec<String>>();
        key.sort();
        let fst_key = key.join(", ");
        let mut main_queue = VecDeque::from([(fst_key.clone(), states, symbol)]);
        let mut table = HashMap::<String, (Option<Rc<dyn TokenBuilder<T>>>, HashMap<char, String>)>::new();
        while let Some((key, states, symbol)) = main_queue.pop_front() {
            if table.contains_key(&key) {
                continue;
            }
            let mut transitions = HashMap::<char, HashSet<usize>>::new();
            for state in states.into_iter() {
                for (key, value) in self.storage[state].nexts.iter() {
                    if let Some(val) = transitions.get_mut(key) {
                        val.insert(*value);
                    } else {
                        transitions.insert(*key, HashSet::from([*value]));
                    }
                }
            }
            let mut nexts = HashMap::<char, String>::new();
            for (key, mut value) in transitions.into_iter() {
                for idx in value.iter() {
                    queue.push_back(*idx);
                }
                while let Some(curr) = queue.pop_front() {
                    value.insert(curr);
                    for epsilon in self.storage[curr].epsilons.iter() {
                        queue.push_back(*epsilon);
                    }
                }
                let mut new_key = value.iter()
                    .map(|s| format!("{}", s))
                    .collect::<Vec<String>>();
                new_key.sort();
                let new_symbol = value.iter()
                    .fold(None, |acc, idx| acc.or(self.storage[*idx].symbol.clone()));
                main_queue.push_back((new_key.join(", "), value, new_symbol));
                nexts.insert(key, new_key.join(", ")); 
            }
            table.insert(key, (symbol, nexts));
        }
        let keys = table.keys().map(|k| k.clone()).collect::<Vec<String>>();
        let states_map = keys.iter().enumerate().map(|(idx, key)| ((*key).clone(), idx)).collect::<HashMap<String, usize>>();
        let mut storage = Vec::<Node<T>>::new();
        let fst = *states_map.get(&fst_key).unwrap();
        for key in keys.into_iter() {
            if let Some((symbol, nexts)) = table.remove(&key) {
                storage.push(Node { symbol, nexts: nexts.into_iter().map(|(key, val)| (key, *states_map.get(&val).unwrap())).collect::<HashMap<char, usize>>() })
            }
        }
        Lexer { storage, fst }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::boxed::Box;

    struct MockedRegexAst {
        head: RegexOp<Box<MockedRegexAst>>
    }

    struct MockedRegexAstView<'a> {
        head: &'a RegexOp<Box<MockedRegexAst>>
    }

    impl<'a> IRegexAstView<'a> for MockedRegexAstView<'a> {
        fn apply<T, F: Fn(RegexOp<T>) -> T>(self: Self, f: &F) -> T {
            match &self.head {
                RegexOp::Char(c) => f(RegexOp::Char(*c)),
                RegexOp::KleeneClosure(idx) => {
                    let operand_node = MockedRegexAstView { head: &idx.head };
                    f(RegexOp::KleeneClosure(operand_node.apply(f)))
                },
                RegexOp::Or((fst, snd)) => {
                    let fst_operand_node = MockedRegexAstView { head: &fst.head };
                    let snd_operand_node = MockedRegexAstView { head: &snd.head };
                    f(RegexOp::Or((fst_operand_node.apply(f), snd_operand_node.apply(f))))
                },
                RegexOp::Concat((fst, snd)) => {
                    let fst_operand_node = MockedRegexAstView { head: &fst.head };
                    let snd_operand_node = MockedRegexAstView { head: &snd.head };
                    f(RegexOp::Concat((fst_operand_node.apply(f), snd_operand_node.apply(f))))
                },
            }
        }
    }

    impl IRegexAst for MockedRegexAst {
        fn concat(self: Self, other: MockedRegexAst) -> MockedRegexAst {
            MockedRegexAst { head: RegexOp::Concat((Box::new(self), Box::new(other))) }
        }
        fn or(self: Self, other: MockedRegexAst) -> MockedRegexAst {
            MockedRegexAst { head: RegexOp::Or((Box::new(self), Box::new(other))) }
        }
        fn kleene_closure(self: Self) -> MockedRegexAst {
            MockedRegexAst { head: RegexOp::KleeneClosure(Box::new(self)) }
        }
        fn root(self: &Self) -> MockedRegexAstView {
            MockedRegexAstView { head: &self.head }
        }
    }

    #[test]
    fn tokenizes_correctly() -> Result<(), String> {
        let word_pattern = MockedRegexAst {
            head: RegexOp::Or((
                Box::new(MockedRegexAst { 
                    head: RegexOp::Concat((
                        Box::new(MockedRegexAst { head: RegexOp::Char('h')}),
                        Box::new(MockedRegexAst {
                            head: RegexOp::Concat((
                                Box::new(MockedRegexAst { head: RegexOp::Char('e')}),
                                Box::new(MockedRegexAst {
                                    head: RegexOp::Concat((
                                        Box::new(MockedRegexAst { head: RegexOp::Char('l')}),
                                        Box::new(MockedRegexAst {
                                            head: RegexOp::Concat((
                                                Box::new(MockedRegexAst { head: RegexOp::Char('l')}),
                                                Box::new(MockedRegexAst { head: RegexOp::Char('o')})
                                            ))
                                        })
                                    ))
                                })
                            ))
                        })
                    ))
                }),
                Box::new(MockedRegexAst {
                    head: RegexOp::Concat((
                        Box::new(MockedRegexAst { head: RegexOp::Char('w')}),
                        Box::new(MockedRegexAst {
                            head: RegexOp::Concat((
                                Box::new(MockedRegexAst { head: RegexOp::Char('o')}),
                                Box::new(MockedRegexAst {
                                    head: RegexOp::Concat((
                                        Box::new(MockedRegexAst { head: RegexOp::Char('r')}),
                                        Box::new(MockedRegexAst {
                                            head: RegexOp::Concat((
                                                Box::new(MockedRegexAst { head: RegexOp::Char('l')}),
                                                Box::new(MockedRegexAst { head: RegexOp::Char('d')}),
                                            ))
                                        })
                                    ))
                                })
                            ))
                        })
                    ))
                })
            ))
        };
        let number_pattern = MockedRegexAst { 
            head: RegexOp::KleeneClosure(Box::new(MockedRegexAst {
                head: RegexOp::Or((
                    Box::new(MockedRegexAst {
                        head: RegexOp::Or((
                            Box::new(MockedRegexAst {
                                head: RegexOp::Or((
                                    Box::new(MockedRegexAst {
                                        head: RegexOp::Or((
                                            Box::new(MockedRegexAst { head: RegexOp::Char('0')}),
                                            Box::new(MockedRegexAst { head: RegexOp::Char('1')}),
                                        ))
                                    }),
                                    Box::new(MockedRegexAst {
                                        head: RegexOp::Or((
                                            Box::new(MockedRegexAst { head: RegexOp::Char('2')}),
                                            Box::new(MockedRegexAst { head: RegexOp::Char('3')}),
                                        ))
                                    }),
                                ))
                            }),
                            Box::new(MockedRegexAst {
                                head: RegexOp::Or((
                                    Box::new(MockedRegexAst { head: RegexOp::Char('4')}),
                                    Box::new(MockedRegexAst { head: RegexOp::Char('5')}),
                                ))
                            }),
                        ))
                    }),
                    Box::new(MockedRegexAst {
                        head: RegexOp::Or((
                            Box::new(MockedRegexAst {
                                head: RegexOp::Or((
                                    Box::new(MockedRegexAst { head: RegexOp::Char('7')}),
                                    Box::new(MockedRegexAst { head: RegexOp::Char('8')}),
                                ))
                            }),
                            Box::new(MockedRegexAst {
                                head: RegexOp::Or((
                                    Box::new(MockedRegexAst { head: RegexOp::Char('8')}),
                                    Box::new(MockedRegexAst { head: RegexOp::Char('9')}),
                                ))
                            }),
                        ))
                    }),
                ))
            }))
        };
        let lexer = LazyLexer::new(word_pattern, Rc::new(WordBuilder))
            .or(LazyLexer::new(number_pattern, Rc::new(NumberBuilder)))
            .realize();
        let str = String::from("hello hello world 10984 293489 8391");
        let mut result = Vec::<Token>::new();
        let expected = [
            Token::Word(String::from("hello")),
            Token::Word(String::from("hello")),
            Token::Word(String::from("world")),
            Token::Number(10984),
            Token::Number(293489),
            Token::Number(8391)
        ];
        for res in lexer.tokenize(str) {
            result.push(res?);
        }
        assert!(result.into_iter().zip(expected.into_iter()).map(|(x, y)| x == y).fold(true, |acc, x| acc && x));
        Ok(())
    }
}
