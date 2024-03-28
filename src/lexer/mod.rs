// What should happen when a sequence is accepted by two different tokens

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

pub mod regex;

use crate::parser::{Ast, AstView};
use regex::{RegexOpRefs, RegexBinaryOp, RegexUnaryOp, RegexTernaryOp};

#[derive(Clone)]
struct Node<T> {
  nexts: HashMap<char, usize>,
  symbol: Option<Rc<dyn Fn(String) -> T>>
}


#[derive(Clone)]
pub struct Lexer<T> {
  storage: Vec<Node<T>>,
  fst: usize
}

pub struct TokenIter<'a, T> {
  next_ch: Option<char>,
  chars: std::vec::IntoIter<char>,
  ignore: HashSet<char>,
  lexer: &'a Lexer<T>,
  line: usize,
  column: usize
}

impl<'a, T> std::iter::Iterator for TokenIter<'a, T> {
  type Item = Result<T, String>;

  fn next(self: &mut Self) -> Option<Self::Item> {
    let mut current = &self.lexer.storage[self.lexer.fst];
    let mut state = Vec::<char>::new();
    while let Some(ch) = self.next_ch {
      if !self.ignore.contains(&ch) {
        break;
      }
      if ch == '\n' {
        self.line += 1;
      } else {
        self.column += 1;
      }
      self.next_ch = self.chars.next();
    }
    if self.next_ch.is_none() {
      return None;
    }
    while let Some(ch) = self.next_ch {
      if let Some(next_node) = current.nexts.get(&ch) {
        state.push(ch);
        self.column += 1;
        self.next_ch = self.chars.next();
        current = &self.lexer.storage[*next_node];
      } else {
        break;
      }
    }
    let s = state.into_iter().collect::<String>();
    return match current.symbol.as_ref() {
      Some(builder) => Some(Ok(builder(s))),
      None => Some(Err(format!("Invalid string at {},{}.\n\t\"{}\"", self.line, self.column, s)))
    };
  }
}

impl<T> Lexer<T> {
  pub fn tokenize(self: &Self, s: String) -> TokenIter<T> {
    let mut chars = s.chars().collect::<Vec<char>>().into_iter();
    TokenIter {
      next_ch: chars.next(),
      chars,
      ignore: HashSet::from([' ', '\t', '\r', '\n']),
      lexer: self,
      line: 0,
      column: 0
    }
  }
}


#[derive(Clone)]
struct LazyNode<T> {
  nexts: HashMap<char, usize>,
  epsilons: Vec<usize>,
  symbol: Option<Rc<dyn Fn(String) -> T>>
}


#[derive(Clone)]
pub struct LazyLexer<T> {
  storage: Vec<LazyNode<T>>,
  fst: usize,
  last: usize
}

impl<T> std::fmt::Debug for LazyLexer<T> {
  fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "fst: {}, last: {}\n{:?}", self.fst, self.last, self.storage.iter().enumerate().map(|(i, x)| (i, &x.nexts, &x.epsilons)).collect::<Vec<(usize, &HashMap<char, usize>, &Vec<usize>)>>())
  }
}


impl<T: std::fmt::Debug> LazyLexer<T> {
  pub fn new<U: std::fmt::Debug, V: Ast<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, U, char>>(pattern: V, symbol: Rc<dyn Fn(String) -> T>) -> LazyLexer<T> {
    let result = pattern.view().apply(&|op| match op {
      RegexOpRefs::<LazyLexer<T>>::Value(ch) => {
        let storage = vec![
          LazyNode { nexts: HashMap::from([(*ch, 1)]), epsilons: Vec::new(), symbol: None },
          LazyNode { nexts: HashMap::new(), epsilons: Vec::new(), symbol: None }
        ];
        LazyLexer { storage, fst: 0, last: 1 }
      },
      RegexOpRefs::<LazyLexer<T>>::UnaryOp(RegexUnaryOp::KleeneClosure, operand) => {
        operand.kleene_closure()
      },
      RegexOpRefs::<LazyLexer<T>>::BinaryOp(RegexBinaryOp::Concat, fst, snd) => fst.append(snd),
      RegexOpRefs::<LazyLexer<T>>::BinaryOp(RegexBinaryOp::Or, fst, snd) => fst.or(snd),
      RegexOpRefs::<LazyLexer<T>>::TernaryOp(..) => { panic!(); },
    });
    if let Some(mut res) = result {
      res.storage[res.last].symbol = Some(symbol.clone());
      res
    } else {
      LazyLexer { storage: Vec::<LazyNode<T>>::new(), fst: 0, last: 0 }
    }
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
      epsilons: vec![self.last, self.fst],
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
    let mut table = HashMap::<String, (Option<Rc<dyn Fn(String) -> T>>, HashMap<char, String>)>::new();
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
  use std::str::FromStr;
  use crate::parser::Op;
  use regex::RegexOp;

  #[derive(Debug, Clone)]
  struct MockedRegexAst {
    head: RegexOp<Box<MockedRegexAst>>
  }

  impl AstView<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, Box<MockedRegexAst>, char> for MockedRegexAst {
    fn subtree(&self, root: &Box<MockedRegexAst>) -> MockedRegexAst {
      root.as_ref().clone()
    }
    fn root(&self) -> Option<&Op<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, Box<MockedRegexAst>, char>> {
      Some(&self.head)
    }
  }

  impl Ast<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, Box<MockedRegexAst>, char> for MockedRegexAst {
    fn view(&self) -> MockedRegexAst {
      self.clone()
    }
  }

  #[derive(Clone, Debug, PartialEq)]
  pub enum Token {
    Word(String),
    Unsigned(u32),
    Float(f32)
  }

  #[test]
  fn tokenizes_correctly() -> Result<(), String> {
    let word_pattern = MockedRegexAst {
      head: RegexOp::BinaryOp(RegexBinaryOp::Or,
                              Box::new(MockedRegexAst { 
                                head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                        Box::new(MockedRegexAst { head: RegexOp::Value('h')}),
                                                        Box::new(MockedRegexAst {
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('e')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                            Box::new(MockedRegexAst {
                                                                                                              head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('o')})
                                                                                                                                     )
                                                                                                            })
                                                                                                           )
                                                                                  })
                                                                                 )
                                                        })
                                                       )
                              }),
                              Box::new(MockedRegexAst {
                                head: RegexOp::BinaryOp(RegexBinaryOp::Or,
                                                        Box::new(MockedRegexAst { 
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('h')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('e')}),
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                            )
                                                                                  })
                                                                                 )
                                                        }),
                                                        Box::new(MockedRegexAst {
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('w')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('o')}),
                                                                                                            Box::new(MockedRegexAst {
                                                                                                              head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('r')}),
                                                                                                                                      Box::new(MockedRegexAst {
                                                                                                                                        head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                                                Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                                                                                Box::new(MockedRegexAst { head: RegexOp::Value('d')}),
                                                                                                                                                                )
                                                                                                                                      })
                                                                                                                                     )
                                                                                                            })
                                                                                                           )
                                                                                  })
                                                                                 )
                                                        })
                                )
                              })
      )
    };
    let unsigned_pattern = MockedRegexAst { 
      head: RegexOp::UnaryOp(
              RegexUnaryOp::KleeneClosure,
              Box::new(MockedRegexAst {
                head: RegexOp::BinaryOp(
                        RegexBinaryOp::Or,
                        Box::new(MockedRegexAst {
                          head: RegexOp::BinaryOp(
                                  RegexBinaryOp::Or,
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('0')}),
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('1')}),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('2')}),
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('3')}),
                                                      )
                                            }),
                                            )
                                  }),
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst { head: RegexOp::Value('4')}),
                                            Box::new(MockedRegexAst { head: RegexOp::Value('5')}),
                                            )
                                  }),
                                  )
                        }),
                        Box::new(MockedRegexAst {
                          head: RegexOp::BinaryOp(
                                  RegexBinaryOp::Or,
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst { head: RegexOp::Value('7')}),
                                            Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                            )
                                  }),
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                            Box::new(MockedRegexAst { head: RegexOp::Value('9')}),
                                            )
                                  }),
                                  )
                        }),
                        )
              })
      )
    };
    let float_pattern = MockedRegexAst { 
      head: RegexOp::BinaryOp(
              RegexBinaryOp::Concat,
              Box::new(MockedRegexAst {
                head: RegexOp::BinaryOp(
                        RegexBinaryOp::Concat,
                        Box::new(MockedRegexAst{
                          head: RegexOp::BinaryOp(
                                  RegexBinaryOp::Or,
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('0')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('1')}),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('2')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('3')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('4')}),
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('5')}),
                                                      )
                                            }),
                                            )
                                  }),
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('7')}),
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                      Box::new(MockedRegexAst { head: RegexOp::Value('9')}),
                                                      )
                                            }),
                                            )
                                  }),
                                  )
                        }),
                        Box::new(MockedRegexAst {
                          head: RegexOp::UnaryOp(
                                  RegexUnaryOp::KleeneClosure,
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('0')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('1')}),
                                                                          )
                                                                }),
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('2')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('3')}),
                                                                          )
                                                                }),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('4')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('5')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('7')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('9')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            )
                                  })
                          )
                        })
                )
              }),
              Box::new(MockedRegexAst {
                head: RegexOp::BinaryOp(
                        RegexBinaryOp::Concat,
                        Box::new(MockedRegexAst {
                          head: RegexOp::BinaryOp(
                                  RegexBinaryOp::Concat,
                                  Box::new(MockedRegexAst { head: RegexOp::Value('.') }),
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('0')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('1')}),
                                                                          )
                                                                }),
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('2')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('3')}),
                                                                          )
                                                                }),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('4')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('5')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('7')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('9')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            )
                                  })
                          )
                        }),
                        Box::new(MockedRegexAst {
                          head: RegexOp::UnaryOp(
                                  RegexUnaryOp::KleeneClosure,
                                  Box::new(MockedRegexAst {
                                    head: RegexOp::BinaryOp(
                                            RegexBinaryOp::Or,
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('0')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('1')}),
                                                                          )
                                                                }),
                                                                Box::new(MockedRegexAst {
                                                                  head: RegexOp::BinaryOp(
                                                                          RegexBinaryOp::Or,
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('2')}),
                                                                          Box::new(MockedRegexAst { head: RegexOp::Value('3')}),
                                                                          )
                                                                }),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('4')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('5')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            Box::new(MockedRegexAst {
                                              head: RegexOp::BinaryOp(
                                                      RegexBinaryOp::Or,
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('7')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                )
                                                      }),
                                                      Box::new(MockedRegexAst {
                                                        head: RegexOp::BinaryOp(
                                                                RegexBinaryOp::Or,
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('8')}),
                                                                Box::new(MockedRegexAst { head: RegexOp::Value('9')}),
                                                                )
                                                      }),
                                                      )
                                            }),
                                            )
                                  }),
                                  )
                        }),
                        )
              })
      )
    };
    let lexer = LazyLexer::new(word_pattern, Rc::new(|s| Token::Word(s)))
      .or(LazyLexer::new(unsigned_pattern, Rc::new(|s| Token::Unsigned(u32::from_str_radix(&s, 10).unwrap()))))
      .or(LazyLexer::new(float_pattern, Rc::new(|s| Token::Float(f32::from_str(&s).unwrap()))))
      .realize();
    let str = String::from("hello\thel world 10984\r\n293489 839 10.984 293.489 8.391");
    let mut result = Vec::<Token>::new();
    let expected = [
      Token::Word(String::from("hello")),
      Token::Word(String::from("hel")),
      Token::Word(String::from("world")),
      Token::Unsigned(10984),
      Token::Unsigned(293489),
      Token::Unsigned(839),
      Token::Float(10.984),
      Token::Float(293.489),
      Token::Float(8.391),
    ];
    for res in lexer.tokenize(str) {
      result.push(res?);
    }
    assert_eq!(&result[..], &expected[..]);
    Ok(())
  }

  #[test]
  fn returns_error_for_invalid_string() {
    let word_pattern = MockedRegexAst {
      head: RegexOp::BinaryOp(RegexBinaryOp::Or,
                              Box::new(MockedRegexAst { 
                                head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                        Box::new(MockedRegexAst { head: RegexOp::Value('h')}),
                                                        Box::new(MockedRegexAst {
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('e')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                            Box::new(MockedRegexAst {
                                                                                                              head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('o')})
                                                                                                                                     )
                                                                                                            })
                                                                                                           )
                                                                                  })
                                                                                 )
                                                        })
                                                       )
                              }),
                              Box::new(MockedRegexAst {
                                head: RegexOp::BinaryOp(RegexBinaryOp::Or,
                                                        Box::new(MockedRegexAst { 
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('h')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('e')}),
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                            )
                                                                                  })
                                                                                 )
                                                        }),
                                                        Box::new(MockedRegexAst {
                                                          head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                  Box::new(MockedRegexAst { head: RegexOp::Value('w')}),
                                                                                  Box::new(MockedRegexAst {
                                                                                    head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                            Box::new(MockedRegexAst { head: RegexOp::Value('o')}),
                                                                                                            Box::new(MockedRegexAst {
                                                                                                              head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                      Box::new(MockedRegexAst { head: RegexOp::Value('r')}),
                                                                                                                                      Box::new(MockedRegexAst {
                                                                                                                                        head: RegexOp::BinaryOp(RegexBinaryOp::Concat,
                                                                                                                                                                Box::new(MockedRegexAst { head: RegexOp::Value('l')}),
                                                                                                                                                                Box::new(MockedRegexAst { head: RegexOp::Value('d')}),
                                                                                                                                                                )
                                                                                                                                      })
                                                                                                                                     )
                                                                                                            })
                                                                                                           )
                                                                                  })
                                                                                 )
                                                        })
                                )
                              })
      )
    };
    let lexer = LazyLexer::new(word_pattern, Rc::new(|s| Token::Word(s)))
      .realize();
    let str = String::from("hello\thel world 10984\r\n293489 839 10.984 293.489 8.391");
    for res in lexer.tokenize(str) {
      if res.is_err() {
        return
      }
    }
    panic!()
  }
}
