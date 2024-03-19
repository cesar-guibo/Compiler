use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

mod regex;

use regex::{RegexAst, RegexRealizedOp};

#[derive(Clone, Debug)]
pub enum Token {
    Identifier(String),
    Type(String),
    Ivalid
}

pub trait TokenBuilder : std::fmt::Debug {
    fn to_token(self: &Self, str: String) -> Token;
}

struct IdentifierBuilder;
impl TokenBuilder for IdentifierBuilder {
    fn to_token(self: &Self, str: String) -> Token {
        Token::Identifier(str)
    }
}
impl std::fmt::Debug for IdentifierBuilder {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "IdentifierBuilder")
    }
}

struct TypeBuilder;
impl TokenBuilder for TypeBuilder {
    fn to_token(self: &Self, str: String) -> Token {
        Token::Type(str)
    }
}
impl std::fmt::Debug for TypeBuilder {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "TypeBuilder")
    }
}


#[derive(Clone, Debug)]
struct Node {
    nexts: HashMap<char, usize>,
    symbol: Option<Rc<dyn TokenBuilder>>
}


#[derive(Clone, Debug)]
pub struct Lexer {
    storage: Vec<Node>,
    fst: usize
}

#[derive(Clone, Debug)]
struct LazyNode {
    nexts: HashMap<char, usize>,
    epsilons: Vec<usize>,
    symbol: Option<Rc<dyn TokenBuilder>>
}


#[derive(Clone, Debug)]
struct LazyLexer {
    storage: Vec<LazyNode>,
    fst: usize,
    last: usize
}

impl LazyLexer {
    pub fn new(pattern: &str, symbol: Rc<dyn TokenBuilder>) -> Result<LazyLexer, String> {
        let ast = RegexAst::new(pattern)?;
        let mut result = ast.root().apply(&|op| LazyLexer::from_regex_op(op))?;
        result.storage[result.last].symbol = Some(symbol.clone());
        Ok(result)
    }

    pub fn from_regex_op(op: RegexRealizedOp<Result<LazyLexer, String>>) -> Result<LazyLexer, String> {
        match op {
            RegexRealizedOp::Char(ch) => {
                let storage = vec![
                    LazyNode { nexts: HashMap::from([(ch, 1)]), epsilons: Vec::new(), symbol: None },
                    LazyNode { nexts: HashMap::new(), epsilons: Vec::new(), symbol: None }
                ];
                Ok(LazyLexer { storage, fst: 0, last: 1 })
            },
            RegexRealizedOp::Concat((fst, snd)) => fst?.append(snd?),
            RegexRealizedOp::Or((fst, snd)) => fst?.or(snd?),
            RegexRealizedOp::KleeneClosure(operand) => operand?.kleene_closure(),
        }
    }

    pub fn append(mut self: LazyLexer, mut snd: LazyLexer) -> Result<LazyLexer, String> {
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
        Ok(self)
    }

    pub fn or(mut self: LazyLexer, mut snd: LazyLexer) -> Result<LazyLexer, String> {
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

        Ok(self)
    }

    pub fn kleene_closure(mut self: LazyLexer) -> Result<LazyLexer, String> {

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

        Ok(self)
    }

    pub fn realize(self: LazyLexer) -> Result<Lexer, String> {
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
        let mut table = HashMap::<String, (Option<Rc<dyn TokenBuilder>>, HashMap<char, String>)>::new();
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
        let mut storage = Vec::<Node>::new();
        let fst = *states_map.get(&fst_key).unwrap();
        for key in keys.into_iter() {
            if let Some((symbol, nexts)) = table.remove(&key) {
                storage.push(Node { symbol, nexts: nexts.into_iter().map(|(key, val)| (key, *states_map.get(&val).unwrap())).collect::<HashMap<char, usize>>() })
            }
        }
        Ok(Lexer { storage, fst })
    }
}


fn main() {
    let aux = "Hello (World \\(W\\))*|(Mother \\\\ fucker \\(MF\\)). \\* \\| [abcdek]";
    println!("{}", RegexAst::new(aux).unwrap());
    println!("{}", RegexAst::new("a").unwrap());
    println!("{:?}\n", LazyLexer::new("ab(cd)*cde", Rc::new(IdentifierBuilder {})).unwrap());
    let fst = LazyLexer::new("((hello)|(ab(cd)*))cdcdef", Rc::new(IdentifierBuilder {})).unwrap();
    println!("{:?}\n", RegexAst::new("((hello)|(ab(cd)*))cdcdef").unwrap());
    println!("{:?}\n", &fst);
    println!("{:?}\n", fst.realize().unwrap());
}
