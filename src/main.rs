use std::rc::Rc;
use std::cmp::Ordering;


mod lexer;
mod parser;

use lexer::regex::RegexAst;
use lexer::{LazyLexer, Lexer};
use parser::{Ast, AstView, Op};

#[derive(Debug)]
enum Tokens {
    Type(String),
    Identifier(String),
    IntegerNumber(i32),
    AssignSymbol,
    AddSymbol,
    SubtractSymbol,
    MultiplySymbol,
    DivideSymbol,
    BinaryOrSymbol,
    BinaryAndSymbol,
    BinaryXorSymbol,
    BitShiftLeftSymbol,
    BitShiftRightSymbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinaryOp {
    Add,
    Multiply,
    Subtract,
    Divide,
    BinaryAnd,
    BinaryOr,
    BitShiftLeft,
    BitShiftRight,
    BinaryXor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnaryOp {}

impl Ord for BinaryOp {
    fn cmp(self: &Self, other: &Self) -> Ordering {
        match (self, other) {
            (BinaryOp::Multiply, BinaryOp::Multiply) => Ordering::Equal,
            (BinaryOp::Multiply, BinaryOp::Divide) => Ordering::Equal,
            (BinaryOp::Multiply, BinaryOp::Add) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::Subtract) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::BitShiftLeft) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::BitShiftRight) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::Multiply, BinaryOp::BinaryOr) => Ordering::Greater,

            (BinaryOp::Divide, BinaryOp::Divide) => Ordering::Equal,
            (BinaryOp::Divide, BinaryOp::Multiply) => Ordering::Equal,
            (BinaryOp::Divide, BinaryOp::Add) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::Subtract) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::BitShiftLeft) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::BitShiftRight) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::Divide, BinaryOp::BinaryOr) => Ordering::Greater,

            (BinaryOp::Add, BinaryOp::Add) => Ordering::Equal,
            (BinaryOp::Add, BinaryOp::Subtract) => Ordering::Equal,
            (BinaryOp::Add, BinaryOp::BitShiftLeft) => Ordering::Greater,
            (BinaryOp::Add, BinaryOp::BitShiftRight) => Ordering::Greater,
            (BinaryOp::Add, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::Add, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::Add, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::Add, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::Add, BinaryOp::Divide) => Ordering::Less,

            (BinaryOp::Subtract, BinaryOp::Subtract) => Ordering::Equal,
            (BinaryOp::Subtract, BinaryOp::Add) => Ordering::Equal,
            (BinaryOp::Subtract, BinaryOp::BitShiftLeft) => Ordering::Greater,
            (BinaryOp::Subtract, BinaryOp::BitShiftRight) => Ordering::Greater,
            (BinaryOp::Subtract, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::Subtract, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::Subtract, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::Subtract, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::Subtract, BinaryOp::Divide) => Ordering::Less,

            (BinaryOp::BitShiftLeft, BinaryOp::BitShiftLeft) => Ordering::Equal,
            (BinaryOp::BitShiftLeft, BinaryOp::BitShiftRight) => Ordering::Equal,
            (BinaryOp::BitShiftLeft, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::BitShiftLeft, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::BitShiftLeft, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::BitShiftLeft, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::BitShiftLeft, BinaryOp::Divide) => Ordering::Less,
            (BinaryOp::BitShiftLeft, BinaryOp::Add) => Ordering::Less,
            (BinaryOp::BitShiftLeft, BinaryOp::Subtract) => Ordering::Less,


            (BinaryOp::BitShiftRight, BinaryOp::BitShiftRight) => Ordering::Equal,
            (BinaryOp::BitShiftRight, BinaryOp::BitShiftLeft) => Ordering::Equal,
            (BinaryOp::BitShiftRight, BinaryOp::BinaryAnd) => Ordering::Greater,
            (BinaryOp::BitShiftRight, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::BitShiftRight, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::BitShiftRight, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::BitShiftRight, BinaryOp::Divide) => Ordering::Less,
            (BinaryOp::BitShiftRight, BinaryOp::Add) => Ordering::Less,
            (BinaryOp::BitShiftRight, BinaryOp::Subtract) => Ordering::Less,

            (BinaryOp::BinaryAnd, BinaryOp::BinaryAnd) => Ordering::Equal,
            (BinaryOp::BinaryAnd, BinaryOp::BinaryXor) => Ordering::Greater,
            (BinaryOp::BinaryAnd, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::BinaryAnd, BinaryOp::Divide) => Ordering::Less,
            (BinaryOp::BinaryAnd, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::BinaryAnd, BinaryOp::Add) => Ordering::Less,
            (BinaryOp::BinaryAnd, BinaryOp::Subtract) => Ordering::Less,
            (BinaryOp::BinaryAnd, BinaryOp::BitShiftLeft) => Ordering::Less,
            (BinaryOp::BinaryAnd, BinaryOp::BitShiftRight) => Ordering::Less,

            (BinaryOp::BinaryXor, BinaryOp::BinaryXor) => Ordering::Equal,
            (BinaryOp::BinaryXor, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::BinaryXor, BinaryOp::Divide) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::Add) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::Subtract) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::BitShiftLeft) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::BitShiftRight) => Ordering::Less,
            (BinaryOp::BinaryXor, BinaryOp::BinaryAnd) => Ordering::Less,

            (BinaryOp::BinaryOr, BinaryOp::BinaryOr) => Ordering::Greater,
            (BinaryOp::BinaryOr, BinaryOp::Divide) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::Multiply) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::Add) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::Subtract) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::BitShiftLeft) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::BitShiftRight) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::BinaryAnd) => Ordering::Less,
            (BinaryOp::BinaryOr, BinaryOp::BinaryXor) => Ordering::Less,
        }
    }
}

impl PartialOrd for BinaryOp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Op<UnaryOp, BinaryOp, usize, Value> {
    fn eq(self: &Self, other: &Self) -> bool {
        match (self, other) {
            (Op::Value(_), Op::Value(_)) => true,
            (Op::BinaryOp(x, ..), Op::BinaryOp(y, ..)) => x == y,
            (Op::UnaryOp(x, ..), Op::UnaryOp(y, ..)) => x == y,
            _ => false
        }
    }
}

impl Eq for Op<UnaryOp, BinaryOp, usize, Value> {}

impl Ord for Op<UnaryOp, BinaryOp, usize, Value> {
    fn cmp(self: &Self, other: &Self) -> Ordering {
        match (self, other) {
            (Op::Value(_), Op::Value(_)) => Ordering::Equal,
            (Op::Value(_), Op::BinaryOp(..)) => Ordering::Greater,
            (Op::Value(_), Op::UnaryOp(..)) => Ordering::Greater,
            (Op::UnaryOp(..), Op::UnaryOp(..)) => Ordering::Equal,
            (Op::UnaryOp(..), Op::BinaryOp(..)) => Ordering::Greater,
            (Op::UnaryOp(..), Op::Value(_)) => Ordering::Less,
            (Op::BinaryOp(x, ..), Op::BinaryOp(y, ..)) => x.cmp(y),
            (Op::BinaryOp(..), Op::UnaryOp(..)) => Ordering::Less,
            (Op::BinaryOp(..), Op::Value(_)) => Ordering::Less,
        }
    }
}

impl PartialOrd for Op<UnaryOp, BinaryOp, usize, Value> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone)]
enum Value {
    Literal(i32),
    Variable(String)
}


struct Instruction {
    nodes: Vec<Op<UnaryOp, BinaryOp, usize, Value>>,
    head: usize
}


struct InstructionView<'a> {
    nodes: &'a Vec<Op<UnaryOp, BinaryOp, usize, Value>>,
    head: usize
}


struct Expression {
    nodes: Vec<Op<UnaryOp, BinaryOp, usize, Value>>,
    head: usize
}

struct ExpressionView<'a> {
    nodes: &'a Vec<Op<UnaryOp, BinaryOp, usize, Value>>,
    head: usize
}

impl Ast<UnaryOp, BinaryOp, usize, Value> for Expression {
    fn root(self: &Self) -> ExpressionView {
        ExpressionView {
            nodes: &self.nodes,
            head: self.head
        }
    }
}

impl<'a> AstView<'a, UnaryOp, BinaryOp, Value> for ExpressionView<'a> {
    // Post order
    fn apply<T, F: Fn(Op<UnaryOp, BinaryOp, T, Value>) -> T>(self: Self, f: &F) -> Option<T> {
        match self.nodes.get(self.head)? {
            Op::Value(c) => Some(f(Op::Value(c.clone()))),
            Op::UnaryOp(..) => {
                panic!();
            },
            Op::BinaryOp(binary_op, fst, snd) => {
                let fst_subtree = ExpressionView { nodes: self.nodes, head: *fst };
                let fst_operand = fst_subtree.apply(f)?;
                let snd_subtree = ExpressionView { nodes: self.nodes, head: *snd };
                let snd_operand = snd_subtree.apply(f)?;
                Some(f(Op::BinaryOp(*binary_op, fst_operand, snd_operand)))
            },
        }
    }
}

impl std::fmt::Debug for Expression {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.draw(f)
    }
}

impl Expression {
    pub fn new(mut tokens_stack: Vec<Tokens>) -> Result<Expression, String> {
        let x = match tokens_stack.pop() {
            Some(Tokens::IntegerNumber(x)) => Value::Literal(x),
            Some(Tokens::Identifier(variable)) => Value::Variable(variable),
            _ => {
                return Err(String::from(""));
            }
        };
        if let Some(token) = tokens_stack.pop() {
            let mut result = Expression::new(tokens_stack)?;
            let mut current_idx = result.head;
            let operator = match token {
                Tokens::MultiplySymbol => BinaryOp::Multiply,
                Tokens::DivideSymbol => BinaryOp::Divide,
                Tokens::AddSymbol => BinaryOp::Add,
                Tokens::SubtractSymbol => BinaryOp::Subtract,
                Tokens::BitShiftLeftSymbol => BinaryOp::BitShiftLeft,
                Tokens::BitShiftRightSymbol => BinaryOp::BitShiftRight,
                Tokens::BinaryAndSymbol => BinaryOp::BinaryAnd,
                Tokens::BinaryXorSymbol => BinaryOp::BinaryXor,
                Tokens::BinaryOrSymbol => BinaryOp::BinaryOr,
                _ => {
                    return Err(String::from(""));
                }
            };
            return loop {
                let current = &result.nodes[current_idx];
                current_idx = match current {
                    Op::Value(_) => {
                        let fst = result.nodes.len();
                        result.nodes.push(Op::Value(x));
                        let new_node_idx = result.nodes.len();
                        result.nodes.push(Op::BinaryOp(operator, fst, new_node_idx));
                        result.nodes.swap(current_idx, new_node_idx);
                        break Ok(result);
                    }
                    Op::BinaryOp(op, left, _) => {
                        if *op >= operator {
                            let fst = result.nodes.len();
                            result.nodes.push(Op::Value(x));
                            let new_node_idx = result.nodes.len();
                            result.nodes.push(Op::BinaryOp(operator, fst, new_node_idx));
                            result.nodes.swap(current_idx, new_node_idx);
                            break Ok(result);
                        }
                        *left
                    }
                    Op::UnaryOp(_, child) => *child
                }
            };
        } else {
            Ok(Expression { nodes: vec![Op::Value(x)], head: 0 })
        }
    }
}


fn main() {
    let lexer: Lexer<Tokens> = LazyLexer::new(RegexAst::new("[0-9][0-9]*").unwrap(), Rc::new(|s| Tokens::IntegerNumber(i32::from_str_radix(&s, 10).unwrap())))
        .or(LazyLexer::new(RegexAst::new("[a-zA-Z_][a-zA-Z0-9_]*").unwrap(), Rc::new(|s| Tokens::Identifier(s))))
        .or(LazyLexer::new(RegexAst::new("int").unwrap(), Rc::new(|s| Tokens::Type(s))))
        .or(LazyLexer::new(RegexAst::new("=").unwrap(), Rc::new(|_| Tokens::AssignSymbol)))
        .or(LazyLexer::new(RegexAst::new("+").unwrap(), Rc::new(|_| Tokens::AddSymbol)))
        .or(LazyLexer::new(RegexAst::new("-").unwrap(), Rc::new(|_| Tokens::SubtractSymbol)))
        .or(LazyLexer::new(RegexAst::new("\\*").unwrap(), Rc::new(|_| Tokens::MultiplySymbol)))
        .or(LazyLexer::new(RegexAst::new("/").unwrap(), Rc::new(|_| Tokens::DivideSymbol)))
        .or(LazyLexer::new(RegexAst::new("\\|").unwrap(), Rc::new(|_| Tokens::BinaryOrSymbol)))
        .or(LazyLexer::new(RegexAst::new("&").unwrap(), Rc::new(|_| Tokens::BinaryAndSymbol)))
        .or(LazyLexer::new(RegexAst::new("^").unwrap(), Rc::new(|_| Tokens::BinaryXorSymbol)))
        .or(LazyLexer::new(RegexAst::new("<<").unwrap(), Rc::new(|_| Tokens::BitShiftLeftSymbol)))
        .or(LazyLexer::new(RegexAst::new(">>").unwrap(), Rc::new(|_| Tokens::BitShiftRightSymbol)))
        .realize();
    let s = String::from("2 + 3 * 5 / 10 >> 3 & 2 + 3 * 5 / 10 << 5 | 20 ^ 10 + 20 & 2 + 3 * 10 + 5 / 10");
    println!("{}", &s);
    let mut tokens = Vec::<Tokens>::new();
    for token in lexer.tokenize(s) {
        tokens.push(token.unwrap());
    }
    //println!("{:?}", &tokens);
    println!("{:?}", Expression::new(tokens).unwrap());
}
