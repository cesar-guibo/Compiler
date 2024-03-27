use std::cmp::Ordering;
use std::collections::{HashSet, HashMap};

use crate::parser::{Op, OpDrawingDescriptor, Ast, AstView};
use crate::tokens::Tokens;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
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
pub enum UnaryOp {
    SuffixIncrement,
    SuffixDecrement,
    PrefixIncrement,
    PrefixDecrement,
    FunctionCall,
    AttributeAcccess,
    AttributePointerAccess,
    UnaryPlus,
    UnaryMinus,
    LogicalNot,
    BitwiseNot,
    Cast,
    Dereference,
    AddressOf,
    Sizeof
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TernaryOp {}

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

#[derive(Debug, Clone)]
pub struct TypedVariable {
    pub name: String,
    pub t: String
}

#[derive(Debug, Clone)]
pub enum Value<T> {
    Literal(i32),
    Variable(T)
}


#[derive(Clone)]
pub struct Expression<T: std::fmt::Debug> {
    nodes: Vec<Op<UnaryOp, BinaryOp, TernaryOp, usize, Value<T>>>,
    head: usize
}

pub struct ExpressionView<'a, T: std::fmt::Debug + 'a> {
    nodes: &'a Vec<Op<UnaryOp, BinaryOp, TernaryOp, usize, Value<T>>>,
    head: usize
}

impl<T: std::fmt::Debug + std::clone::Clone> Ast<UnaryOp, BinaryOp, TernaryOp, usize, Value<T>> for Expression<T> {
    fn view(&self) -> ExpressionView<T> {
        ExpressionView {
            nodes: &self.nodes,
            head: self.head
        }
    }
}

impl<'a, T: std::fmt::Debug + std::clone::Clone> AstView<UnaryOp, BinaryOp, TernaryOp, usize, Value<T>> for ExpressionView<'a, T> {
    fn root(&self) -> Option<&Op<UnaryOp, BinaryOp, TernaryOp, usize, Value<T>>> {
       self.nodes.get(self.head)
    }

    fn subtree(&self, root: &usize) -> ExpressionView<T> {
        ExpressionView { nodes: self.nodes, head: *root }
    }
}

impl<T: std::fmt::Debug + std::clone::Clone> std::fmt::Debug for Expression<T> {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Expression")
    }
}

impl Expression<String> {
    pub fn new(tokens_stack: &mut Vec<Tokens>) -> Option<Expression<String>> {
        let x_token = tokens_stack.pop()?;
        let x = match &x_token {
            Tokens::IntegerNumber(x) => Value::Literal(*x),
            Tokens::Identifier(variable) => Value::Variable(variable.clone()),
            _ => {
                tokens_stack.push(x_token);
                return None;
            },
        };
        let operator = tokens_stack.pop().and_then(|token| match token {
            Tokens::MultiplySymbol => Some(BinaryOp::Multiply),
            Tokens::DivideSymbol => Some(BinaryOp::Divide),
            Tokens::AddSymbol => Some(BinaryOp::Add),
            Tokens::SubtractSymbol => Some(BinaryOp::Subtract),
            Tokens::BitShiftLeftSymbol => Some(BinaryOp::BitShiftLeft),
            Tokens::BitShiftRightSymbol => Some(BinaryOp::BitShiftRight),
            Tokens::BinaryAndSymbol => Some(BinaryOp::BinaryAnd),
            Tokens::BinaryXorSymbol => Some(BinaryOp::BinaryXor),
            Tokens::BinaryOrSymbol => Some(BinaryOp::BinaryOr),
            tk => {
                tokens_stack.push(tk);
                None
            }
        });
        if let Some((operator, mut result)) = operator.zip(Expression::new(tokens_stack)) {
            let mut current_idx = result.head;
            return loop {
                let current = &result.nodes[current_idx];
                current_idx = match current {
                    Op::Value(_) => {
                        let fst = result.nodes.len();
                        result.nodes.push(Op::Value(x));
                        let new_node_idx = result.nodes.len();
                        result.nodes.push(Op::BinaryOp(operator, fst, new_node_idx));
                        result.nodes.swap(current_idx, new_node_idx);
                        break Some(result);
                    }
                    Op::BinaryOp(op, left, _) => {
                        if *op >= operator {
                            let fst = result.nodes.len();
                            result.nodes.push(Op::Value(x));
                            let new_node_idx = result.nodes.len();
                            result.nodes.push(Op::BinaryOp(operator, fst, new_node_idx));
                            result.nodes.swap(current_idx, new_node_idx);
                            break Some(result);
                        }
                        *left
                    }
                    Op::UnaryOp(_, child) => *child,
                    Op::TernaryOp(..) => { panic!(); }
                }
            };
        } else {
            Some(Expression { nodes: vec![Op::Value(x)], head: 0 })
        }
    }
    pub fn to_typed(self: Self, scope: HashMap<String, String>) -> (Option<Result<Expression<TypedVariable>, String>>, HashMap<String, String>) {
        self.view().apply_with_state(&|op, scope: &mut HashMap<String, String>| {
            match op {
                Op::<&UnaryOp, &BinaryOp, &TernaryOp, Result<Expression<TypedVariable>, String>, &Value<String>>::Value(val) => {
                    let val = match val {
                        Value::Literal(i) => Value::Literal(i.clone()),
                        Value::Variable(var) => {
                            if let Some(t) = scope.get(var) {
                                Value::Variable(TypedVariable { name: var.clone(), t: t.clone() })
                            } else {
                                return Err(String::from(""));
                            }
                        }
                    };
                    Ok(Expression { nodes: vec![Op::Value(val)], head: 0 })
                },
                Op::UnaryOp(..) | Op::TernaryOp(..) => {
                    panic!();
                },
                Op::BinaryOp(op, fst_result, snd_result) => {
                    let mut fst: Expression<TypedVariable> = fst_result.unwrap();
                    let mut snd: Expression<TypedVariable> = snd_result.unwrap();
                    let fst_n = fst.nodes.len();
                    snd.head += fst_n;
                    snd.nodes = snd.nodes.into_iter().map(|op| match op {
                        Op::UnaryOp(op, idx) => Op::UnaryOp(op, idx + fst_n),
                        Op::BinaryOp(op, fst, snd) => Op::BinaryOp(op, fst + fst_n, snd + fst_n),
                        Op::TernaryOp(op, fst, snd, third) => Op::TernaryOp(op, fst + fst_n, snd + fst_n, third + fst_n),
                        val => val
                    }).collect();
                    fst.nodes.append(&mut snd.nodes);
                    fst.nodes.push(Op::BinaryOp(op.clone(), fst.head, snd.head));
                    fst.head = fst.nodes.len() - 1;
                    Ok(fst)
                },
            }
        }, scope)
    }
}
