use std::cmp::Ordering;
use std::collections::HashMap;

use crate::parser::{Op, Ast, AstView};
use crate::tokens::Tokens;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprUnaryOp {
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
pub enum ExprBinaryOp {
  Add,
  Multiply,
  Subtract,
  Divide,
  BitwiseAnd,
  BitwiseOr,
  BitShiftLeft,
  BitShiftRight,
  BitwiseXor,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprTernaryOp {}

#[derive(Debug, Clone)]
pub struct TypedVariable {
  pub name: String,
  pub t: String
}

#[derive(Debug, Clone)]
pub enum ExprValue<T> {
  Literal(i32),
  Variable(T)
}

pub type ExprOp<T, U> = Op<
  ExprUnaryOp,
  ExprBinaryOp,
  ExprTernaryOp,
  T,
  ExprValue<U>
>;

pub type ExprOpRefs<'a, T, U> = Op<
  &'a ExprUnaryOp,
  &'a ExprBinaryOp,
  &'a ExprTernaryOp,
  T,
  &'a ExprValue<U>
>;

impl PartialOrd for ExprBinaryOp {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for ExprBinaryOp {
  fn cmp(self: &Self, other: &Self) -> Ordering {
    match (self, other) {
      (ExprBinaryOp::Multiply, ExprBinaryOp::Multiply) => Ordering::Equal,
      (ExprBinaryOp::Multiply, ExprBinaryOp::Divide) => Ordering::Equal,
      (ExprBinaryOp::Multiply, ExprBinaryOp::Add) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::Subtract) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::BitShiftLeft) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::BitShiftRight) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::Multiply, ExprBinaryOp::BitwiseOr) => Ordering::Greater,

      (ExprBinaryOp::Divide, ExprBinaryOp::Divide) => Ordering::Equal,
      (ExprBinaryOp::Divide, ExprBinaryOp::Multiply) => Ordering::Equal,
      (ExprBinaryOp::Divide, ExprBinaryOp::Add) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::Subtract) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::BitShiftLeft) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::BitShiftRight) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::Divide, ExprBinaryOp::BitwiseOr) => Ordering::Greater,

      (ExprBinaryOp::Add, ExprBinaryOp::Add) => Ordering::Equal,
      (ExprBinaryOp::Add, ExprBinaryOp::Subtract) => Ordering::Equal,
      (ExprBinaryOp::Add, ExprBinaryOp::BitShiftLeft) => Ordering::Greater,
      (ExprBinaryOp::Add, ExprBinaryOp::BitShiftRight) => Ordering::Greater,
      (ExprBinaryOp::Add, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::Add, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::Add, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::Add, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::Add, ExprBinaryOp::Divide) => Ordering::Less,

      (ExprBinaryOp::Subtract, ExprBinaryOp::Subtract) => Ordering::Equal,
      (ExprBinaryOp::Subtract, ExprBinaryOp::Add) => Ordering::Equal,
      (ExprBinaryOp::Subtract, ExprBinaryOp::BitShiftLeft) => Ordering::Greater,
      (ExprBinaryOp::Subtract, ExprBinaryOp::BitShiftRight) => Ordering::Greater,
      (ExprBinaryOp::Subtract, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::Subtract, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::Subtract, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::Subtract, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::Subtract, ExprBinaryOp::Divide) => Ordering::Less,

      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::BitShiftLeft) => Ordering::Equal,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::BitShiftRight) => Ordering::Equal,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::Divide) => Ordering::Less,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::Add) => Ordering::Less,
      (ExprBinaryOp::BitShiftLeft, ExprBinaryOp::Subtract) => Ordering::Less,


      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::BitShiftRight) => Ordering::Equal,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::BitShiftLeft) => Ordering::Equal,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::BitwiseAnd) => Ordering::Greater,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::Divide) => Ordering::Less,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::Add) => Ordering::Less,
      (ExprBinaryOp::BitShiftRight, ExprBinaryOp::Subtract) => Ordering::Less,

      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::BitwiseAnd) => Ordering::Equal,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::BitwiseXor) => Ordering::Greater,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::Divide) => Ordering::Less,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::Add) => Ordering::Less,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::Subtract) => Ordering::Less,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::BitShiftLeft) => Ordering::Less,
      (ExprBinaryOp::BitwiseAnd, ExprBinaryOp::BitShiftRight) => Ordering::Less,

      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::BitwiseXor) => Ordering::Equal,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::Divide) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::Add) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::Subtract) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::BitShiftLeft) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::BitShiftRight) => Ordering::Less,
      (ExprBinaryOp::BitwiseXor, ExprBinaryOp::BitwiseAnd) => Ordering::Less,

      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::BitwiseOr) => Ordering::Greater,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::Divide) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::Multiply) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::Add) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::Subtract) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::BitShiftLeft) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::BitShiftRight) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::BitwiseAnd) => Ordering::Less,
      (ExprBinaryOp::BitwiseOr, ExprBinaryOp::BitwiseXor) => Ordering::Less,
    }
  }
}


#[derive(Clone)]
pub struct Expr<T: std::fmt::Debug> {
  nodes: Vec<ExprOp<usize, T>>,
  head: usize
}

pub struct ExprView<'a, T: std::fmt::Debug + 'a> {
  nodes: &'a Vec<ExprOp<usize, T>>,
  head: usize
}

impl<T: std::fmt::Debug + std::clone::Clone> Ast<ExprUnaryOp, ExprBinaryOp, ExprTernaryOp, usize, ExprValue<T>> for Expr<T> {
  fn view(&self) -> ExprView<T> {
    ExprView {
      nodes: &self.nodes,
      head: self.head
    }
  }
}

impl<'a, T: std::fmt::Debug + std::clone::Clone> AstView<ExprUnaryOp, ExprBinaryOp, ExprTernaryOp, usize, ExprValue<T>> for ExprView<'a, T> {
  fn root(&self) -> Option<&ExprOp<usize, T>> {
    self.nodes.get(self.head)
  }

  fn subtree(&self, root: &usize) -> ExprView<T> {
    ExprView { nodes: self.nodes, head: *root }
  }
}

impl Expr<String> {
  pub fn new(tokens_stack: &mut Vec<Tokens>) -> Option<Expr<String>> {
    let x_token = tokens_stack.pop()?;
    let x = match &x_token {
      Tokens::IntegerNumber(x) => ExprValue::Literal(*x),
      Tokens::Identifier(variable) => ExprValue::Variable(variable.clone()),
      _ => {
        tokens_stack.push(x_token);
        return None;
      },
    };
    let operator = tokens_stack.pop().and_then(|token| match token {
      Tokens::MultiplySymbol => Some(ExprBinaryOp::Multiply),
      Tokens::DivideSymbol => Some(ExprBinaryOp::Divide),
      Tokens::AddSymbol => Some(ExprBinaryOp::Add),
      Tokens::SubtractSymbol => Some(ExprBinaryOp::Subtract),
      Tokens::BitShiftLeftSymbol => Some(ExprBinaryOp::BitShiftLeft),
      Tokens::BitShiftRightSymbol => Some(ExprBinaryOp::BitShiftRight),
      Tokens::BitwiseAndSymbol => Some(ExprBinaryOp::BitwiseAnd),
      Tokens::BitwiseXorSymbol => Some(ExprBinaryOp::BitwiseXor),
      Tokens::BitwiseOrSymbol => Some(ExprBinaryOp::BitwiseOr),
      tk => {
        tokens_stack.push(tk);
        None
      }
    });
    if let Some((operator, mut result)) = operator.zip(Expr::new(tokens_stack)) {
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
      Some(Expr { nodes: vec![Op::Value(x)], head: 0 })
    }
  }
  pub fn to_typed(self: Self, scope: HashMap<String, String>) -> (Option<Result<Expr<TypedVariable>, String>>, HashMap<String, String>) {
    self.view().apply_with_state(&|op, scope: &mut HashMap<String, String>| {
      match op {
        ExprOpRefs::<Result<Expr<TypedVariable>, String>, String>::Value(val) => {
          let val = match val {
            ExprValue::Literal(i) => ExprValue::Literal(i.clone()),
            ExprValue::Variable(var) => {
              if let Some(t) = scope.get(var) {
                ExprValue::Variable(TypedVariable { name: var.clone(), t: t.clone() })
              } else {
                return Err(String::from(""));
              }
            }
          };
          Ok(Expr { nodes: vec![Op::Value(val)], head: 0 })
        },
        Op::UnaryOp(..) | Op::TernaryOp(..) => {
          panic!();
        },
        Op::BinaryOp(op, fst_result, snd_result) => {
          let mut fst: Expr<TypedVariable> = fst_result.unwrap();
          let mut snd: Expr<TypedVariable> = snd_result.unwrap();
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
