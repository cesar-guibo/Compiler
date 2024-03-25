use crate::expressions::{Expression, TypedVariable};
use std::collections::HashSet;
use crate::tokens::Tokens;
use crate::parser::{Op, OpDrawingDescriptor, Ast, AstView, AstDrawable};

#[derive(Debug, Clone, Copy)]
pub enum UnaryInstruction {
    Return
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryInstruction {
    Declare,
    Assign,
}

#[derive(Debug, Clone, Copy)]
pub enum TernaryInstruction {
    DeclareAndAssign
}

#[derive(Debug, Clone)]
pub enum InstructionValue {
    Expression(Expression<String>),
    Type(String),
    Identifier(String)
}


pub struct Instruction {
    nodes: Vec<Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue>>,
    head: usize
}

pub struct InstructionView<'a> {
    nodes: &'a Vec<Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue>>,
    head: usize
}

impl std::fmt::Debug for Instruction {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Instruction")
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.to_drawn_string())
    }
}

impl AstDrawable for InstructionValue  {
    fn draw(&self) -> Vec<OpDrawingDescriptor> {
        match self {
            InstructionValue::Expression(exp) => exp.draw(),
            InstructionValue::Type(s) => {
                let desc = OpDrawingDescriptor {
                    indentation: 0,
                    vertical_lines: HashSet::<usize>::new(),
                    has_operands: false,
                    is_last_child: false,
                    name: format!("{}", s)
                };
                vec![desc]
            },
            InstructionValue::Identifier(s) => {
                let desc = OpDrawingDescriptor {
                    indentation: 0,
                    vertical_lines: HashSet::<usize>::new(),
                    has_operands: false,
                    is_last_child: false,
                    name: format!("{}", s)
                };
                vec![desc]
            },
        }
    }
}

impl AstDrawable for Instruction {
    fn draw(&self) -> Vec<OpDrawingDescriptor> {
        self.draw_tree()
    }
}

impl Ast<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue> for Instruction {
    fn root(self: &Self) -> InstructionView {
        InstructionView {
            nodes: &self.nodes,
            head: self.head
        }
    }
}

impl<'a> AstView<'a, UnaryInstruction, BinaryInstruction, TernaryInstruction, InstructionValue> for InstructionView<'a> {
    // Post order
    fn apply<T, F: Fn(Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, T, InstructionValue>) -> T>(self: Self, f: &F) -> Option<T> {
        match self.nodes.get(self.head)? {
            Op::Value(c) => Some(f(Op::Value(c.clone()))),
            Op::UnaryOp(op, operand_idx) => {
                let subtree = InstructionView { nodes: self.nodes, head: *operand_idx };
                let operand = subtree.apply(f)?;
                Some(f(Op::UnaryOp(*op, operand)))
            },
            Op::BinaryOp(op, fst, snd) => {
                let fst_subtree = InstructionView { nodes: self.nodes, head: *fst };
                let fst_operand = fst_subtree.apply(f)?;
                let snd_subtree = InstructionView { nodes: self.nodes, head: *snd };
                let snd_operand = snd_subtree.apply(f)?;
                Some(f(Op::BinaryOp(*op, fst_operand, snd_operand)))
            },
            Op::TernaryOp(op, fst, snd, third) => {
                let fst_subtree = InstructionView { nodes: self.nodes, head: *fst };
                let fst_operand = fst_subtree.apply(f)?;
                let snd_subtree = InstructionView { nodes: self.nodes, head: *snd };
                let snd_operand = snd_subtree.apply(f)?;
                let third_subtree = InstructionView { nodes: self.nodes, head: *third };
                let third_operand = third_subtree.apply(f)?;
                Some(f(Op::TernaryOp(*op, fst_operand, snd_operand, third_operand)))
            }
        }
    }

    fn apply_with_state<U, V, F: Fn(Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, U, InstructionValue>, V) -> (U, V)>(self: Self, f: &F, s0: V) -> (Option<U>, V) {
        if let Some(op) = self.nodes.get(self.head) {
            let (val, state) = match op {
                Op::Value(c) => f(Op::Value(c.clone()), s0),
                Op::UnaryOp(op, operand_idx) => {
                    let subtree = InstructionView { nodes: self.nodes, head: *operand_idx };
                    let (operand_res, state) = subtree.apply_with_state(f, s0);
                    if let Some(operand) = operand_res {
                        f(Op::UnaryOp(*op, operand), state)
                    } else {
                        return (None, state);
                    }
                },
                Op::BinaryOp(binary_op, fst, snd) => {
                    let fst_subtree = InstructionView { nodes: self.nodes, head: *fst };
                    let (fst_operand, fst_state) = fst_subtree.apply_with_state(f, s0);
                    let snd_subtree = InstructionView { nodes: self.nodes, head: *snd };
                    let (snd_operand, snd_state) = snd_subtree.apply_with_state(f, fst_state);
                    if let Some((fst, snd)) = fst_operand.zip(snd_operand) {
                        f(Op::BinaryOp(*binary_op, fst, snd), snd_state)
                    } else {
                        return (None, snd_state);
                    }
                },
                Op::TernaryOp(op, fst, snd, third) => {
                    let fst_subtree = InstructionView { nodes: self.nodes, head: *fst };
                    let (fst_operand, fst_state) = fst_subtree.apply_with_state(f, s0);
                    let snd_subtree = InstructionView { nodes: self.nodes, head: *snd };
                    let (snd_operand, snd_state) = snd_subtree.apply_with_state(f, fst_state);
                    let third_subtree = InstructionView { nodes: self.nodes, head: *third };
                    let (third_operand, third_state) = third_subtree.apply_with_state(f, snd_state);
                    if let Some(((fst, snd), third)) = fst_operand.zip(snd_operand).zip(third_operand) {
                        f(Op::TernaryOp(*op, fst, snd, third), third_state)
                    } else {
                        return (None, third_state);
                    }
                }
            };
            (Some(val), state)
        } else {
            (None, s0)
        }
    }
}

impl Instruction {
    pub fn new(tokens_stack: &mut Vec<Tokens>) -> Option<Instruction> {
        let current = tokens_stack.pop()?;
        match &current {
            Tokens::Identifier(variable) => {
                match tokens_stack.pop().unwrap() {
                    Tokens::AssignSymbol => {
                        if let Some(mut snd) = Instruction::new(tokens_stack) {
                            let fst_idx = snd.nodes.len();
                            snd.nodes.push(Op::Value(InstructionValue::Identifier(variable.clone())));
                            let new_head = snd.nodes.len();
                            snd.nodes.push(Op::BinaryOp(BinaryInstruction::Assign, fst_idx, snd.head));
                            snd.head = new_head;
                            Some(snd)
                        } else {
                            let aux = Expression::new(tokens_stack).unwrap();
                            println!("{}", &aux);
                            let instruction = Instruction {
                                nodes: vec![
                                    Op::Value(InstructionValue::Identifier(variable.clone())),
                                    Op::Value(InstructionValue::Expression(aux)),
                                    Op::BinaryOp(BinaryInstruction::Assign, 0, 1)
                                ],
                                head: 2
                            };
                            match tokens_stack.pop()? {
                                Tokens::SemiColon => {
                                    Some(instruction)
                                },
                                val => {
                                    tokens_stack.push(val);
                                    None
                                }
                            }
                        }
                    }, 
                    val => {
                        tokens_stack.push(val);
                        let instruction = Instruction {
                            nodes: vec![
                                Op::Value(InstructionValue::Expression(Expression::new(tokens_stack).unwrap())),
                            ],
                            head: 0
                        };
                        match tokens_stack.pop()? {
                            Tokens::SemiColon => {
                                Some(instruction)
                            },
                            val => {
                                tokens_stack.push(val);
                                None
                            }
                        }
                    }
                }
            },
            Tokens::Type(t) => {
                match tokens_stack.pop()? {
                    Tokens::Identifier(variable) => {
                        match tokens_stack.pop()? {
                            Tokens::AssignSymbol => {
                                if let Some(mut third) = Instruction::new(tokens_stack) {
                                    let fst_idx = third.nodes.len();
                                    third.nodes.push(Op::Value(InstructionValue::Type(t.clone())));
                                    let snd_idx = third.nodes.len();
                                    third.nodes.push(Op::Value(InstructionValue::Identifier(variable.clone())));
                                    let new_head = third.nodes.len();
                                    third.nodes.push(Op::TernaryOp(TernaryInstruction::DeclareAndAssign, fst_idx, snd_idx, third.head));
                                    third.head = new_head;
                                    Some(third)
                                } else {
                                    let aux = Expression::new(tokens_stack).unwrap();
                                    let instruction = Instruction {
                                        nodes: vec![
                                            Op::Value(InstructionValue::Type(t.clone())),
                                            Op::Value(InstructionValue::Identifier(variable)),
                                            Op::Value(InstructionValue::Expression(aux)),
                                            Op::TernaryOp(TernaryInstruction::DeclareAndAssign, 0, 1, 2)
                                        ],
                                        head: 3
                                    };
                                    match tokens_stack.pop()? {
                                        Tokens::SemiColon => {
                                            Some(instruction)
                                        },
                                        val => {
                                            tokens_stack.push(val);
                                            None
                                        }
                                    }
                                }
                            }, 
                            Tokens::SemiColon => {
                                Some(Instruction {
                                    nodes: vec![
                                        Op::Value(InstructionValue::Type(t.clone())),
                                        Op::Value(InstructionValue::Identifier(variable)),
                                        Op::BinaryOp(BinaryInstruction::Declare, 0, 1)
                                    ],
                                    head: 2
                                })
                            }
                            val => {
                                tokens_stack.push(val);
                                tokens_stack.push(Tokens::Identifier(variable));
                                tokens_stack.push(current);
                                None
                            }
                        }
                    },
                    val => {
                        tokens_stack.push(val);
                        tokens_stack.push(current);
                        None
                    }
                }
            },
            Tokens::Return => {
                let instruction = Instruction {
                    nodes: vec![
                        Op::Value(InstructionValue::Expression(Expression::new(tokens_stack)?)),
                        Op::UnaryOp(UnaryInstruction::Return, 0)
                    ],
                    head: 1
                };
                match tokens_stack.pop()? {
                    Tokens::SemiColon => {
                        Some(instruction)
                    },
                    _ => None
                }
            }
            Tokens::SemiColon => {
                None
            }
            _ => {
                tokens_stack.push(current);
                None
            }
        }
    }
}
