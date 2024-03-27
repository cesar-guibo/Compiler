use crate::expressions::{Expression, TypedVariable};
use std::collections::HashSet;
use crate::tokens::Tokens;
use crate::parser::{Op, Ast, AstView};

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

impl Ast<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue> for Instruction {
    fn view(&self) -> InstructionView {
        InstructionView {
            nodes: &self.nodes,
            head: self.head
        }
    }
}

impl<'a> AstView<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue> for InstructionView<'a> {
    fn root(&self) -> Option<&Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, usize, InstructionValue>> {
        self.nodes.get(self.head)
    }

    fn subtree(&self, root: &usize) -> InstructionView {
        InstructionView { nodes: self.nodes, head: *root }
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
