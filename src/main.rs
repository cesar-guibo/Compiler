use std::collections::HashMap;

mod lexer;
mod parser;
mod tokens;
mod expressions;
mod instructions;

use tokens::{LanguageTokenizer, Tokens};
//use expressions::Expression;
use parser::{Ast, AstView, Op};
use expressions::{Value, BinaryOp};
use instructions::{Instruction, UnaryInstruction, BinaryInstruction, TernaryInstruction, InstructionValue};


fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let tokenizer = LanguageTokenizer::new().unwrap();
    if args.len() < 2 {
        println!("Missing filename in the command line args");
        return;
    }
    let contents = std::fs::read_to_string(&args[1]).expect("Failed to open file");
    let mut tokens: Vec<Tokens> = tokenizer.to_tokens(contents).map(|tk| tk.unwrap()).collect::<Vec<Tokens>>().into_iter().rev().collect();
    let mut global_scope = HashMap::<String, String>::new();
    let mut linear_representation = None;
    while let Some(instruction) = Instruction::new(&mut tokens) {
        println!("{}", &instruction);
        (linear_representation, global_scope) = instruction.root().apply_with_state(&|op: Op<UnaryInstruction, BinaryInstruction, TernaryInstruction, String, InstructionValue>, mut scope: HashMap<String, String>| {
            match op {
                Op::BinaryOp(BinaryInstruction::Declare, t, variable) => {
                    scope.insert(variable.clone(), t.clone());
                    (String::new(), scope)
                },
                Op::TernaryOp(TernaryInstruction::DeclareAndAssign, t, variable, mut expr) => {
                    scope.insert(variable.clone(), t.clone());
                    expr.push_str(format!("\nstore {}, v0", variable).as_str());
                    (expr, scope)
                },
                Op::Value(val) => {
                    let (res, scope) = match val {
                        InstructionValue::Type(t) => (t, scope),
                        InstructionValue::Identifier(var) => (var, scope),
                        InstructionValue::Expression(exp) => {
                            let auxs = std::rc::Rc::new(std::cell::RefCell::new((0..20).rev().collect::<Vec<usize>>()));
                            let (typed_res, scope) = exp.clone().to_typed(scope);
                            let typed = typed_res.unwrap().unwrap();
                            let (_, insts) = typed.root().apply(&|op| {
                                match op {
                                    Op::Value(val) => {
                                        let to_use = auxs.borrow_mut().pop().unwrap();
                                        match val {
                                            Value::Literal(i) => (to_use, vec![format!("load (v{}, int), ({}, int)", to_use, i)]),
                                            Value::Variable(v) => (to_use, vec![format!("load (v{}, int), ({}, {})", to_use, v.name, v.t)])
                                        }
                                    },
                                    Op::BinaryOp(op, (fst_var, mut fst_instructs), (snd_var, mut snd_instructs)) => {
                                        let op_name = match op {
                                            BinaryOp::Add => "add",
                                            BinaryOp::Subtract => "sub",
                                            BinaryOp::Multiply => "mul",
                                            BinaryOp::Divide => "div",
                                            BinaryOp::BitShiftLeft => "shl",
                                            BinaryOp::BitShiftRight => "shr",
                                            BinaryOp::BinaryAnd => "and",
                                            BinaryOp::BinaryXor => "xor",
                                            BinaryOp::BinaryOr => "or"
                                        };
                                        fst_instructs.append(&mut snd_instructs);
                                        fst_instructs.push(format!("{} (v{}, int), (v{}, int)", op_name, fst_var, snd_var));
                                        auxs.borrow_mut().push(snd_var);
                                        (fst_var, fst_instructs)
                                    }
                                    _ => { panic!(); }
                                }
                            }).unwrap();
                            (format!("{}", insts.join("\n")), scope)
                        }
                    };
                    (res, scope)
                }
                _ => (String::new(), scope)
            }
        }, global_scope);
        println!("{}", linear_representation.unwrap());
    }
}
