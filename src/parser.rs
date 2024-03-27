use std::collections::HashSet;

pub struct OpDrawingDescriptor {
    pub indentation: usize,
    pub vertical_lines: HashSet<usize>,
    pub has_operands: bool,
    pub is_last_child: bool,
    pub name: String
}

#[derive(Debug, Clone)]
pub enum Op<T, U, V, W, Y> {
    UnaryOp(T, W),
    BinaryOp(U, W, W),
    TernaryOp(V, W, W, W),
    Value(Y)
}

impl<T: std::fmt::Debug, U:std::fmt::Debug, V: std::fmt::Debug, Y: std::fmt::Debug> Op<&T, &U, &V, Vec<OpDrawingDescriptor>, &Y> {
    fn to_descriptors(op: Op<&T, &U, &V, Vec<OpDrawingDescriptor>, &Y>) -> Vec<OpDrawingDescriptor> {
        match op {
            Op::Value(val) => {
                let desc = OpDrawingDescriptor {
                    indentation: 0,
                    vertical_lines: HashSet::<usize>::new(),
                    has_operands: false,
                    is_last_child: false,
                    name: format!("{:?}", val)
                };
                vec![desc]
            },
            Op::UnaryOp(op, mut descriptors) => {
                let end = descriptors.len() - 1;
                descriptors[end].is_last_child = true;
                let new_descriptor = OpDrawingDescriptor {
                    indentation: descriptors[end].indentation + 1,
                    vertical_lines: descriptors[end].vertical_lines.clone(),
                    has_operands: true,
                    is_last_child: true,
                    name: format!("{:?}", op)
                };
                descriptors.push(new_descriptor);
                descriptors
            },
            Op::BinaryOp(op, mut fst_descriptors, mut snd_descriptors) => {
                let n1 = fst_descriptors.len();
                let n2 = snd_descriptors.len();
                if snd_descriptors[n2 - 1].indentation < fst_descriptors[n1 - 1].indentation {
                    let diff = fst_descriptors[n1 - 1].indentation - snd_descriptors[n2 - 1].indentation;
                    for descriptor in snd_descriptors.iter_mut() {
                        descriptor.indentation += diff;
                        descriptor.vertical_lines = descriptor.vertical_lines.iter().map(|v| v + diff).collect();
                    }
                } else {
                    let diff = snd_descriptors[n2 - 1].indentation - fst_descriptors[n1 - 1].indentation;
                    for descriptor in fst_descriptors.iter_mut() {
                        descriptor.indentation += diff;
                        descriptor.vertical_lines = descriptor.vertical_lines.iter().map(|v| v + diff).collect();
                    }
                }
                snd_descriptors[n2 - 1].is_last_child = true;
                let max = snd_descriptors[n2 - 1].indentation;
                for descriptor in fst_descriptors.iter_mut() {
                    descriptor.vertical_lines.insert(max);
                }
                snd_descriptors.append(&mut fst_descriptors);
                let end = snd_descriptors.len() - 1;
                let new_descriptor = OpDrawingDescriptor {
                    indentation: snd_descriptors[end].indentation + 1,
                    vertical_lines: HashSet::new(),
                    has_operands: true,
                    is_last_child: false,
                    name: format!("{:?}", op)
                };
                snd_descriptors.push(new_descriptor);
                snd_descriptors
            },
            Op::TernaryOp(op, mut fst_descriptors, mut snd_descriptors, mut third_descriptors) => {
                let n1 = fst_descriptors.len();
                let n2 = snd_descriptors.len();
                let n3 = third_descriptors.len();
                
                let max_spaces = [
                    fst_descriptors[n1 - 1].indentation,
                    snd_descriptors[n2 - 1].indentation,
                    third_descriptors[n3 - 1].indentation
                ].into_iter().fold(0, std::cmp::max);
                let diff1 = max_spaces - fst_descriptors[n1 - 1].indentation;
                let diff2 = max_spaces - snd_descriptors[n2 - 1].indentation;
                let diff3 = max_spaces - third_descriptors[n3 - 1].indentation;

                for descriptor in fst_descriptors.iter_mut() {
                    descriptor.indentation += diff1;
                    descriptor.vertical_lines = descriptor.vertical_lines.iter().map(|v| v + diff1).collect();
                }
                for descriptor in snd_descriptors.iter_mut() {
                    descriptor.indentation += diff2;
                    descriptor.vertical_lines = descriptor.vertical_lines.iter().map(|v| v + diff2).collect();
                }
                for descriptor in third_descriptors.iter_mut() {
                    descriptor.indentation += diff3;
                    descriptor.vertical_lines = descriptor.vertical_lines.iter().map(|v| v + diff3).collect();
                }

                third_descriptors[n3 - 1].is_last_child = true;
                let max = third_descriptors[n3 - 1].indentation;
                for descriptor in fst_descriptors.iter_mut() {
                    descriptor.vertical_lines.insert(max);
                }
                for descriptor in snd_descriptors.iter_mut() {
                    descriptor.vertical_lines.insert(max);
                }
                third_descriptors.append(&mut snd_descriptors);
                third_descriptors.append(&mut fst_descriptors);
                let end = third_descriptors.len() - 1;
                let new_descriptor = OpDrawingDescriptor {
                    indentation: third_descriptors[end].indentation + 1,
                    vertical_lines: HashSet::new(),
                    has_operands: true,
                    is_last_child: false,
                    name: format!("{:?}", op)
                };
                third_descriptors.push(new_descriptor);
                third_descriptors
            },
        }
    }
}

pub trait AstView<T: std::fmt::Debug, U: std::fmt::Debug, V: std::fmt::Debug, W: std::fmt::Debug, X: std::fmt::Debug> : Sized {
    fn subtree(&self, root: &W) -> impl AstView<T, U, V, W, X>;
    
    fn root(&self) -> Option<&Op<T, U, V, W, X>>;

    fn apply<Y, F: Fn(Op<&T, &U, &V, Y, &X>) -> Y>(&self, f: &F) -> Option<Y> {
        let res = match self.root()? {
            Op::Value(val) => f(Op::Value(val)),
            Op::UnaryOp(op, fst) => {
                let res1 = self.subtree(fst).apply(f)?;
                f(Op::UnaryOp(op, res1))
            },
            Op::BinaryOp(op, fst, snd) => {
                let res1 = self.subtree(fst).apply(f)?;
                let res2 = self.subtree(snd).apply(f)?;
                f(Op::BinaryOp(op, res1, res2))
            },
            Op::TernaryOp(op, fst, snd, trd) => {
                let res1 = self.subtree(fst).apply(f)?;
                let res2 = self.subtree(snd).apply(f)?;
                let res3 = self.subtree(trd).apply(f)?;
                f(Op::TernaryOp(op, res1, res2, res3))
            }
        };
        Some(res)
    }

    fn apply_with_state<Y, Z, F: Fn(Op<&T, &U, &V, Y, &X>, &mut Z) -> Y>(&self, f: &F, mut s0: Z) -> (Option<Y>, Z) {
        match self.root() {
            Some(Op::Value(val)) => (Some(f(Op::Value(val), &mut s0)), s0),
            Some(Op::UnaryOp(op, fst)) => {
                let (res1, mut s1) = self.subtree(fst).apply_with_state(f, s0);
                (res1.map(|res| (f(Op::UnaryOp(op, res), &mut s1))), s1)
            },
            Some(Op::BinaryOp(op, fst, snd)) => {
                let (res1, s1) = self.subtree(fst).apply_with_state(f, s0);
                let (res2, mut s2) = self.subtree(snd).apply_with_state(f, s1);
                (res1.zip(res2).map(|(r1, r2)| (f(Op::BinaryOp(op, r1, r2), &mut s2))), s2)
            },
            Some(Op::TernaryOp(op, fst, snd, trd)) => {
                let (res1, s1) = self.subtree(fst).apply_with_state(f, s0);
                let (res2, s2) = self.subtree(snd).apply_with_state(f, s1);
                let (res3, mut s3) = self.subtree(trd).apply_with_state(f, s2);
                (res1.zip(res2).zip(res3).map(|((r1, r2), r3)| (f(Op::TernaryOp(op, r1, r2, r3), &mut s3))), s3)
            },
            None => (None, s0)
        }
    }
}

pub trait Ast<T: std::fmt::Debug, U: std::fmt::Debug, V: std::fmt::Debug, W: std::fmt::Debug, Y: std::fmt::Debug> {
    fn view(&self) -> impl AstView<T, U, V, W, Y>;

    fn draw(&self) -> String {
        if let Some(descriptors) = self.view().apply(&Op::to_descriptors).map(|desc| desc.into_iter().rev().collect::<Vec<OpDrawingDescriptor>>()) {
            let max_val = descriptors.iter().map(|desc| desc.indentation).fold(0, std::cmp::max);
            descriptors.into_iter().map(|desc| {
                let mut spacing = String::new();
                for idx in 0..(max_val - desc.indentation) {
                    if desc.vertical_lines.contains(&(max_val - idx)) {
                        spacing.push_str("\u{2503}   ");
                        continue;
                    }
                    spacing.push_str("    ");
                }
                std::iter::repeat("  ".to_string()).take(max_val - desc.indentation).collect::<Vec<String>>().join("");
                match (desc.has_operands, !desc.is_last_child) {
                    (true, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, desc.name),
                    (true, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, desc.name),
                    (false, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, desc.name),
                    (false, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, desc.name)
                }
            }).collect::<Vec<String>>().join("\r\n")
        } else {
            String::new()
        }
    }
}
