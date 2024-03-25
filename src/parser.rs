use std::collections::HashSet;

pub struct OpDrawingDescriptor {
    pub indentation: usize,
    pub vertical_lines: HashSet<usize>,
    pub has_operands: bool,
    pub is_last_child: bool,
    pub name: String
}

pub trait AstDrawable {
    fn draw(self: &Self) -> Vec<OpDrawingDescriptor>;
}

#[derive(Debug, Clone)]
pub enum Op<T, U, V, W, Y> {
    UnaryOp(T, W),
    BinaryOp(U, W, W),
    TernaryOp(V, W, W, W),
    Value(Y)
}

pub trait AstView<'a, T: std::fmt::Debug, U: std::fmt::Debug, V: std::fmt::Debug, Y: AstDrawable> {
    fn apply<W, F: Fn(Op<T, U, V, W, Y>) -> W>(self: Self, f: &F) -> Option<W>;

    fn apply_with_state<W, Z, F: Fn(Op<T, U, V, W, Y>, Z) -> (W, Z)>(self: Self, f: &F, s0: Z) -> (Option<W>, Z);
}

pub trait Ast<T: std::fmt::Debug, U: std::fmt::Debug, V: std::fmt::Debug, W: std::fmt::Debug, Y: AstDrawable> : AstDrawable {
    fn root(&self) -> impl AstView<T, U, V, Y>;

    fn draw_tree(&self) -> Vec<OpDrawingDescriptor> {
        let to_str = |node| {
            match node {
                Op::<T, U, V, Vec<OpDrawingDescriptor>, Y>::Value(val) => {
                    val.draw()
                },
                Op::<T, U, V, Vec<OpDrawingDescriptor>, Y>::UnaryOp(op, mut descriptors) => {
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
                Op::<T, U, V, Vec<OpDrawingDescriptor>, Y>::BinaryOp(op, mut fst_descriptors, mut snd_descriptors) => {
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
                Op::<T, U, V, Vec<OpDrawingDescriptor>, Y>::TernaryOp(op, mut fst_descriptors, mut snd_descriptors, mut third_descriptors) => {
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
        };
        self.root().apply(&to_str).unwrap()
    }

    fn to_drawn_string(&self) -> String {
        let vals = self.draw().into_iter().rev().collect::<Vec<OpDrawingDescriptor>>();
        let max_val = vals.iter().map(|desc| desc.indentation).fold(0, std::cmp::max);
        vals.into_iter().map(|desc| {
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
    }
}
