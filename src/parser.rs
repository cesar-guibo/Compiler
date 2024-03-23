use std::collections::HashSet;

#[derive(Debug)]
pub enum Op<T, U, V, W> {
    UnaryOp(T, V),
    BinaryOp(U, V, V),
    Value(W)
}

pub trait AstView<'a, T: std::fmt::Debug, U: std::fmt::Debug, W: std::fmt::Debug> {
    fn apply<V, F: Fn(Op<T, U, V, W>) -> V>(self: Self, f: &F) -> Option<V>;
}

pub trait Ast<T: std::fmt::Debug, U: std::fmt::Debug, V: std::fmt::Debug, W: std::fmt::Debug> : std::fmt::Debug {
    fn root(self: &Self) -> impl AstView<T, U, W>;

    fn draw(self: &Self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let to_str = |node| {
            match node {
                Op::<T, U, Vec<(usize, HashSet<usize>, bool, bool, String)>, W>::Value(val) => {
                    vec![(0, HashSet::new(), false, true, format!("{:?}", val))]
                },
                Op::<T, U, Vec<(usize, HashSet<usize>, bool, bool, String)>, W>::UnaryOp(op, mut operand) => {
                    let end = operand.len() - 1;
                    operand[end].3 = false;
                    operand.push((operand[end].0 + 1, operand[end].1.clone(), true, true, format!("{:?}", op)));
                    operand
                },
                Op::<T, U, Vec<(usize, HashSet<usize>, bool, bool, String)>, W>::BinaryOp(op, mut fst_operand, mut snd_operand) => {
                    let n1 = fst_operand.len();
                    let n2 = snd_operand.len();
                    if snd_operand[n2 - 1].0 < fst_operand[n1 - 1].0 {
                        let diff = fst_operand[n1 - 1].0 - snd_operand[n2 - 1].0;
                        for (t, vert, _, _, _) in snd_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    } else {
                        let diff = snd_operand[n2 - 1].0 - fst_operand[n1 - 1].0;
                        for (t, vert, _, _, _) in fst_operand.iter_mut() {
                            *t += diff;
                            *vert = vert.iter().map(|v| v + diff).collect();
                        }
                    }
                    fst_operand[n1 - 1].3 = false;
                    let max = fst_operand[n1 - 1].0;
                    for (_, vert, _, _, _) in snd_operand.iter_mut() {
                        vert.insert(max);
                    }
                    fst_operand.append(&mut snd_operand);
                    let end = fst_operand.len() - 1;
                    fst_operand.push((fst_operand[end].0 +  1, HashSet::new(), true, true, format!("{:?}", op)));
                    fst_operand
                },
            }
        };
        let vals = self.root().apply(&to_str).unwrap().into_iter().rev().collect::<Vec<(usize, HashSet<usize>, bool, bool, String)>>();
        let max_val = vals.iter().map(|(i, _, _, _, _)| *i).fold(0, std::cmp::max);
        let str = vals.into_iter().map(|(i, verts, has_operands, middle, s)| {
            let mut spacing = String::new();
            for idx in 0..(max_val - i) {
                if verts.contains(&(max_val - idx)) {
                    spacing.push_str("\u{2503}   ");
                    continue;
                }
                spacing.push_str("    ");
            }
            std::iter::repeat("  ".to_string()).take(max_val - i).collect::<Vec<String>>().join("");
            match (has_operands, middle) {
                (true, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, s),
                (true, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2533}\u{2501} {}", spacing, s),
                (false, true) => format!("{}\u{2523}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, s),
                (false, false) => format!("{}\u{2517}\u{2501}\u{2501}\u{2501}\u{2501}\u{2501} {}", spacing, s)
            }
        }).collect::<Vec<String>>().join("\r\n");
        write!(f, "{}", str)
    }
}
