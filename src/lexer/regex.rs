use crate::parser::{Ast, AstView, Op};

#[derive(Debug)]
pub enum RegexErrorType {
  UnmatchedOpenningParenthesis,
  UnmatchedClosingParenthesis,
  UnmatchedOpenningSquareBracket,
  UnmatchedClosingSquareBracket,
  NoCharacterToEscape,
  InvalidInterval
}

#[derive(Debug)]
pub struct RegexError {
  pub error_type: RegexErrorType,
  expression: String,
}

impl RegexError {
  pub fn new(error_type: RegexErrorType, expr: &Vec<char>, start: usize, end: usize) -> RegexError {
    let mut expression = String::new();
    for ch in &expr[..start] {
      expression.push(*ch);
    }
    expression.push_str("\x1b[1;31m");
    for ch in &expr[start..=end] {
      expression.push(*ch);
    }
    expression.push_str("\x1b[0m");
    for ch in &expr[(end + 1)..expr.len()] {
      expression.push(*ch);
    }
    RegexError { error_type, expression }
  }
}


impl From<RegexError> for String {
  fn from(error: RegexError) -> Self {
    match error.error_type {
      RegexErrorType::UnmatchedOpenningParenthesis => {
        format!("Pattern doesn't have a matching ( for )\n\t{}", error.expression)
      },
      RegexErrorType::UnmatchedClosingParenthesis => {
        format!("Pattern doesn't have a matching ) for (\n\t{}", error.expression)
      },
      RegexErrorType::UnmatchedOpenningSquareBracket => {
        format!("Pattern doesn't have a matching ] for [\n\t{}", error.expression)
      },
      RegexErrorType::UnmatchedClosingSquareBracket => {
        format!("Pattern doesn't have a matching [ for ]\n\t{}", error.expression)
      },
      RegexErrorType::NoCharacterToEscape => {
        format!("Pattern doesn't have a character to be escaped by \\\n\n\t{}", error.expression)
      },
      RegexErrorType::InvalidInterval => {
        format!("Interval must be of the form a-b where a <= b\\\n\t{}", error.expression)
      },
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegexUnaryOp {
  KleeneClosure
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegexBinaryOp {
  Or,
  Concat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegexTernaryOp {}


pub type RegexOp<T> = Op<
  RegexUnaryOp,
  RegexBinaryOp,
  RegexTernaryOp,
  T,
  char
>;

pub type RegexOpRefs<'a, 'b, 'c, 'd, T> = Op<
  &'a RegexUnaryOp,
  &'b RegexBinaryOp,
  &'c RegexTernaryOp,
  T,
  &'d char
>;

pub type RegexResult<T> = Result<T, RegexError>;

pub struct RegexAst {
  nodes: Vec<RegexOp<usize>>,
  head: usize
}

impl std::fmt::Debug for RegexAst {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "RegexAst")
  }
}

impl Ast<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, usize, char>
  for RegexAst
{
  fn view(&self) -> RegexAstSubtree {
    RegexAstSubtree {
      nodes: &self.nodes,
      head: self.head
    }
  }
}

pub struct RegexAstSubtree<'a> {
  nodes: &'a Vec<RegexOp<usize>>,
  head: usize
}

impl<'a> AstView<RegexUnaryOp, RegexBinaryOp, RegexTernaryOp, usize, char>
  for RegexAstSubtree<'a>
{
  fn root(&self) -> Option<&RegexOp<usize>> {
    self.nodes.get(self.head)
  }

  fn subtree(&self, root: &usize) -> RegexAstSubtree {
    RegexAstSubtree { nodes: self.nodes, head: *root }
  }
}


impl RegexAst {
  pub fn new(pattern: &str) -> RegexResult<RegexAst> {
    let chars = pattern.chars().collect::<Vec<char>>();
    if chars.is_empty() {
      Ok(RegexAst { nodes: Vec::<RegexOp<usize>>::new(), head: 0 })
    } else {
      Self::parse(&chars, 0, chars.len() - 1)
    }
  }

  fn parse(pattern: &Vec<char>, start: usize, end: usize) -> RegexResult<RegexAst> {
    let mut result = RegexAst { nodes: Vec::<RegexOp<usize>>::new(), head: 0 };
    let mut idx = start;
    while idx <= end {
      if pattern[idx] == '|' {
        return Ok(result.or(Self::parse(pattern, idx + 1, end)?));
      }
      if pattern[idx] == '(' {
        let start_subpattern = idx + 1;
        let mut subpatterns = 1;
        while subpatterns > 0 {
          idx += 1;
          if idx > end {
            return Err(
              RegexError::new(
                RegexErrorType::UnmatchedOpenningParenthesis,
                pattern,
                start_subpattern - 1,
                start_subpattern - 1
                )
              );
          }
          if pattern[idx] == '\\' {
            idx += 1;
            continue;
          }
          if pattern[idx] == '(' {
            subpatterns += 1;
            continue;
          }
          if pattern[idx] == ')' {
            subpatterns -= 1;
          }
        }
        let new = Self::parse(pattern, start_subpattern, idx - 1)?;
        if idx <= end - 1 && pattern[idx + 1] == '*' {
          result = result.concat(new.kleene_closure());
          idx += 2;
        } else {
          result = result.concat(new);
          idx += 1;
        }
        continue;
      }
      if pattern[idx] == '[' {
        let start_options = idx + 1;
        while pattern[idx] != ']' {
          idx += 1;
          if idx > end {
            return Err(
              RegexError::new(
                RegexErrorType::UnmatchedOpenningSquareBracket,
                pattern,
                start_options - 1,
                start_options - 1
                )
              );
          }
          if pattern[idx] == '\\' {
            idx += 1;
            continue;
          }
        }
        let new = Self::parse_options(pattern, start_options, idx - 1)?;
        if idx + 1 <= end && pattern[idx + 1] == '*' {
          result = result.concat(new.kleene_closure());
          idx += 2;
        } else {
          result = result.concat(new);
          idx += 1;
        }
        continue;
      }
      if pattern[idx] == ')' {
        return Err(
          RegexError::new(
            RegexErrorType::UnmatchedClosingParenthesis,
            pattern,
            idx,
            idx
            )
          );
      }
      if  pattern[idx] == ']' {
        return Err(
          RegexError::new(
            RegexErrorType::UnmatchedClosingSquareBracket,
            pattern,
            idx,
            idx
            )
          );
      }
      if pattern[idx] == '\\' {
        if idx + 1 > end {
          return Err(
            RegexError::new(
              RegexErrorType::NoCharacterToEscape,
              pattern,
              end,
              end
              )
            );
        }
        result = result.concat(RegexAst { nodes: vec![RegexOp::Value(pattern[idx + 1])], head: 0 });
        idx += 2;
        continue;
      }
      let mut new = match pattern[idx] {
        '.' => (0u8..=255u8).map(|val| RegexAst { nodes: vec![RegexOp::Value(char::from(val))], head: 0 })
          .fold(RegexAst { nodes: Vec::<RegexOp<usize>>::new(), head: 0 }, |acc, x| acc.or(x)),
        ch => RegexAst { nodes: vec![RegexOp::Value(ch)], head: 0 }
      };
      if idx + 1 <= end && pattern[idx + 1] == '*' {
        new = new.kleene_closure();
        idx += 1;
      } 
      result = result.concat(new);
      idx += 1;
    }
    Ok(result)
  }

  fn parse_options(pattern: &Vec<char>, start: usize, end: usize) -> Result<RegexAst, RegexError> {
    let mut result = RegexAst { nodes: Vec::<RegexOp<usize>>::new(), head: 0 };
    let mut idx = start;
    while idx <= end {
      if pattern[idx] == '\\' {
        result = result.or(RegexAst { nodes: vec![RegexOp::Value(pattern[idx + 1])], head: 0 });
        idx += 2;
        continue;
      }
      if idx + 2 <= end && pattern[idx + 1] == '-' {
        if pattern[idx + 2] != '\\' {
          if pattern[idx + 2] < pattern[idx + 1] {
            return Err(
              RegexError::new(
                RegexErrorType::InvalidInterval,
                pattern,
                idx,
                idx + 2
                )
              );
          }
          result = (pattern[idx]..=pattern[idx + 2])
            .map(|ch| RegexAst { nodes: vec![RegexOp::Value(ch)], head: 0 })
            .fold(result, |acc, x| acc.or(x));
          idx += 3;
          continue;
        } else if idx + 3 <= end {
          if pattern[idx + 3] < pattern[idx + 1] {
            return Err(
              RegexError::new(
                RegexErrorType::InvalidInterval,
                pattern,
                idx,
                idx + 3
                )
              );
          }
          result = (pattern[idx]..=pattern[idx + 3])
            .map(|ch| RegexAst { nodes: vec![RegexOp::Value(ch)], head: 0 })
            .fold(result, |acc, x| acc.or(x));
          idx += 4;
          continue;
        }
      }
      let new = RegexAst { nodes: vec![RegexOp::Value(pattern[idx])], head: 0 };
      result = result.or(new);
      idx += 1;
    }
    Ok(result)
  }

  fn concat(mut self: Self, mut other: RegexAst) -> RegexAst {
    if self.nodes.is_empty() {
      return other
    }
    if other.nodes.is_empty() {
      return self
    }
    let n = self.nodes.len();
    if n > 0 {
      other.nodes = other.nodes.into_iter().map(|x| match x {
        RegexOp::Value(c) => RegexOp::Value(c),
        RegexOp::BinaryOp(op, fst, snd) => RegexOp::BinaryOp(op, fst + n, snd + n),
        RegexOp::UnaryOp(op, idx) => RegexOp::UnaryOp(op, idx + n),
        RegexOp::TernaryOp(op, fst, snd, third) => RegexOp::TernaryOp(op, fst + n, snd + n, third + n)
      }).collect();
      self.nodes.append(&mut other.nodes);
      other.head += n;
      self.nodes.push(RegexOp::BinaryOp(RegexBinaryOp::Concat, self.head, other.head));
      self.head = self.nodes.len() - 1;
    } else {
      self = other;
    }
    self
  }

  fn or(mut self: Self, mut other: RegexAst) -> RegexAst {
    if self.nodes.is_empty() {
      return other
    }
    if other.nodes.is_empty() {
      return self
    }
    let n = self.nodes.len();
    other.nodes = other.nodes.into_iter().map(|x| match x {
      RegexOp::Value(c) => RegexOp::Value(c),
      RegexOp::BinaryOp(op, fst, snd) => RegexOp::BinaryOp(op, fst + n, snd + n),
      RegexOp::UnaryOp(op, idx) => RegexOp::UnaryOp(op, idx + n),
      RegexOp::TernaryOp(op, fst, snd, third) => RegexOp::TernaryOp(op, fst + n, snd + n, third + n)
    }).collect();
    self.nodes.append(&mut other.nodes);
    other.head += n;
    self.nodes.push(RegexOp::BinaryOp(RegexBinaryOp::Or, self.head, other.head));
    self.head = self.nodes.len() - 1;
    self
  }

  fn kleene_closure(mut self: Self) -> RegexAst {
    self.nodes.push(RegexOp::UnaryOp(RegexUnaryOp::KleeneClosure, self.head));
    self.head = self.nodes.len() - 1;
    self
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::boxed::Box;

  pub fn build_matcher(op: RegexOpRefs<Box<dyn Fn(&str) -> (bool, &str)>>) -> Box<dyn Fn(&str) -> (bool, &str)> {
    match op {
      RegexOpRefs::Value(c) => {
        let c = c.clone();
        std::boxed::Box::new(move |s: &str| {
          match s.chars().last().is_some_and(|ch| ch == c) {
            true => (true, &s[..(s.len() - 1)]),
            false => (false, s)
          }
        })
      },
      RegexOpRefs::UnaryOp(RegexUnaryOp::KleeneClosure, match_operand) => {
        std::boxed::Box::new(move |s: &str| {
          let (mut matched, mut current) = match_operand(s);
          while matched {
            (matched, current) = match_operand(current);
          }
          (true, current)
        })
      },
      RegexOpRefs::BinaryOp(RegexBinaryOp::Or, fst, snd) => {
        std::boxed::Box::new(move |s: &str| {
          let (matched, state) = snd(s);
          match matched {
            true => (matched, state),
            false => fst(state)
          }
        })
      },
      RegexOpRefs::BinaryOp(RegexBinaryOp::Concat, fst, snd) => {
        std::boxed::Box::new(move |s: &str| {
          let (matched, state) = snd(s);
          match matched {
            true => fst(state),
            false => (false, s)
          }
        })
      },
      RegexOpRefs::TernaryOp(..) => { panic!(); }
    }
  }

  #[test]
  fn properly_matches_strings() -> Result<(), RegexError> {
    let regex_match = RegexAst::new("((hello)|(ab(cd)*))cd.cdef[a-d]")?.view().apply(&build_matcher).unwrap();
    let should_pass = [
      "hellocd'cdefa",
      "hellocd\"cdefb",
      "hellocd/cdefc",
      "hellocd|cdefd",
      "abcd=cdefa",
      "abcd-cdefb",
      "abcd+cdefc",
      "abcd]cdefd",
      "abcdcd[cdefa",
      "abcdcd(cdefb",
      "abcdcd)cdefc",
      "abcdcd!cdefd",
      "abcdcdcd@cdefa",
      "abcdcdcd#cdefb",
      "abcdcdcd$cdefc",
      "abcdcdcd%cdefd",
      "abcdcdcdcd&cdefa",
      "abcdcdcdcd cdefb",
      "abcdcdcdcd2cdefc",
      "abcdcdcdcd8cdefd",
      "abcdcdcdkcdefa",
      "abcdcdcdhcdefb",
      "abcdcdcdmcdefc",
      "abcdcdcdhcdefd",
      "abcdcdcdcd8cdefa",
      "abcdcdcdcd\ncdefb",
      "abcdcdcdcd\ncdefc",
      "abcdcdcdcd\ncdefd",
      ];
    let shouldnt_pass = [
      "helfhdkasllocdcdef",
      "abcdcdfhdkfdsklhkl\\asef",
      "ab cdcd cd .odfahifan ef",
      "af",
      "",
    ];
    for case in should_pass {
      let (matched, _) = regex_match(case);
      if !matched {
        println!("{}", case);
      }
      assert!(matched);
    }
    for case in shouldnt_pass {
      let (matched, _) = regex_match(case);
      if matched {
        println!("{}", case);
      }
      assert!(!matched);
    }
    Ok(())
  }

  #[test]
  fn returns_none_for_apply_on_empty_regex() -> Result<(), RegexError> {
    let result = RegexAst::new("")?.view().apply(&build_matcher);
    assert!(result.is_none());
    Ok(())
  }

  #[test]
  fn returns_error_for_non_closed_parenthesis() {
    let result = RegexAst::new("((hello)|(ab(cd)*)cdcdef[a-d]");
    assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedOpenningParenthesis)));
  }

  #[test]
  fn returns_error_for_non_closed_square_bracket() {
    let result = RegexAst::new("((hello)|(ab(cd)*))cdcdef[a-d");
    assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedOpenningSquareBracket)));
  }

  #[test]
  fn returns_error_for_non_opened_parenthesis() {
    let result = RegexAst::new("((hello))|(ab(cd)*))cdcdef[a-d]");
    assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedClosingParenthesis)));
  }

  #[test]
  fn returns_error_for_non_opened_square_bracket() {
    let result = RegexAst::new("((hello)|(ab(cd)*))cdcdef[a-d]]");
    assert!(result.is_err_and(|err| matches!(err.error_type, RegexErrorType::UnmatchedClosingSquareBracket)));
  }
}
