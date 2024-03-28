use std::rc::Rc;

use crate::lexer::{Lexer, LazyLexer, TokenIter};
use crate::lexer::regex::RegexAst;

#[derive(Debug)]
pub enum Tokens {
  Type(String),
  Identifier(String),
  IntegerNumber(i32),
  AssignSymbol,
  AddSymbol,
  SubtractSymbol,
  MultiplySymbol,
  DivideSymbol,
  BitwiseOrSymbol,
  BitwiseAndSymbol,
  BitwiseXorSymbol,
  BitShiftLeftSymbol,
  BitShiftRightSymbol,
  Return,
  SemiColon
}

pub struct LanguageTokenizer {
  lexer: Lexer<Tokens>
}

impl LanguageTokenizer {
  pub fn new() -> Result<LanguageTokenizer, String> {
    let result = LanguageTokenizer {
      lexer: LazyLexer::new(RegexAst::new("[0-9][0-9]*")?, Rc::new(|s| Tokens::IntegerNumber(i32::from_str_radix(&s, 10).unwrap())))
        .or(LazyLexer::new(RegexAst::new("[a-zA-Z_][a-zA-Z0-9_]*")?, Rc::new(|s| {
          match s.as_str() {
            "int" => Tokens::Type(s),
            "return" => Tokens::Return,
            _ => Tokens::Identifier(s)
          }
        })))
      .or(LazyLexer::new(RegexAst::new("=")?, Rc::new(|_| Tokens::AssignSymbol)))
        .or(LazyLexer::new(RegexAst::new("+")?, Rc::new(|_| Tokens::AddSymbol)))
        .or(LazyLexer::new(RegexAst::new("-")?, Rc::new(|_| Tokens::SubtractSymbol)))
        .or(LazyLexer::new(RegexAst::new("\\*")?, Rc::new(|_| Tokens::MultiplySymbol)))
        .or(LazyLexer::new(RegexAst::new("/")?, Rc::new(|_| Tokens::DivideSymbol)))
        .or(LazyLexer::new(RegexAst::new("\\|")?, Rc::new(|_| Tokens::BitwiseOrSymbol)))
        .or(LazyLexer::new(RegexAst::new("&")?, Rc::new(|_| Tokens::BitwiseAndSymbol)))
        .or(LazyLexer::new(RegexAst::new("^")?, Rc::new(|_| Tokens::BitwiseXorSymbol)))
        .or(LazyLexer::new(RegexAst::new("<<")?, Rc::new(|_| Tokens::BitShiftLeftSymbol)))
        .or(LazyLexer::new(RegexAst::new(">>")?, Rc::new(|_| Tokens::BitShiftRightSymbol)))
        .or(LazyLexer::new(RegexAst::new(";")?, Rc::new(|_| Tokens::SemiColon)))
        .realize()
    };
    Ok(result)
  }
  pub fn to_tokens<'a>(self: &'a Self, src: String) -> TokenIter<'a, Tokens> {
    self.lexer.tokenize(src)
  }
}
