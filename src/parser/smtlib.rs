//! SMT-LIB 2 format parser
//!
//! Parses SMT-LIB 2 input format used by SMT solvers.
//! Supports: set-logic, declare-fun, assert, check-sat, get-model

use std::collections::HashMap;
use std::fmt;

/// SMT-LIB parsing error
#[derive(Debug, Clone, PartialEq)]
pub enum SmtLibError {
    /// Unexpected end of input
    UnexpectedEof,
    /// Unexpected character
    UnexpectedChar(char),
    /// Unexpected token
    UnexpectedToken(String),
    /// Unknown command
    UnknownCommand(String),
    /// Unknown logic
    UnknownLogic(String),
    /// Undeclared function
    UndeclaredFunction(String),
    /// Sort mismatch
    SortMismatch { expected: Sort, found: Sort },
    /// Invalid arity
    InvalidArity { name: String, expected: usize, found: usize },
    /// Parse error with message
    ParseError(String),
}

impl fmt::Display for SmtLibError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtLibError::UnexpectedEof => write!(f, "unexpected end of input"),
            SmtLibError::UnexpectedChar(c) => write!(f, "unexpected character: '{}'", c),
            SmtLibError::UnexpectedToken(t) => write!(f, "unexpected token: {}", t),
            SmtLibError::UnknownCommand(c) => write!(f, "unknown command: {}", c),
            SmtLibError::UnknownLogic(l) => write!(f, "unknown or unsupported logic: {}", l),
            SmtLibError::UndeclaredFunction(n) => write!(f, "undeclared function: {}", n),
            SmtLibError::SortMismatch { expected, found } => {
                write!(f, "sort mismatch: expected {:?}, found {:?}", expected, found)
            }
            SmtLibError::InvalidArity { name, expected, found } => {
                write!(f, "invalid arity for {}: expected {}, found {}", name, expected, found)
            }
            SmtLibError::ParseError(msg) => write!(f, "parse error: {}", msg),
        }
    }
}

impl std::error::Error for SmtLibError {}

/// SMT-LIB sorts (types)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// Boolean sort
    Bool,
    /// Integer sort
    Int,
    /// Real sort
    Real,
    /// Bitvector sort with width
    BitVec(u32),
    /// Array sort (index -> element)
    Array(Box<Sort>, Box<Sort>),
    /// Uninterpreted sort
    Uninterpreted(String),
}

/// SMT-LIB logic
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub enum Logic {
    /// Quantifier-free uninterpreted functions
    QF_UF,
    /// Quantifier-free linear integer arithmetic
    QF_LIA,
    /// Quantifier-free linear real arithmetic
    QF_LRA,
    /// Quantifier-free bitvectors
    QF_BV,
    /// Quantifier-free arrays
    QF_A,
    /// Quantifier-free arrays with uninterpreted functions and linear integer arithmetic
    QF_AUFLIA,
    /// All theories
    ALL,
}

impl Logic {
    /// Parse logic name from string
    pub fn from_str(s: &str) -> Option<Logic> {
        match s {
            "QF_UF" => Some(Logic::QF_UF),
            "QF_LIA" => Some(Logic::QF_LIA),
            "QF_LRA" => Some(Logic::QF_LRA),
            "QF_BV" => Some(Logic::QF_BV),
            "QF_A" => Some(Logic::QF_A),
            "QF_AUFLIA" => Some(Logic::QF_AUFLIA),
            "ALL" => Some(Logic::ALL),
            _ => None,
        }
    }
}

/// Function declaration
#[derive(Debug, Clone)]
pub struct FunDecl {
    /// Function name
    pub name: String,
    /// Parameter sorts
    pub params: Vec<Sort>,
    /// Return sort
    pub ret: Sort,
}

/// SMT-LIB term (expression)
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Boolean constant
    Bool(bool),
    /// Integer constant
    Int(i64),
    /// Real constant (as string to preserve precision)
    Real(String),
    /// Bitvector constant
    BitVec { value: u64, width: u32 },
    /// Variable or constant reference
    Var(String),
    /// Function application
    App { func: String, args: Vec<Term> },
    /// Let binding
    Let { bindings: Vec<(String, Term)>, body: Box<Term> },
    /// Negation
    Not(Box<Term>),
    /// Conjunction
    And(Vec<Term>),
    /// Disjunction
    Or(Vec<Term>),
    /// Implication
    Implies(Box<Term>, Box<Term>),
    /// Equality
    Eq(Vec<Term>),
    /// Distinct (pairwise inequality)
    Distinct(Vec<Term>),
    /// If-then-else
    Ite(Box<Term>, Box<Term>, Box<Term>),
    /// Arithmetic addition
    Add(Vec<Term>),
    /// Arithmetic subtraction
    Sub(Box<Term>, Box<Term>),
    /// Arithmetic multiplication
    Mul(Vec<Term>),
    /// Arithmetic division
    Div(Box<Term>, Box<Term>),
    /// Arithmetic negation
    Neg(Box<Term>),
    /// Less than
    Lt(Box<Term>, Box<Term>),
    /// Less than or equal
    Le(Box<Term>, Box<Term>),
    /// Greater than
    Gt(Box<Term>, Box<Term>),
    /// Greater than or equal
    Ge(Box<Term>, Box<Term>),
}

/// SMT-LIB command
#[derive(Debug, Clone)]
pub enum Command {
    /// Set the logic
    SetLogic(Logic),
    /// Declare a sort
    DeclareSort { name: String, arity: u32 },
    /// Declare a function/constant
    DeclareFun(FunDecl),
    /// Define a function
    DefineFun { name: String, params: Vec<(String, Sort)>, ret: Sort, body: Term },
    /// Assert a formula
    Assert(Term),
    /// Check satisfiability
    CheckSat,
    /// Get model (after SAT)
    GetModel,
    /// Get value of terms
    GetValue(Vec<Term>),
    /// Push assertion stack
    Push(u32),
    /// Pop assertion stack
    Pop(u32),
    /// Exit
    Exit,
}

/// Parsed SMT-LIB script
#[derive(Debug, Clone)]
pub struct Script {
    /// Logic (if set)
    pub logic: Option<Logic>,
    /// Function declarations
    pub functions: HashMap<String, FunDecl>,
    /// Assertions
    pub assertions: Vec<Term>,
    /// Commands in order
    pub commands: Vec<Command>,
}

impl Script {
    /// Create empty script
    pub fn new() -> Self {
        Script {
            logic: None,
            functions: HashMap::new(),
            assertions: Vec::new(),
            commands: Vec::new(),
        }
    }
}

impl Default for Script {
    fn default() -> Self {
        Self::new()
    }
}

/// S-expression token
#[derive(Debug, Clone, PartialEq)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
    Numeral(i64),
    Decimal(String),
    String(String),
    BitVec { value: u64, width: u32 },
}

/// Tokenizer for SMT-LIB
struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer { input, pos: 0 }
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn next_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() {
                self.next_char();
            } else if c == ';' {
                // Comment - skip to end of line
                while let Some(c) = self.next_char() {
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Result<Option<Token>, SmtLibError> {
        self.skip_whitespace();

        let c = match self.peek_char() {
            Some(c) => c,
            None => return Ok(None),
        };

        match c {
            '(' => {
                self.next_char();
                Ok(Some(Token::LParen))
            }
            ')' => {
                self.next_char();
                Ok(Some(Token::RParen))
            }
            '"' => {
                self.next_char();
                let mut s = String::new();
                loop {
                    match self.next_char() {
                        Some('"') => {
                            // Check for escaped quote
                            if self.peek_char() == Some('"') {
                                self.next_char();
                                s.push('"');
                            } else {
                                break;
                            }
                        }
                        Some(c) => s.push(c),
                        None => return Err(SmtLibError::UnexpectedEof),
                    }
                }
                Ok(Some(Token::String(s)))
            }
            '#' => {
                self.next_char();
                match self.next_char() {
                    Some('b') => {
                        // Binary bitvector #b0101
                        let mut bits = String::new();
                        while let Some(c) = self.peek_char() {
                            if c == '0' || c == '1' {
                                bits.push(c);
                                self.next_char();
                            } else {
                                break;
                            }
                        }
                        let width = bits.len() as u32;
                        let value = u64::from_str_radix(&bits, 2)
                            .map_err(|_| SmtLibError::ParseError("invalid bitvector".to_string()))?;
                        Ok(Some(Token::BitVec { value, width }))
                    }
                    Some('x') => {
                        // Hex bitvector #xABCD
                        let mut hex = String::new();
                        while let Some(c) = self.peek_char() {
                            if c.is_ascii_hexdigit() {
                                hex.push(c);
                                self.next_char();
                            } else {
                                break;
                            }
                        }
                        let width = (hex.len() * 4) as u32;
                        let value = u64::from_str_radix(&hex, 16)
                            .map_err(|_| SmtLibError::ParseError("invalid bitvector".to_string()))?;
                        Ok(Some(Token::BitVec { value, width }))
                    }
                    Some(c) => Err(SmtLibError::UnexpectedChar(c)),
                    None => Err(SmtLibError::UnexpectedEof),
                }
            }
            '0'..='9' => {
                let mut num = String::new();
                while let Some(c) = self.peek_char() {
                    if c.is_ascii_digit() {
                        num.push(c);
                        self.next_char();
                    } else {
                        break;
                    }
                }
                // Check for decimal
                if self.peek_char() == Some('.') {
                    num.push('.');
                    self.next_char();
                    while let Some(c) = self.peek_char() {
                        if c.is_ascii_digit() {
                            num.push(c);
                            self.next_char();
                        } else {
                            break;
                        }
                    }
                    Ok(Some(Token::Decimal(num)))
                } else {
                    let n: i64 = num.parse()
                        .map_err(|_| SmtLibError::ParseError("invalid numeral".to_string()))?;
                    Ok(Some(Token::Numeral(n)))
                }
            }
            _ if is_symbol_char(c) => {
                let mut sym = String::new();
                while let Some(c) = self.peek_char() {
                    if is_symbol_char(c) || c.is_ascii_digit() {
                        sym.push(c);
                        self.next_char();
                    } else {
                        break;
                    }
                }
                Ok(Some(Token::Symbol(sym)))
            }
            '|' => {
                // Quoted symbol |...|
                self.next_char();
                let mut sym = String::new();
                loop {
                    match self.next_char() {
                        Some('|') => break,
                        Some(c) => sym.push(c),
                        None => return Err(SmtLibError::UnexpectedEof),
                    }
                }
                Ok(Some(Token::Symbol(sym)))
            }
            _ => Err(SmtLibError::UnexpectedChar(c)),
        }
    }
}

fn is_symbol_char(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '+' | '-' | '*' | '/' | '=' | '<' | '>' | '!' | '?' | '@' | '$' | '%' | '^' | '&' | '~')
}

/// SMT-LIB parser
pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Option<Token>,
}

impl<'a> Parser<'a> {
    /// Create new parser
    pub fn new(input: &'a str) -> Self {
        Parser {
            lexer: Lexer::new(input),
            current: None,
        }
    }

    fn advance(&mut self) -> Result<(), SmtLibError> {
        self.current = self.lexer.next_token()?;
        Ok(())
    }

    fn expect_lparen(&mut self) -> Result<(), SmtLibError> {
        match &self.current {
            Some(Token::LParen) => {
                self.advance()?;
                Ok(())
            }
            Some(t) => Err(SmtLibError::UnexpectedToken(format!("{:?}", t))),
            None => Err(SmtLibError::UnexpectedEof),
        }
    }

    fn expect_rparen(&mut self) -> Result<(), SmtLibError> {
        match &self.current {
            Some(Token::RParen) => {
                self.advance()?;
                Ok(())
            }
            Some(t) => Err(SmtLibError::UnexpectedToken(format!("{:?}", t))),
            None => Err(SmtLibError::UnexpectedEof),
        }
    }

    fn expect_symbol(&mut self) -> Result<String, SmtLibError> {
        match self.current.take() {
            Some(Token::Symbol(s)) => {
                self.advance()?;
                Ok(s)
            }
            Some(t) => Err(SmtLibError::UnexpectedToken(format!("{:?}", t))),
            None => Err(SmtLibError::UnexpectedEof),
        }
    }

    fn parse_sort(&mut self) -> Result<Sort, SmtLibError> {
        match &self.current {
            Some(Token::Symbol(s)) => {
                let sort = match s.as_str() {
                    "Bool" => Sort::Bool,
                    "Int" => Sort::Int,
                    "Real" => Sort::Real,
                    name => Sort::Uninterpreted(name.to_string()),
                };
                self.advance()?;
                Ok(sort)
            }
            Some(Token::LParen) => {
                self.advance()?;
                let head = self.expect_symbol()?;
                match head.as_str() {
                    "_" => {
                        let name = self.expect_symbol()?;
                        if name == "BitVec" {
                            let width = match &self.current {
                                Some(Token::Numeral(n)) => *n as u32,
                                _ => return Err(SmtLibError::ParseError("expected bitvector width".to_string())),
                            };
                            self.advance()?;
                            self.expect_rparen()?;
                            Ok(Sort::BitVec(width))
                        } else {
                            Err(SmtLibError::ParseError(format!("unknown indexed sort: {}", name)))
                        }
                    }
                    "Array" => {
                        let index = self.parse_sort()?;
                        let elem = self.parse_sort()?;
                        self.expect_rparen()?;
                        Ok(Sort::Array(Box::new(index), Box::new(elem)))
                    }
                    _ => Err(SmtLibError::ParseError(format!("unknown sort constructor: {}", head))),
                }
            }
            _ => Err(SmtLibError::ParseError("expected sort".to_string())),
        }
    }

    fn parse_term(&mut self) -> Result<Term, SmtLibError> {
        match self.current.take() {
            Some(Token::Symbol(s)) => {
                self.advance()?;
                match s.as_str() {
                    "true" => Ok(Term::Bool(true)),
                    "false" => Ok(Term::Bool(false)),
                    _ => Ok(Term::Var(s)),
                }
            }
            Some(Token::Numeral(n)) => {
                self.advance()?;
                Ok(Term::Int(n))
            }
            Some(Token::Decimal(d)) => {
                self.advance()?;
                Ok(Term::Real(d))
            }
            Some(Token::BitVec { value, width }) => {
                self.advance()?;
                Ok(Term::BitVec { value, width })
            }
            Some(Token::LParen) => {
                self.advance()?;
                let head = self.expect_symbol()?;
                
                let term = match head.as_str() {
                    "let" => {
                        self.expect_lparen()?;
                        let mut bindings = Vec::new();
                        while self.current != Some(Token::RParen) {
                            self.expect_lparen()?;
                            let name = self.expect_symbol()?;
                            let value = self.parse_term()?;
                            self.expect_rparen()?;
                            bindings.push((name, value));
                        }
                        self.advance()?; // consume )
                        let body = self.parse_term()?;
                        Term::Let { bindings, body: Box::new(body) }
                    }
                    "not" => {
                        let arg = self.parse_term()?;
                        Term::Not(Box::new(arg))
                    }
                    "and" => {
                        let args = self.parse_term_list()?;
                        Term::And(args)
                    }
                    "or" => {
                        let args = self.parse_term_list()?;
                        Term::Or(args)
                    }
                    "=>" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Implies(Box::new(lhs), Box::new(rhs))
                    }
                    "=" => {
                        let args = self.parse_term_list()?;
                        Term::Eq(args)
                    }
                    "distinct" => {
                        let args = self.parse_term_list()?;
                        Term::Distinct(args)
                    }
                    "ite" => {
                        let cond = self.parse_term()?;
                        let then_branch = self.parse_term()?;
                        let else_branch = self.parse_term()?;
                        Term::Ite(Box::new(cond), Box::new(then_branch), Box::new(else_branch))
                    }
                    "+" => {
                        let args = self.parse_term_list()?;
                        Term::Add(args)
                    }
                    "-" => {
                        let first = self.parse_term()?;
                        if self.current == Some(Token::RParen) {
                            Term::Neg(Box::new(first))
                        } else {
                            let second = self.parse_term()?;
                            Term::Sub(Box::new(first), Box::new(second))
                        }
                    }
                    "*" => {
                        let args = self.parse_term_list()?;
                        Term::Mul(args)
                    }
                    "div" | "/" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Div(Box::new(lhs), Box::new(rhs))
                    }
                    "<" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Lt(Box::new(lhs), Box::new(rhs))
                    }
                    "<=" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Le(Box::new(lhs), Box::new(rhs))
                    }
                    ">" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Gt(Box::new(lhs), Box::new(rhs))
                    }
                    ">=" => {
                        let lhs = self.parse_term()?;
                        let rhs = self.parse_term()?;
                        Term::Ge(Box::new(lhs), Box::new(rhs))
                    }
                    func => {
                        let args = self.parse_term_list()?;
                        Term::App { func: func.to_string(), args }
                    }
                };
                
                self.expect_rparen()?;
                Ok(term)
            }
            Some(t) => Err(SmtLibError::UnexpectedToken(format!("{:?}", t))),
            None => Err(SmtLibError::UnexpectedEof),
        }
    }

    fn parse_term_list(&mut self) -> Result<Vec<Term>, SmtLibError> {
        let mut terms = Vec::new();
        while self.current != Some(Token::RParen) {
            terms.push(self.parse_term()?);
        }
        Ok(terms)
    }

    fn parse_command(&mut self) -> Result<Option<Command>, SmtLibError> {
        if self.current.is_none() {
            return Ok(None);
        }

        self.expect_lparen()?;
        let cmd_name = self.expect_symbol()?;

        let cmd = match cmd_name.as_str() {
            "set-logic" => {
                let logic_name = self.expect_symbol()?;
                let logic = Logic::from_str(&logic_name)
                    .ok_or_else(|| SmtLibError::UnknownLogic(logic_name))?;
                Command::SetLogic(logic)
            }
            "declare-sort" => {
                let name = self.expect_symbol()?;
                let arity = match &self.current {
                    Some(Token::Numeral(n)) => *n as u32,
                    _ => return Err(SmtLibError::ParseError("expected numeral".to_string())),
                };
                self.advance()?;
                Command::DeclareSort { name, arity }
            }
            "declare-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                while self.current != Some(Token::RParen) {
                    params.push(self.parse_sort()?);
                }
                self.advance()?; // consume )
                let ret = self.parse_sort()?;
                Command::DeclareFun(FunDecl { name, params, ret })
            }
            "define-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                while self.current != Some(Token::RParen) {
                    self.expect_lparen()?;
                    let param_name = self.expect_symbol()?;
                    let param_sort = self.parse_sort()?;
                    self.expect_rparen()?;
                    params.push((param_name, param_sort));
                }
                self.advance()?; // consume )
                let ret = self.parse_sort()?;
                let body = self.parse_term()?;
                Command::DefineFun { name, params, ret, body }
            }
            "assert" => {
                let term = self.parse_term()?;
                Command::Assert(term)
            }
            "check-sat" => Command::CheckSat,
            "get-model" => Command::GetModel,
            "get-value" => {
                self.expect_lparen()?;
                let terms = self.parse_term_list()?;
                self.advance()?; // consume )
                Command::GetValue(terms)
            }
            "push" => {
                let n = match &self.current {
                    Some(Token::Numeral(n)) => {
                        let v = *n as u32;
                        self.advance()?;
                        v
                    }
                    _ => 1,
                };
                Command::Push(n)
            }
            "pop" => {
                let n = match &self.current {
                    Some(Token::Numeral(n)) => {
                        let v = *n as u32;
                        self.advance()?;
                        v
                    }
                    _ => 1,
                };
                Command::Pop(n)
            }
            "exit" => Command::Exit,
            _ => return Err(SmtLibError::UnknownCommand(cmd_name)),
        };

        self.expect_rparen()?;
        Ok(Some(cmd))
    }

    /// Parse entire script
    pub fn parse_script(&mut self) -> Result<Script, SmtLibError> {
        self.advance()?;
        
        let mut script = Script::new();
        
        while let Some(cmd) = self.parse_command()? {
            match &cmd {
                Command::SetLogic(logic) => {
                    script.logic = Some(*logic);
                }
                Command::DeclareFun(decl) => {
                    script.functions.insert(decl.name.clone(), decl.clone());
                }
                Command::Assert(term) => {
                    script.assertions.push(term.clone());
                }
                _ => {}
            }
            script.commands.push(cmd);
        }
        
        Ok(script)
    }
}

/// Parse SMT-LIB 2 input
pub fn parse_smtlib(input: &str) -> Result<Script, SmtLibError> {
    let mut parser = Parser::new(input);
    parser.parse_script()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_qf_uf() {
        let input = r#"
            (set-logic QF_UF)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (assert (or p q))
            (assert (not p))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.logic, Some(Logic::QF_UF));
        assert_eq!(script.functions.len(), 2);
        assert_eq!(script.assertions.len(), 2);
    }

    #[test]
    fn test_parse_qf_lia() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (assert (> x 0))
            (assert (< y 10))
            (assert (= (+ x y) 15))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.logic, Some(Logic::QF_LIA));
        assert_eq!(script.functions.len(), 2);
        assert_eq!(script.assertions.len(), 3);
    }

    #[test]
    fn test_parse_bitvector() {
        let input = r#"
            (set-logic QF_BV)
            (declare-fun x () (_ BitVec 32))
            (assert (= x #x0000FFFF))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.logic, Some(Logic::QF_BV));
        
        let decl = script.functions.get("x").unwrap();
        assert_eq!(decl.ret, Sort::BitVec(32));
    }

    #[test]
    fn test_parse_let_binding() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (let ((y (+ x 1))) (> y 0)))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.assertions.len(), 1);
        
        match &script.assertions[0] {
            Term::Let { bindings, .. } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "y");
            }
            _ => panic!("expected let term"),
        }
    }

    #[test]
    fn test_parse_ite() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (= x (ite (> x 0) 1 (- 1))))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.assertions.len(), 1);
    }

    #[test]
    fn test_parse_array() {
        let input = r#"
            (set-logic QF_A)
            (declare-fun a () (Array Int Int))
            (declare-fun i () Int)
            (assert (= (select a i) 42))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        let decl = script.functions.get("a").unwrap();
        match &decl.ret {
            Sort::Array(idx, elem) => {
                assert_eq!(**idx, Sort::Int);
                assert_eq!(**elem, Sort::Int);
            }
            _ => panic!("expected array sort"),
        }
    }

    #[test]
    fn test_parse_comments() {
        let input = r#"
            ; This is a comment
            (set-logic QF_UF)
            ; Another comment
            (declare-fun p () Bool)
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.logic, Some(Logic::QF_UF));
    }

    #[test]
    fn test_parse_binary_bitvector() {
        let input = r#"
            (set-logic QF_BV)
            (declare-fun x () (_ BitVec 8))
            (assert (= x #b10101010))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        match &script.assertions[0] {
            Term::Eq(args) => {
                match &args[1] {
                    Term::BitVec { value, width } => {
                        assert_eq!(*value, 0b10101010);
                        assert_eq!(*width, 8);
                    }
                    _ => panic!("expected bitvector"),
                }
            }
            _ => panic!("expected equality"),
        }
    }

    #[test]
    fn test_unknown_logic_error() {
        let input = "(set-logic UNKNOWN_LOGIC)";
        let result = parse_smtlib(input);
        assert!(matches!(result, Err(SmtLibError::UnknownLogic(_))));
    }

    #[test]
    fn test_parse_distinct() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
            (assert (distinct x y z))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        match &script.assertions[0] {
            Term::Distinct(args) => {
                assert_eq!(args.len(), 3);
            }
            _ => panic!("expected distinct"),
        }
    }

    #[test]
    fn test_parse_define_fun() {
        let input = r#"
            (set-logic QF_LIA)
            (define-fun double ((x Int)) Int (* x 2))
            (declare-fun y () Int)
            (assert (= (double y) 10))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        let has_define = script.commands.iter().any(|c| matches!(c, Command::DefineFun { .. }));
        assert!(has_define);
    }

    #[test]
    fn test_parse_push_pop() {
        let input = r#"
            (set-logic QF_UF)
            (declare-fun p () Bool)
            (push 1)
            (assert p)
            (check-sat)
            (pop 1)
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        let push_count = script.commands.iter().filter(|c| matches!(c, Command::Push(_))).count();
        let pop_count = script.commands.iter().filter(|c| matches!(c, Command::Pop(_))).count();
        
        assert_eq!(push_count, 1);
        assert_eq!(pop_count, 1);
    }

    #[test]
    fn test_parse_implies() {
        let input = r#"
            (set-logic QF_UF)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (assert (=> p q))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        match &script.assertions[0] {
            Term::Implies(_, _) => {}
            _ => panic!("expected implies"),
        }
    }

    #[test]
    fn test_parse_nested_arithmetic() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (= (+ (* x 2) (- x 1)) 10))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        assert_eq!(script.assertions.len(), 1);
    }

    #[test]
    fn test_parse_function_application() {
        let input = r#"
            (set-logic QF_UF)
            (declare-fun f (Int) Int)
            (declare-fun x () Int)
            (assert (= (f x) x))
            (check-sat)
        "#;
        
        let script = parse_smtlib(input).unwrap();
        
        let f_decl = script.functions.get("f").unwrap();
        assert_eq!(f_decl.params.len(), 1);
        assert_eq!(f_decl.params[0], Sort::Int);
        assert_eq!(f_decl.ret, Sort::Int);
    }
}
