//! SMT-LIB 2 parser.
//!
//! Parses SMT-LIB 2 format into an internal representation.
//! Supports: set-logic, declare-fun, define-fun, assert, check-sat, get-model, push, pop.

use std::collections::HashMap;
use std::fmt;
use std::path::Path;

/// SMT-LIB parse error.
#[derive(Debug, Clone)]
pub struct SmtLibError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for SmtLibError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SMT-LIB error at {}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for SmtLibError {}

/// SMT-LIB logic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Logic {
    QfUf,      // Quantifier-free uninterpreted functions
    QfLia,     // Quantifier-free linear integer arithmetic
    QfLra,     // Quantifier-free linear real arithmetic
    QfBv,      // Quantifier-free bitvectors
    QfA,       // Quantifier-free arrays
    QfAuflia,  // Combined: arrays + UF + LIA
    QfAufbv,   // Combined: arrays + UF + BV
    All,       // All theories
}

impl Logic {
    pub fn from_str(s: &str) -> Option<Logic> {
        match s.to_uppercase().as_str() {
            "QF_UF" => Some(Logic::QfUf),
            "QF_LIA" => Some(Logic::QfLia),
            "QF_LRA" => Some(Logic::QfLra),
            "QF_BV" => Some(Logic::QfBv),
            "QF_A" | "QF_AX" => Some(Logic::QfA),
            "QF_AUFLIA" => Some(Logic::QfAuflia),
            "QF_AUFBV" => Some(Logic::QfAufbv),
            "ALL" => Some(Logic::All),
            _ => None,
        }
    }
}

/// SMT-LIB sort (type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(Box<Sort>, Box<Sort>),
    Uninterpreted(String),
}

impl Sort {
    pub fn is_bool(&self) -> bool {
        matches!(self, Sort::Bool)
    }
    
    pub fn is_int(&self) -> bool {
        matches!(self, Sort::Int)
    }
    
    pub fn is_bitvec(&self) -> bool {
        matches!(self, Sort::BitVec(_))
    }
}

/// Function declaration.
#[derive(Debug, Clone)]
pub struct FunDecl {
    pub name: String,
    pub params: Vec<Sort>,
    pub return_sort: Sort,
}

/// SMT-LIB term (expression).
#[derive(Debug, Clone)]
pub enum Term {
    // Constants
    True,
    False,
    IntLit(i64),
    RealLit(f64),
    BitVecLit { value: u64, width: u32 },
    
    // Variables
    Var(String),
    
    // Boolean operations
    Not(Box<Term>),
    And(Vec<Term>),
    Or(Vec<Term>),
    Xor(Box<Term>, Box<Term>),
    Implies(Box<Term>, Box<Term>),
    Ite(Box<Term>, Box<Term>, Box<Term>),
    
    // Equality
    Eq(Box<Term>, Box<Term>),
    Distinct(Vec<Term>),
    
    // Arithmetic
    Neg(Box<Term>),
    Add(Vec<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Vec<Term>),
    Div(Box<Term>, Box<Term>),
    Mod(Box<Term>, Box<Term>),
    Abs(Box<Term>),
    
    // Comparisons
    Lt(Box<Term>, Box<Term>),
    Le(Box<Term>, Box<Term>),
    Gt(Box<Term>, Box<Term>),
    Ge(Box<Term>, Box<Term>),
    
    // Bitvector operations
    BvNot(Box<Term>),
    BvAnd(Box<Term>, Box<Term>),
    BvOr(Box<Term>, Box<Term>),
    BvXor(Box<Term>, Box<Term>),
    BvAdd(Box<Term>, Box<Term>),
    BvSub(Box<Term>, Box<Term>),
    BvMul(Box<Term>, Box<Term>),
    BvUdiv(Box<Term>, Box<Term>),
    BvSdiv(Box<Term>, Box<Term>),
    BvUrem(Box<Term>, Box<Term>),
    BvSrem(Box<Term>, Box<Term>),
    BvShl(Box<Term>, Box<Term>),
    BvLshr(Box<Term>, Box<Term>),
    BvAshr(Box<Term>, Box<Term>),
    BvUlt(Box<Term>, Box<Term>),
    BvUle(Box<Term>, Box<Term>),
    BvUgt(Box<Term>, Box<Term>),
    BvUge(Box<Term>, Box<Term>),
    BvSlt(Box<Term>, Box<Term>),
    BvSle(Box<Term>, Box<Term>),
    BvSgt(Box<Term>, Box<Term>),
    BvSge(Box<Term>, Box<Term>),
    BvConcat(Box<Term>, Box<Term>),
    BvExtract { high: u32, low: u32, term: Box<Term> },
    BvZeroExtend(u32, Box<Term>),
    BvSignExtend(u32, Box<Term>),
    
    // Array operations
    Select(Box<Term>, Box<Term>),
    Store(Box<Term>, Box<Term>, Box<Term>),
    
    // Function application
    Apply(String, Vec<Term>),
    
    // Let binding
    Let(Vec<(String, Term)>, Box<Term>),
}

/// SMT-LIB command.
#[derive(Debug, Clone)]
pub enum Command {
    SetLogic(Logic),
    DeclareSort(String, u32),
    DeclareFun(FunDecl),
    DefineFun(String, Vec<(String, Sort)>, Sort, Term),
    Assert(Term),
    CheckSat,
    GetModel,
    GetValue(Vec<Term>),
    Push(u32),
    Pop(u32),
    Reset,
    Exit,
}

/// Parsed SMT-LIB problem.
#[derive(Debug, Clone)]
pub struct SmtProblem {
    pub logic: Option<Logic>,
    pub declarations: Vec<FunDecl>,
    pub definitions: HashMap<String, (Vec<(String, Sort)>, Sort, Term)>,
    pub assertions: Vec<Term>,
    pub commands: Vec<Command>,
}

impl SmtProblem {
    pub fn new() -> Self {
        SmtProblem {
            logic: None,
            declarations: Vec::new(),
            definitions: HashMap::new(),
            assertions: Vec::new(),
            commands: Vec::new(),
        }
    }
}

impl Default for SmtProblem {
    fn default() -> Self {
        Self::new()
    }
}

/// Token for lexing.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
    Keyword(String),
    Numeral(i64),
    Decimal(f64),
    HexLit(u64, u32),  // value, width
    BinLit(u64, u32),  // value, width
    StringLit(String),
}

/// Lexer for SMT-LIB.
struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    line: usize,
    column: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            input,
            pos: 0,
            line: 1,
            column: 1,
        }
    }
    
    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }
    
    fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(c)
    }
    
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else if c == ';' {
                // Comment - skip to end of line
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }
    
    fn read_symbol(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c) {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        s
    }
    
    fn read_quoted_symbol(&mut self) -> Result<String, SmtLibError> {
        self.advance(); // skip |
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '|' {
                self.advance();
                return Ok(s);
            } else if c == '\\' {
                self.advance();
                if let Some(escaped) = self.advance() {
                    s.push(escaped);
                }
            } else {
                s.push(c);
                self.advance();
            }
        }
        Err(SmtLibError {
            message: "Unterminated quoted symbol".to_string(),
            line: self.line,
            column: self.column,
        })
    }
    
    fn read_string(&mut self) -> Result<String, SmtLibError> {
        self.advance(); // skip opening "
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '"' {
                self.advance();
                // Check for escaped quote
                if self.peek() == Some('"') {
                    s.push('"');
                    self.advance();
                } else {
                    return Ok(s);
                }
            } else {
                s.push(c);
                self.advance();
            }
        }
        Err(SmtLibError {
            message: "Unterminated string literal".to_string(),
            line: self.line,
            column: self.column,
        })
    }
    
    fn read_numeral(&mut self) -> i64 {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        s.parse().unwrap_or(0)
    }
    
    fn read_hex(&mut self) -> (u64, u32) {
        self.advance(); // skip #
        self.advance(); // skip x
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_hexdigit() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        let width = (s.len() * 4) as u32;
        let value = u64::from_str_radix(&s, 16).unwrap_or(0);
        (value, width)
    }
    
    fn read_binary(&mut self) -> (u64, u32) {
        self.advance(); // skip #
        self.advance(); // skip b
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c == '0' || c == '1' {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        let width = s.len() as u32;
        let value = u64::from_str_radix(&s, 2).unwrap_or(0);
        (value, width)
    }
    
    fn next_token(&mut self) -> Result<Option<Token>, SmtLibError> {
        self.skip_whitespace();
        
        let Some(c) = self.peek() else {
            return Ok(None);
        };
        
        match c {
            '(' => {
                self.advance();
                Ok(Some(Token::LParen))
            }
            ')' => {
                self.advance();
                Ok(Some(Token::RParen))
            }
            '|' => {
                let s = self.read_quoted_symbol()?;
                Ok(Some(Token::Symbol(s)))
            }
            '"' => {
                let s = self.read_string()?;
                Ok(Some(Token::StringLit(s)))
            }
            ':' => {
                self.advance();
                let s = self.read_symbol();
                Ok(Some(Token::Keyword(s)))
            }
            '#' => {
                let next = self.input[self.pos + 1..].chars().next();
                match next {
                    Some('x') | Some('X') => {
                        let (value, width) = self.read_hex();
                        Ok(Some(Token::HexLit(value, width)))
                    }
                    Some('b') | Some('B') => {
                        let (value, width) = self.read_binary();
                        Ok(Some(Token::BinLit(value, width)))
                    }
                    _ => {
                        Err(SmtLibError {
                            message: format!("Invalid # literal"),
                            line: self.line,
                            column: self.column,
                        })
                    }
                }
            }
            c if c.is_ascii_digit() => {
                let n = self.read_numeral();
                if self.peek() == Some('.') {
                    self.advance();
                    let frac_start = self.pos;
                    let frac = self.read_numeral();
                    let frac_len = self.pos - frac_start;
                    let decimal = n as f64 + (frac as f64) / 10f64.powi(frac_len as i32);
                    Ok(Some(Token::Decimal(decimal)))
                } else {
                    Ok(Some(Token::Numeral(n)))
                }
            }
            _ => {
                let s = self.read_symbol();
                if s.is_empty() {
                    Err(SmtLibError {
                        message: format!("Unexpected character: {}", c),
                        line: self.line,
                        column: self.column,
                    })
                } else {
                    Ok(Some(Token::Symbol(s)))
                }
            }
        }
    }
    
    fn tokenize(&mut self) -> Result<Vec<Token>, SmtLibError> {
        let mut tokens = Vec::new();
        while let Some(tok) = self.next_token()? {
            tokens.push(tok);
        }
        Ok(tokens)
    }
}

/// Parser for SMT-LIB.
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }
    
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
    
    fn advance(&mut self) -> Option<&Token> {
        let tok = self.tokens.get(self.pos);
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }
    
    fn expect_lparen(&mut self) -> Result<(), SmtLibError> {
        match self.advance() {
            Some(Token::LParen) => Ok(()),
            _ => Err(SmtLibError {
                message: "Expected '('".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn expect_rparen(&mut self) -> Result<(), SmtLibError> {
        match self.advance() {
            Some(Token::RParen) => Ok(()),
            _ => Err(SmtLibError {
                message: "Expected ')'".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn expect_symbol(&mut self) -> Result<String, SmtLibError> {
        match self.advance() {
            Some(Token::Symbol(s)) => Ok(s.clone()),
            _ => Err(SmtLibError {
                message: "Expected symbol".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn parse_sort(&mut self) -> Result<Sort, SmtLibError> {
        match self.peek() {
            Some(Token::Symbol(s)) => {
                let s = s.clone();
                self.advance();
                match s.as_str() {
                    "Bool" => Ok(Sort::Bool),
                    "Int" => Ok(Sort::Int),
                    "Real" => Ok(Sort::Real),
                    _ => Ok(Sort::Uninterpreted(s)),
                }
            }
            Some(Token::LParen) => {
                self.advance();
                let head = self.expect_symbol()?;
                match head.as_str() {
                    "_" => {
                        let sort_name = self.expect_symbol()?;
                        if sort_name == "BitVec" {
                            let width = match self.advance().cloned() {
                                Some(Token::Numeral(n)) => n as u32,
                                _ => return Err(SmtLibError {
                                    message: "Expected bitvector width".to_string(),
                                    line: 0,
                                    column: 0,
                                }),
                            };
                            self.expect_rparen()?;
                            Ok(Sort::BitVec(width))
                        } else {
                            Err(SmtLibError {
                                message: format!("Unknown indexed sort: {}", sort_name),
                                line: 0,
                                column: 0,
                            })
                        }
                    }
                    "Array" => {
                        let index_sort = self.parse_sort()?;
                        let elem_sort = self.parse_sort()?;
                        self.expect_rparen()?;
                        Ok(Sort::Array(Box::new(index_sort), Box::new(elem_sort)))
                    }
                    _ => Err(SmtLibError {
                        message: format!("Unknown parametric sort: {}", head),
                        line: 0,
                        column: 0,
                    }),
                }
            }
            _ => Err(SmtLibError {
                message: "Expected sort".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn parse_term(&mut self) -> Result<Term, SmtLibError> {
        match self.peek() {
            Some(Token::Symbol(s)) => {
                let s = s.clone();
                self.advance();
                match s.as_str() {
                    "true" => Ok(Term::True),
                    "false" => Ok(Term::False),
                    _ => Ok(Term::Var(s)),
                }
            }
            Some(Token::Numeral(n)) => {
                let n = *n;
                self.advance();
                Ok(Term::IntLit(n))
            }
            Some(Token::Decimal(d)) => {
                let d = *d;
                self.advance();
                Ok(Term::RealLit(d))
            }
            Some(Token::HexLit(v, w)) => {
                let (v, w) = (*v, *w);
                self.advance();
                Ok(Term::BitVecLit { value: v, width: w })
            }
            Some(Token::BinLit(v, w)) => {
                let (v, w) = (*v, *w);
                self.advance();
                Ok(Term::BitVecLit { value: v, width: w })
            }
            Some(Token::LParen) => {
                self.advance();
                self.parse_compound_term()
            }
            _ => Err(SmtLibError {
                message: "Expected term".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn parse_compound_term(&mut self) -> Result<Term, SmtLibError> {
        // Check for special forms
        match self.peek() {
            Some(Token::Symbol(s)) => {
                let op = s.clone();
                self.advance();
                
                match op.as_str() {
                    "not" => {
                        let arg = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Not(Box::new(arg)))
                    }
                    "and" => {
                        let args = self.parse_term_list()?;
                        self.expect_rparen()?;
                        Ok(Term::And(args))
                    }
                    "or" => {
                        let args = self.parse_term_list()?;
                        self.expect_rparen()?;
                        Ok(Term::Or(args))
                    }
                    "xor" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Xor(Box::new(a), Box::new(b)))
                    }
                    "=>" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Implies(Box::new(a), Box::new(b)))
                    }
                    "ite" => {
                        let cond = self.parse_term()?;
                        let then_branch = self.parse_term()?;
                        let else_branch = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Ite(Box::new(cond), Box::new(then_branch), Box::new(else_branch)))
                    }
                    "=" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Eq(Box::new(a), Box::new(b)))
                    }
                    "distinct" => {
                        let args = self.parse_term_list()?;
                        self.expect_rparen()?;
                        Ok(Term::Distinct(args))
                    }
                    "-" => {
                        let a = self.parse_term()?;
                        if matches!(self.peek(), Some(Token::RParen)) {
                            self.expect_rparen()?;
                            Ok(Term::Neg(Box::new(a)))
                        } else {
                            let b = self.parse_term()?;
                            self.expect_rparen()?;
                            Ok(Term::Sub(Box::new(a), Box::new(b)))
                        }
                    }
                    "+" => {
                        let args = self.parse_term_list()?;
                        self.expect_rparen()?;
                        Ok(Term::Add(args))
                    }
                    "*" => {
                        let args = self.parse_term_list()?;
                        self.expect_rparen()?;
                        Ok(Term::Mul(args))
                    }
                    "div" | "/" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Div(Box::new(a), Box::new(b)))
                    }
                    "mod" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Mod(Box::new(a), Box::new(b)))
                    }
                    "abs" => {
                        let a = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Abs(Box::new(a)))
                    }
                    "<" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Lt(Box::new(a), Box::new(b)))
                    }
                    "<=" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Le(Box::new(a), Box::new(b)))
                    }
                    ">" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Gt(Box::new(a), Box::new(b)))
                    }
                    ">=" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Ge(Box::new(a), Box::new(b)))
                    }
                    // Bitvector operations
                    "bvnot" => {
                        let a = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvNot(Box::new(a)))
                    }
                    "bvand" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvAnd(Box::new(a), Box::new(b)))
                    }
                    "bvor" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvOr(Box::new(a), Box::new(b)))
                    }
                    "bvxor" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvXor(Box::new(a), Box::new(b)))
                    }
                    "bvadd" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvAdd(Box::new(a), Box::new(b)))
                    }
                    "bvsub" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSub(Box::new(a), Box::new(b)))
                    }
                    "bvmul" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvMul(Box::new(a), Box::new(b)))
                    }
                    "bvudiv" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUdiv(Box::new(a), Box::new(b)))
                    }
                    "bvsdiv" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSdiv(Box::new(a), Box::new(b)))
                    }
                    "bvurem" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUrem(Box::new(a), Box::new(b)))
                    }
                    "bvsrem" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSrem(Box::new(a), Box::new(b)))
                    }
                    "bvshl" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvShl(Box::new(a), Box::new(b)))
                    }
                    "bvlshr" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvLshr(Box::new(a), Box::new(b)))
                    }
                    "bvashr" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvAshr(Box::new(a), Box::new(b)))
                    }
                    "bvult" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUlt(Box::new(a), Box::new(b)))
                    }
                    "bvule" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUle(Box::new(a), Box::new(b)))
                    }
                    "bvugt" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUgt(Box::new(a), Box::new(b)))
                    }
                    "bvuge" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvUge(Box::new(a), Box::new(b)))
                    }
                    "bvslt" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSlt(Box::new(a), Box::new(b)))
                    }
                    "bvsle" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSle(Box::new(a), Box::new(b)))
                    }
                    "bvsgt" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSgt(Box::new(a), Box::new(b)))
                    }
                    "bvsge" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvSge(Box::new(a), Box::new(b)))
                    }
                    "concat" => {
                        let a = self.parse_term()?;
                        let b = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::BvConcat(Box::new(a), Box::new(b)))
                    }
                    // Array operations
                    "select" => {
                        let arr = self.parse_term()?;
                        let idx = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Select(Box::new(arr), Box::new(idx)))
                    }
                    "store" => {
                        let arr = self.parse_term()?;
                        let idx = self.parse_term()?;
                        let val = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Store(Box::new(arr), Box::new(idx), Box::new(val)))
                    }
                    // Let binding
                    "let" => {
                        self.expect_lparen()?;
                        let mut bindings = Vec::new();
                        while !matches!(self.peek(), Some(Token::RParen)) {
                            self.expect_lparen()?;
                            let name = self.expect_symbol()?;
                            let term = self.parse_term()?;
                            self.expect_rparen()?;
                            bindings.push((name, term));
                        }
                        self.expect_rparen()?;
                        let body = self.parse_term()?;
                        self.expect_rparen()?;
                        Ok(Term::Let(bindings, Box::new(body)))
                    }
                    // Indexed operators
                    "_" => {
                        let op_name = self.expect_symbol()?;
                        match op_name.as_str() {
                            "extract" => {
                                let high = match self.advance() {
                                    Some(Token::Numeral(n)) => *n as u32,
                                    _ => return Err(SmtLibError {
                                        message: "Expected high index".to_string(),
                                        line: 0,
                                        column: 0,
                                    }),
                                };
                                let low = match self.advance() {
                                    Some(Token::Numeral(n)) => *n as u32,
                                    _ => return Err(SmtLibError {
                                        message: "Expected low index".to_string(),
                                        line: 0,
                                        column: 0,
                                    }),
                                };
                                self.expect_rparen()?;
                                let term = self.parse_term()?;
                                self.expect_rparen()?;
                                Ok(Term::BvExtract { high, low, term: Box::new(term) })
                            }
                            "zero_extend" => {
                                let bits = match self.advance() {
                                    Some(Token::Numeral(n)) => *n as u32,
                                    _ => return Err(SmtLibError {
                                        message: "Expected extension bits".to_string(),
                                        line: 0,
                                        column: 0,
                                    }),
                                };
                                self.expect_rparen()?;
                                let term = self.parse_term()?;
                                self.expect_rparen()?;
                                Ok(Term::BvZeroExtend(bits, Box::new(term)))
                            }
                            "sign_extend" => {
                                let bits = match self.advance() {
                                    Some(Token::Numeral(n)) => *n as u32,
                                    _ => return Err(SmtLibError {
                                        message: "Expected extension bits".to_string(),
                                        line: 0,
                                        column: 0,
                                    }),
                                };
                                self.expect_rparen()?;
                                let term = self.parse_term()?;
                                self.expect_rparen()?;
                                Ok(Term::BvSignExtend(bits, Box::new(term)))
                            }
                            _ => Err(SmtLibError {
                                message: format!("Unknown indexed operator: {}", op_name),
                                line: 0,
                                column: 0,
                            }),
                        }
                    }
                    // Function application
                    _ => {
                        let mut args = Vec::new();
                        while !matches!(self.peek(), Some(Token::RParen)) {
                            args.push(self.parse_term()?);
                        }
                        self.expect_rparen()?;
                        Ok(Term::Apply(op, args))
                    }
                }
            }
            Some(Token::LParen) => {
                // Nested expression - could be indexed operator application
                self.advance();
                let inner = self.parse_compound_term()?;
                // Apply to remaining args
                let mut args = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen)) {
                    args.push(self.parse_term()?);
                }
                self.expect_rparen()?;
                
                // Handle extract, zero_extend, sign_extend applied to a term
                match inner {
                    Term::Apply(name, idx_args) if name == "_" && !idx_args.is_empty() => {
                        // This was an indexed operator
                        Err(SmtLibError {
                            message: "Invalid indexed operator application".to_string(),
                            line: 0,
                            column: 0,
                        })
                    }
                    _ => {
                        // Treat as higher-order application (unusual)
                        Err(SmtLibError {
                            message: "Higher-order application not supported".to_string(),
                            line: 0,
                            column: 0,
                        })
                    }
                }
            }
            _ => Err(SmtLibError {
                message: "Expected operator in compound term".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }
    
    fn parse_term_list(&mut self) -> Result<Vec<Term>, SmtLibError> {
        let mut terms = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen)) {
            terms.push(self.parse_term()?);
        }
        Ok(terms)
    }
    
    fn parse_command(&mut self) -> Result<Option<Command>, SmtLibError> {
        if !matches!(self.peek(), Some(Token::LParen)) {
            return Ok(None);
        }
        self.expect_lparen()?;
        
        let cmd_name = self.expect_symbol()?;
        
        let cmd = match cmd_name.as_str() {
            "set-logic" => {
                let logic_name = self.expect_symbol()?;
                let logic = Logic::from_str(&logic_name).ok_or_else(|| SmtLibError {
                    message: format!("Unknown logic: {}", logic_name),
                    line: 0,
                    column: 0,
                })?;
                self.expect_rparen()?;
                Command::SetLogic(logic)
            }
            "declare-sort" => {
                let name = self.expect_symbol()?;
                let arity = match self.advance() {
                    Some(Token::Numeral(n)) => *n as u32,
                    _ => 0,
                };
                self.expect_rparen()?;
                Command::DeclareSort(name, arity)
            }
            "declare-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen)) {
                    params.push(self.parse_sort()?);
                }
                self.expect_rparen()?;
                let return_sort = self.parse_sort()?;
                self.expect_rparen()?;
                Command::DeclareFun(FunDecl { name, params, return_sort })
            }
            "declare-const" => {
                let name = self.expect_symbol()?;
                let sort = self.parse_sort()?;
                self.expect_rparen()?;
                Command::DeclareFun(FunDecl { name, params: vec![], return_sort: sort })
            }
            "define-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen)) {
                    self.expect_lparen()?;
                    let param_name = self.expect_symbol()?;
                    let param_sort = self.parse_sort()?;
                    self.expect_rparen()?;
                    params.push((param_name, param_sort));
                }
                self.expect_rparen()?;
                let return_sort = self.parse_sort()?;
                let body = self.parse_term()?;
                self.expect_rparen()?;
                Command::DefineFun(name, params, return_sort, body)
            }
            "assert" => {
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Command::Assert(term)
            }
            "check-sat" => {
                self.expect_rparen()?;
                Command::CheckSat
            }
            "get-model" => {
                self.expect_rparen()?;
                Command::GetModel
            }
            "get-value" => {
                self.expect_lparen()?;
                let terms = self.parse_term_list()?;
                self.expect_rparen()?;
                self.expect_rparen()?;
                Command::GetValue(terms)
            }
            "push" => {
                let n = match self.peek() {
                    Some(Token::Numeral(n)) => {
                        let n = *n as u32;
                        self.advance();
                        n
                    }
                    _ => 1,
                };
                self.expect_rparen()?;
                Command::Push(n)
            }
            "pop" => {
                let n = match self.peek() {
                    Some(Token::Numeral(n)) => {
                        let n = *n as u32;
                        self.advance();
                        n
                    }
                    _ => 1,
                };
                self.expect_rparen()?;
                Command::Pop(n)
            }
            "reset" => {
                self.expect_rparen()?;
                Command::Reset
            }
            "exit" => {
                self.expect_rparen()?;
                Command::Exit
            }
            _ => {
                // Skip unknown commands
                let mut depth = 1;
                while depth > 0 {
                    match self.advance() {
                        Some(Token::LParen) => depth += 1,
                        Some(Token::RParen) => depth -= 1,
                        None => break,
                        _ => {}
                    }
                }
                return self.parse_command();
            }
        };
        
        Ok(Some(cmd))
    }
    
    fn parse(&mut self) -> Result<SmtProblem, SmtLibError> {
        let mut problem = SmtProblem::new();
        
        while let Some(cmd) = self.parse_command()? {
            match &cmd {
                Command::SetLogic(logic) => {
                    problem.logic = Some(logic.clone());
                }
                Command::DeclareFun(decl) => {
                    problem.declarations.push(decl.clone());
                }
                Command::DefineFun(name, params, sort, body) => {
                    problem.definitions.insert(
                        name.clone(),
                        (params.clone(), sort.clone(), body.clone()),
                    );
                }
                Command::Assert(term) => {
                    problem.assertions.push(term.clone());
                }
                _ => {}
            }
            problem.commands.push(cmd);
        }
        
        Ok(problem)
    }
}

/// Parse SMT-LIB 2 input string.
pub fn parse_smtlib(input: &str) -> Result<SmtProblem, SmtLibError> {
    let mut lexer = Lexer::new(input);
    let tokens = lexer.tokenize()?;
    let mut parser = Parser::new(tokens);
    parser.parse()
}

/// Parse SMT-LIB 2 file.
pub fn parse_smtlib_file(path: &Path) -> Result<SmtProblem, SmtLibError> {
    let content = std::fs::read_to_string(path).map_err(|e| SmtLibError {
        message: format!("Failed to read file: {}", e),
        line: 0,
        column: 0,
    })?;
    parse_smtlib(&content)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty() {
        let problem = parse_smtlib("").unwrap();
        assert!(problem.assertions.is_empty());
    }

    #[test]
    fn test_parse_set_logic() {
        let problem = parse_smtlib("(set-logic QF_LIA)").unwrap();
        assert_eq!(problem.logic, Some(Logic::QfLia));
    }

    #[test]
    fn test_parse_declare_const() {
        let problem = parse_smtlib("(declare-const x Int)").unwrap();
        assert_eq!(problem.declarations.len(), 1);
        assert_eq!(problem.declarations[0].name, "x");
        assert_eq!(problem.declarations[0].return_sort, Sort::Int);
    }

    #[test]
    fn test_parse_declare_fun() {
        let problem = parse_smtlib("(declare-fun f (Int Int) Bool)").unwrap();
        assert_eq!(problem.declarations.len(), 1);
        assert_eq!(problem.declarations[0].name, "f");
        assert_eq!(problem.declarations[0].params.len(), 2);
        assert_eq!(problem.declarations[0].return_sort, Sort::Bool);
    }

    #[test]
    fn test_parse_assert_simple() {
        let problem = parse_smtlib("(assert true)").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        assert!(matches!(problem.assertions[0], Term::True));
    }

    #[test]
    fn test_parse_assert_and() {
        let problem = parse_smtlib("(assert (and true false))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        match &problem.assertions[0] {
            Term::And(args) => {
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected And"),
        }
    }

    #[test]
    fn test_parse_arithmetic() {
        let problem = parse_smtlib("(assert (> (+ x 1) 0))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        assert!(matches!(problem.assertions[0], Term::Gt(_, _)));
    }

    #[test]
    fn test_parse_bitvec_literal_hex() {
        let problem = parse_smtlib("(assert (= x #xFF))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        match &problem.assertions[0] {
            Term::Eq(_, b) => {
                match b.as_ref() {
                    Term::BitVecLit { value, width } => {
                        assert_eq!(*value, 255);
                        assert_eq!(*width, 8);
                    }
                    _ => panic!("Expected BitVecLit"),
                }
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_parse_bitvec_literal_binary() {
        let problem = parse_smtlib("(assert (= x #b1010))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        match &problem.assertions[0] {
            Term::Eq(_, b) => {
                match b.as_ref() {
                    Term::BitVecLit { value, width } => {
                        assert_eq!(*value, 10);
                        assert_eq!(*width, 4);
                    }
                    _ => panic!("Expected BitVecLit"),
                }
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_parse_bitvec_sort() {
        let problem = parse_smtlib("(declare-const x (_ BitVec 32))").unwrap();
        assert_eq!(problem.declarations.len(), 1);
        assert_eq!(problem.declarations[0].return_sort, Sort::BitVec(32));
    }

    #[test]
    fn test_parse_array_sort() {
        let problem = parse_smtlib("(declare-const a (Array Int Int))").unwrap();
        assert_eq!(problem.declarations.len(), 1);
        match &problem.declarations[0].return_sort {
            Sort::Array(idx, elem) => {
                assert_eq!(**idx, Sort::Int);
                assert_eq!(**elem, Sort::Int);
            }
            _ => panic!("Expected Array sort"),
        }
    }

    #[test]
    fn test_parse_select_store() {
        let problem = parse_smtlib("(assert (= (select (store a i v) i) v))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
    }

    #[test]
    fn test_parse_let() {
        let problem = parse_smtlib("(assert (let ((x 1) (y 2)) (= x y)))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        match &problem.assertions[0] {
            Term::Let(bindings, _) => {
                assert_eq!(bindings.len(), 2);
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_parse_ite() {
        let problem = parse_smtlib("(assert (ite true 1 0))").unwrap();
        assert_eq!(problem.assertions.len(), 1);
        assert!(matches!(problem.assertions[0], Term::Ite(_, _, _)));
    }

    #[test]
    fn test_parse_check_sat() {
        let problem = parse_smtlib("(check-sat)").unwrap();
        assert!(matches!(problem.commands.last(), Some(Command::CheckSat)));
    }

    #[test]
    fn test_parse_full_problem() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (declare-const y Int)
            (assert (> x 0))
            (assert (< y 10))
            (assert (= (+ x y) 15))
            (check-sat)
            (get-model)
        "#;
        let problem = parse_smtlib(input).unwrap();
        assert_eq!(problem.logic, Some(Logic::QfLia));
        assert_eq!(problem.declarations.len(), 2);
        assert_eq!(problem.assertions.len(), 3);
    }

    #[test]
    fn test_parse_comments() {
        let input = r#"
            ; This is a comment
            (set-logic QF_UF)
            ; Another comment
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        assert_eq!(problem.logic, Some(Logic::QfUf));
    }
}
