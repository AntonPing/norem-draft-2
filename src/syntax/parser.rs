#![allow(dead_code)]

use super::lexer::{self, Span, Token, TokenSpan};
use crate::syntax::ast::*;
use crate::utils::ident::Ident;

pub struct Parser<'src> {
    source: &'src str,
    tokens: Vec<TokenSpan>,
    cursor: usize,
}

type ParseFunc<T> = fn(&mut Parser) -> Option<T>;

impl<'src> Parser<'src> {
    pub fn new(input: &'src str) -> Parser<'src> {
        let tokens = lexer::tokenize(input);
        Parser {
            source: input,
            tokens: tokens,
            cursor: 0,
        }
    }

    fn peek_token_span(&self) -> &TokenSpan {
        &self.tokens[self.cursor]
    }

    fn peek_token(&self) -> Token {
        self.tokens[self.cursor].token
    }

    fn peek_token_nth(&self, n: usize) -> Token {
        if self.cursor + n < self.tokens.len() {
            self.tokens[self.cursor + n].token
        } else {
            Token::EndOfFile
        }
    }

    fn peek_span(&self) -> &Span {
        &self.tokens[self.cursor].span
    }

    fn peek_span_nth(&self, n: usize) -> Span {
        if self.cursor + n < self.tokens.len() {
            self.tokens[self.cursor + n].span.clone()
        } else {
            self.tokens[self.tokens.len() - 1].span.clone()
        }
    }

    fn peek_slice(&self) -> &'src str {
        let span = &self.tokens[self.cursor].span;
        &self.source[span.start..span.end]
    }

    fn start_pos(&self) -> usize {
        self.tokens[self.cursor].span.start
    }

    fn end_pos(&self) -> usize {
        self.tokens[self.cursor - 1].span.end
    }

    fn next_token(&mut self) -> &TokenSpan {
        let tok = &self.tokens[self.cursor];
        if self.cursor < self.tokens.len() - 1 {
            self.cursor += 1;
        }
        tok
    }

    fn match_token(&mut self, tok: Token) -> Option<()> {
        if self.peek_token() == tok {
            self.next_token();
            Some(())
        } else {
            None
        }
    }

    fn option<T>(&mut self, func: ParseFunc<T>) -> Option<Option<T>> {
        let last = self.cursor;
        match func(self) {
            Some(res) => Some(Some(res)),
            None => {
                // if it failed without consuming any token
                if self.cursor == last {
                    Some(None) // return None
                } else {
                    None // otherwise fail
                }
            }
        }
    }

    fn surround<T>(&mut self, left: Token, right: Token, func: ParseFunc<T>) -> Option<T> {
        self.match_token(left)?;
        let res = func(self)?;
        self.match_token(right)?;
        Some(res)
    }

    fn delimited_list<T>(
        &mut self,
        left: Token,
        delim: Token,
        right: Token,
        func: ParseFunc<T>,
    ) -> Option<Vec<T>> {
        let mut vec: Vec<T> = Vec::new();
        self.match_token(left)?;
        if self.peek_token() == right {
            self.next_token();
            return Some(vec);
        }
        vec.push(func(self)?);
        while self.peek_token() == delim {
            self.next_token();
            vec.push(func(self)?);
        }
        // allow trailing delimiter
        if self.peek_token() == delim {
            self.next_token();
        }
        self.match_token(right)?;
        Some(vec)
    }
}

fn parse_lit_val(par: &mut Parser) -> Option<LitVal> {
    match par.peek_token() {
        Token::Int => {
            let x = par.peek_slice().parse::<i64>().unwrap();
            par.next_token();
            Some(LitVal::Int(x))
        }
        Token::Float => {
            let x = par.peek_slice().parse::<f64>().unwrap();
            par.next_token();
            Some(LitVal::Float(x))
        }
        Token::Bool => {
            let x = par.peek_slice().parse::<bool>().unwrap();
            par.next_token();
            Some(LitVal::Bool(x))
        }
        Token::Char => {
            let x = par.peek_slice().parse::<char>().unwrap();
            par.next_token();
            Some(LitVal::Char(x))
        }
        _tok => None,
    }
}

fn parse_ident(par: &mut Parser) -> Option<Ident> {
    match par.peek_token() {
        Token::LowerIdent => {
            let res = Ident::dummy(&par.peek_slice());
            par.next_token();
            Some(res)
        }
        _tok => None,
    }
}

fn parse_prim_opr(par: &mut Parser) -> Option<PrimOpr> {
    match par.peek_token() {
        Token::PrimOpr => {
            let s = par.peek_slice();
            par.next_token();
            match s {
                "@iadd" => Some(PrimOpr::IAdd),
                "@isub" => Some(PrimOpr::ISub),
                "@imul" => Some(PrimOpr::IMul),
                _s => None,
            }
        }
        _tok => None,
    }
}

fn parse_parameters(par: &mut Parser) -> Option<Vec<Ident>> {
    par.delimited_list(Token::LParen, Token::Comma, Token::RParen, parse_ident)
}

fn parse_expr_args(par: &mut Parser) -> Option<Vec<Expr>> {
    par.delimited_list(Token::LParen, Token::Comma, Token::RParen, parse_expr)
}

fn parse_expr(par: &mut Parser) -> Option<Expr> {
    let start = par.start_pos();
    match par.peek_token() {
        Token::Int | Token::Float | Token::Bool | Token::Char => {
            let lit = parse_lit_val(par)?;
            let end = par.end_pos();
            let span = Span { start, end };
            Some(Expr::Lit { lit, span })
        }
        Token::LowerIdent => {
            let ident = parse_ident(par)?;
            let end = par.end_pos();
            let span = Span { start, end };
            let var = Expr::Var { ident, span };
            if par.peek_token() == Token::LParen {
                // for "f(42)" syntax
                let func = Box::new(var);
                let args = parse_expr_args(par)?;
                let end = par.end_pos();
                let span = Span { start, end };
                Some(Expr::App { func, args, span })
            } else {
                Some(var)
            }
        }
        Token::PrimOpr => {
            let prim = parse_prim_opr(par)?;
            let args = parse_expr_args(par)?;
            let end = par.end_pos();
            let span = Span { start, end };
            Some(Expr::Prim { prim, args, span })
        }
        Token::Fn => {
            par.match_token(Token::Fn)?;
            let pars = parse_parameters(par)?;
            par.match_token(Token::FatArrow)?;
            let body = Box::new(parse_expr(par)?);
            let end = par.end_pos();
            let span = Span { start, end };
            Some(Expr::Func { pars, body, span })
        }
        Token::LParen => {
            let res = par.surround(Token::LParen, Token::RParen, parse_expr)?;
            if par.peek_token() == Token::LParen {
                // for "(fn(x) => x)(42)" syntax
                let func = Box::new(res);
                let args = parse_expr_args(par)?;
                let end = par.end_pos();
                let span = Span { start, end };
                Some(Expr::App { func, args, span })
            } else {
                Some(res)
            }
        }
        _tok => None,
    }
}

#[test]
#[ignore = "just to see result"]
fn parser_test() {
    let s = r#"
// test line comment
/*
    /*
        test block comment
    */
*/
(fn(x) => (@iadd(x,1)))(42)
"#;

    let mut par = Parser::new(s);
    let res = parse_expr(&mut par);
    if let Some(res) = res {
        println!("{:#?}", res);
    } else {
        panic!("parse failed")
    }
}
