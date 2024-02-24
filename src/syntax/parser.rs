#![allow(dead_code)]

use super::lexer::{self, Span, Token, TokenSpan};
use crate::syntax::ast::*;
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

pub struct Parser<'src> {
    source: &'src str,
    tokens: Vec<TokenSpan>,
    cursor: usize,
}

type ParseFunc<'src, T> = fn(&mut Parser<'src>) -> Option<T>;

impl<'src> Parser<'src> {
    pub fn new(input: &'src str) -> Parser<'src> {
        let tokens = lexer::tokenize(input);
        Parser {
            source: input,
            tokens,
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

    fn peek_span_nth(&self, n: usize) -> &Span {
        if self.cursor + n < self.tokens.len() {
            &self.tokens[self.cursor + n].span
        } else {
            &self.tokens[self.tokens.len() - 1].span
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

    fn option<T, F: Fn(&mut Parser) -> Option<T>>(&mut self, func: F) -> Option<Option<T>> {
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

    fn surround<T, F: Fn(&mut Parser) -> Option<T>>(
        &mut self,
        left: Token,
        right: Token,
        func: F,
    ) -> Option<T> {
        self.match_token(left)?;
        let res = func(self)?;
        self.match_token(right)?;
        Some(res)
    }

    fn delimited_list<T, F: Fn(&mut Parser) -> Option<T>>(
        &mut self,
        left: Token,
        delim: Token,
        right: Token,
        func: F,
    ) -> Option<Vec<T>> {
        let mut vec: Vec<T> = Vec::new();
        self.match_token(left)?;
        if self.peek_token() == delim {
            self.next_token();
        }
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

    fn parse_lit_val(&mut self) -> Option<LitVal> {
        match self.peek_token() {
            Token::Int => {
                let x = self.peek_slice().parse::<i64>().unwrap();
                self.next_token();
                Some(LitVal::Int(x))
            }
            Token::Float => {
                let x = self.peek_slice().parse::<f64>().unwrap();
                self.next_token();
                Some(LitVal::Float(x))
            }
            Token::Bool => {
                let x = self.peek_slice().parse::<bool>().unwrap();
                self.next_token();
                Some(LitVal::Bool(x))
            }
            Token::Char => {
                let x = self.peek_slice().parse::<char>().unwrap();
                self.next_token();
                Some(LitVal::Char(x))
            }
            _tok => None,
        }
    }

    fn parse_llabel(&mut self) -> Option<InternStr> {
        match self.peek_token() {
            Token::LowerIdent => {
                let res = InternStr::new(&self.peek_slice());
                self.next_token();
                Some(res)
            }
            _tok => None,
        }
    }

    fn parse_ulabel(&mut self) -> Option<InternStr> {
        match self.peek_token() {
            Token::UpperIdent => {
                let res = InternStr::new(&self.peek_slice());
                self.next_token();
                Some(res)
            }
            _tok => None,
        }
    }

    fn parse_lident(&mut self) -> Option<Ident> {
        match self.peek_token() {
            Token::LowerIdent => {
                let res = Ident::dummy(&self.peek_slice());
                self.next_token();
                Some(res)
            }
            _tok => None,
        }
    }

    fn parse_uident(&mut self) -> Option<Ident> {
        match self.peek_token() {
            Token::UpperIdent => {
                let res = Ident::dummy(&self.peek_slice());
                self.next_token();
                Some(res)
            }
            _tok => None,
        }
    }

    fn parse_prim_opr(&mut self) -> Option<PrimOpr> {
        match self.peek_token() {
            Token::PrimOpr => {
                let s = self.peek_slice();
                self.next_token();
                match s {
                    "@iadd" => Some(PrimOpr::IAdd),
                    "@isub" => Some(PrimOpr::ISub),
                    "@imul" => Some(PrimOpr::IMul),
                    "@icmpls" => Some(PrimOpr::ICmpLs),
                    "@icmpeq" => Some(PrimOpr::ICmpEq),
                    "@icmpgr" => Some(PrimOpr::ICmpGr),
                    _s => None,
                }
            }
            _tok => None,
        }
    }

    fn parse_polyvars(&mut self) -> Option<Vec<Ident>> {
        self.option(|par| {
            par.delimited_list(Token::LBracket, Token::Comma, Token::RBracket, |par| {
                par.parse_uident()
            })
        })
        .map(|res| res.unwrap_or(Vec::new()))
    }

    fn parse_parameters(&mut self) -> Option<Vec<Ident>> {
        self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
            par.parse_lident()
        })
    }

    fn parse_expr_args(&mut self) -> Option<Vec<Expr>> {
        self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
            par.parse_expr()
        })
    }

    fn parse_expr(&mut self) -> Option<Expr> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Int | Token::Float | Token::Bool | Token::Char => {
                let lit = self.parse_lit_val()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Lit { lit, span })
            }
            Token::LowerIdent => {
                let ident = self.parse_lident()?;
                let end = self.end_pos();
                let span = Span { start, end };
                let var = Expr::Var { ident, span };
                if self.peek_token() == Token::LParen {
                    // for "f(42)" syntax
                    let func = Box::new(var);
                    let args = self.parse_expr_args()?;
                    let end = self.end_pos();
                    let span = Span { start, end };
                    Some(Expr::App { func, args, span })
                } else {
                    Some(var)
                }
            }
            Token::UpperIdent => {
                let cons = self.parse_uident()?;
                let flds = self.parse_labeled_list(
                    |par| par.parse_expr(),
                    Some(|s, span| Expr::Var {
                        ident: Ident::dummy(&s),
                        span,
                    }),
                )?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Cons { cons, flds, span })
            }
            Token::PrimOpr => {
                let prim = self.parse_prim_opr()?;
                let args = self.parse_expr_args()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Prim { prim, args, span })
            }
            Token::Fn => {
                self.match_token(Token::Fn)?;
                let pars = self.parse_parameters()?;
                self.match_token(Token::FatArrow)?;
                let body = Box::new(self.parse_expr()?);
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Func { pars, body, span })
            }
            Token::If => {
                self.match_token(Token::If)?;
                let cond = Box::new(self.parse_expr()?);
                self.match_token(Token::Then)?;
                let trbr = Box::new(self.parse_expr()?);
                self.match_token(Token::Else)?;
                let flbr = Box::new(self.parse_expr()?);
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Ifte {
                    cond,
                    trbr,
                    flbr,
                    span,
                })
            }
            Token::Match => {
                self.match_token(Token::Match)?;
                let expr = Box::new(self.parse_expr()?);
                let rules = self
                    .delimited_list(Token::With, Token::Bar, Token::End, |par| par.parse_rule())?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Expr::Case { expr, rules, span })
            }
            Token::Begin => self.parse_block(),
            Token::LParen => {
                let res = self.surround(Token::LParen, Token::RParen, |par| par.parse_expr())?;
                if self.peek_token() == Token::LParen {
                    // for "(fn(x) => x)(42)" syntax
                    let func = Box::new(res);
                    let args = self.parse_expr_args()?;
                    let end = self.end_pos();
                    let span = Span { start, end };
                    Some(Expr::App { func, args, span })
                } else {
                    Some(res)
                }
            }
            _tok => None,
        }
    }

    fn parse_stmt(&mut self) -> Option<Stmt> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Let => {
                self.match_token(Token::Let);
                let ident = self.parse_lident()?;
                let typ: Option<Type> = self.option(|par| {
                    par.match_token(Token::Colon)?;
                    par.parse_type()
                })?;
                self.match_token(Token::Equal);
                let expr = self.parse_expr()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Stmt::Let {
                    ident,
                    typ,
                    expr,
                    span,
                })
            }
            _tok => {
                let expr = self.parse_expr()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Stmt::Do { expr, span })
            }
        }
    }

    fn parse_labeled_list<T, F: Fn(&mut Parser) -> Option<T>>(
        &mut self,
        func: F,
        default: Option<fn(InternStr, Span) -> T>,
    ) -> Option<Vec<Labeled<T>>> {
        match self.peek_token() {
            Token::LBrace => {
                // Cons { fld1: Typ1, ..., fldn: Typn }
                let res =
                    self.delimited_list(Token::LBrace, Token::Comma, Token::RBrace, |par| {
                        let start = par.start_pos();
                        let label = par.parse_llabel()?;
                        if par.peek_token() == Token::Colon {
                            par.match_token(Token::Colon)?;
                            let data = func(par)?;
                            let end = par.end_pos();
                            let span = Span { start, end };
                            Some(Labeled { label, data, span })
                        } else {
                            if let Some(dft) = default {
                                let end = par.end_pos();
                                let span = Span { start, end };
                                let data = dft(label, span.clone());
                                Some(Labeled { label, data, span })
                            } else {
                                None
                            }
                        }
                    })?;
                Some(res)
            }
            Token::LParen => {
                // Cons(fld1, ..., fldn)
                let res: Vec<(T, Span)> =
                    self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
                        let start = par.start_pos();
                        let expr = func(par)?;
                        let end = par.end_pos();
                        let span = Span { start, end };
                        Some((expr, span))
                    })?;
                let res = res
                    .into_iter()
                    .enumerate()
                    .map(|(i, (expr, span))| Labeled {
                        label: InternStr::new(format!("@{}", i)),
                        data: expr,
                        span,
                    })
                    .collect();
                Some(res)
            }
            _tok => Some(Vec::new()),
        }
    }

    fn parse_rule(&mut self) -> Option<Rule> {
        let start = self.start_pos();
        let patn = self.parse_pattern()?;
        self.match_token(Token::FatArrow)?;
        let body = self.parse_expr()?;
        let end = self.end_pos();
        let span = Span { start, end };
        Some(Rule { patn, body, span })
    }

    fn parse_pattern(&mut self) -> Option<Pattern> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Int | Token::Float | Token::Bool | Token::Char => {
                let lit = self.parse_lit_val()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Pattern::Lit { lit, span })
            }
            Token::LowerIdent => {
                let ident = self.parse_lident()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Pattern::Var { ident, span })
            }
            Token::UpperIdent => {
                let cons = self.parse_uident()?;
                let patns = self.parse_labeled_list(
                    |par| par.parse_pattern(),
                    Some(|s, span| Pattern::Var {
                        ident: Ident::dummy(&s),
                        span,
                    }),
                )?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Pattern::Cons { cons, patns, span })
            }
            Token::Wild => {
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Pattern::Wild { span })
            }
            _tok => None,
        }
    }

    fn parse_block(&mut self) -> Option<Expr> {
        self.match_token(Token::Begin)?;
        let mut vec: Vec<Stmt> = Vec::new();
        loop {
            if self.peek_token() == Token::End {
                self.match_token(Token::End);
                let end = self.end_pos();
                let res = vec.into_iter().rev().fold(
                    Expr::Lit {
                        lit: LitVal::Unit,
                        span: Span { start: end, end },
                    },
                    |cont, stmt| {
                        let span = Span {
                            start: stmt.get_span().start,
                            end: cont.get_span().end,
                        };
                        Expr::Stmt {
                            stmt: Box::new(stmt),
                            cont: Box::new(cont),
                            span,
                        }
                    },
                );
                return Some(res);
            } else {
                let stmt = self.parse_stmt()?;
                match (stmt, self.peek_token()) {
                    (stmt, Token::Semi) => {
                        vec.push(stmt);
                        self.match_token(Token::Semi)?;
                        continue;
                    }
                    (Stmt::Do { expr, span: _ }, Token::End) => {
                        self.match_token(Token::End)?;
                        let res = vec.into_iter().rev().fold(expr, |cont, stmt| {
                            let span = Span {
                                start: stmt.get_span().start,
                                end: cont.get_span().end,
                            };
                            Expr::Stmt {
                                stmt: Box::new(stmt),
                                cont: Box::new(cont),
                                span,
                            }
                        });
                        return Some(res);
                    }
                    _tok => return None,
                }
            }
        }
    }

    fn parse_type(&mut self) -> Option<Type> {
        match self.peek_token() {
            Token::TyInt => {
                self.match_token(Token::TyInt)?;
                Some(Type::Lit {
                    lit: LitType::TyInt,
                })
            }
            Token::TyFloat => {
                self.match_token(Token::TyFloat)?;
                Some(Type::Lit {
                    lit: LitType::TyFloat,
                })
            }
            Token::TyBool => {
                self.match_token(Token::TyBool)?;
                Some(Type::Lit {
                    lit: LitType::TyBool,
                })
            }
            Token::TyChar => {
                self.match_token(Token::TyChar)?;
                Some(Type::Lit {
                    lit: LitType::TyChar,
                })
            }
            Token::UpperIdent => {
                let ident = self.parse_uident()?;
                if self.peek_token() == Token::LBracket {
                    let args = self.delimited_list(
                        Token::LBracket,
                        Token::Comma,
                        Token::RBracket,
                        |par| par.parse_type(),
                    )?;
                    Some(Type::Cons { cons: ident, args })
                } else {
                    Some(Type::Var { ident })
                }
            }
            Token::Fn => {
                self.match_token(Token::Fn)?;
                let pars =
                    self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
                        par.parse_type()
                    })?;
                if self.peek_token() == Token::Arrow {
                    self.match_token(Token::Arrow)?;
                    let res = Box::new(self.parse_type()?);
                    Some(Type::Func { pars, res })
                } else {
                    let res = Box::new(Type::Lit {
                        lit: LitType::TyUnit,
                    });
                    Some(Type::Func { pars, res })
                }
            }
            _tok => None,
        }
    }

    fn parse_varient(&mut self) -> Option<Varient> {
        let start = self.start_pos();
        let cons = self.parse_uident()?;
        let flds = self.parse_labeled_list(|par| par.parse_type(), None)?;
        let end = self.end_pos();
        let span = Span { start, end };
        Some(Varient { cons, flds, span })
    }

    fn parse_decl(&mut self) -> Option<Decl> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Function => {
                self.match_token(Token::Function)?;
                let ident = self.parse_lident()?;
                let polys = self.parse_polyvars()?;
                let pars =
                    self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
                        let ident = par.parse_lident()?;
                        par.match_token(Token::Colon)?;
                        let typ = par.parse_type()?;
                        Some((ident, typ))
                    })?;
                let res = self
                    .option(|par| {
                        par.match_token(Token::Arrow)?;
                        par.parse_type()
                    })?
                    .unwrap_or(Type::Lit {
                        lit: LitType::TyUnit,
                    });
                let end1 = self.end_pos();
                let span1 = Span { start, end: end1 };
                let body = self.parse_block()?;
                let end2 = self.end_pos();
                let span2 = Span { start, end: end2 };
                Some(Decl::Func {
                    ident,
                    pars,
                    polys,
                    res,
                    span1,
                    body,
                    span2,
                })
            }
            Token::Datatype => {
                self.match_token(Token::Datatype)?;
                let ident = self.parse_uident()?;
                let polys = self.parse_polyvars()?;
                let vars = self.delimited_list(Token::Where, Token::Bar, Token::End, |par| {
                    par.parse_varient()
                })?;
                let end = self.end_pos();
                let span = Span { start, end };
                Some(Decl::Data {
                    ident,
                    polys,
                    vars,
                    span,
                })
            }
            _tok => None,
        }
    }

    fn parse_module(&mut self) -> Option<Module> {
        self.match_token(Token::Module)?;
        let name = self.parse_uident()?;
        self.match_token(Token::Where)?;
        let mut decls: Vec<Decl> = Vec::new();
        loop {
            match self.peek_token() {
                Token::Function | Token::Datatype => {
                    let res = self.parse_decl()?;
                    decls.push(res)
                }
                _tok => break,
            }
        }
        self.match_token(Token::EndOfFile)?;
        Some(Module { name, decls })
    }
}

pub fn parse_expr<'src>(s: &'src str) -> Option<Expr> {
    let mut par = Parser::new(s);
    let res = par.parse_expr();
    res
}

pub fn parse_module<'src>(s: &'src str) -> Option<Module> {
    let mut par = Parser::new(s);
    let res = par.parse_module();
    res
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
module Test where
datatype List[T] where
| Nil
| Cons(T, List[T])
end
function map[T, U](f: fn(T) -> U, xs: List[T]) -> List[U]
begin
    match xs with
    | Nil => Nil
    | Cons(x, xs) => Cons(f(x), map(f,xs))
    end
end
datatype Listt[T] where
| Nill
| Conss { head: T, tail: Listt[T] }
end
function mapp[T, U](f: fn(T) -> U, xs: List[T]) -> List[U]
begin
    match xs with
    | Nill => Nill
    | Conss { head, tail } => 
        Conss { head: f(head), tail: mapp(f,tail) }
    end
end
function f(x: Int) -> Int
begin
    let f = fn(x) => @iadd(x,1);
    let res = f(42);
    let test = if @icmpls(1, 2) then 3 else 4;
    res
end
function g(x: Int) -> Int
begin
    let r = @iadd(x, 1);
    r
end
function id[T](x: T) -> T
begin
    x
end
"#;
    let mut par = Parser::new(s);
    let res = par.parse_module().unwrap();
    println!("{:#?}", res);
}
