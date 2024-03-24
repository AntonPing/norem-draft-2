#![allow(dead_code)]

use super::lexer::{self, Span, Token, TokenSpan};
use crate::analyze::diagnostic::Diagnostic;
use crate::syntax::ast::*;
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

pub struct Parser<'src, 'diag> {
    source: &'src str,
    tokens: Vec<TokenSpan>,
    cursor: usize,
    diags: &'diag mut Vec<Diagnostic>,
}

#[derive(Debug, Clone)]
enum ParseError {
    LexerError(Span),
    FailedToMatch(Token, Token, Span),
    FailedToParse(&'static str, Token, Span),
    NotALeftValue(Span),
}
type ParseResult<T> = Result<T, ParseError>;

type ParseFunc<'src, 'diag, T> = fn(&mut Parser<'src, 'diag>) -> ParseResult<T>;

impl<'src, 'diag> Parser<'src, 'diag> {
    pub fn new(src: &'src str, diags: &'diag mut Vec<Diagnostic>) -> Parser<'src, 'diag> {
        let tokens = lexer::tokenize(src);
        Parser {
            source: src,
            tokens,
            cursor: 0,
            diags,
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

    fn emit(&mut self, err: &ParseError) {
        match err {
            ParseError::LexerError(span) => self.diags.push(
                Diagnostic::error("cannot scan next token!")
                    .line_span(span.clone(), "here is the bad token"),
            ),
            ParseError::FailedToMatch(expect, found, span) => {
                self.diags
                    .push(Diagnostic::error("cannot match token!").line_span(
                        span.clone(),
                        format!("expect token {expect:?}, found token {found:?}"),
                    ))
            }
            ParseError::FailedToParse(name, found, span) => self.diags.push(
                Diagnostic::error(format!("cannot parse {name}!"))
                    .line_span(span.clone(), format!("found token {found:?}")),
            ),
            ParseError::NotALeftValue(span) => self.diags.push(
                Diagnostic::error(format!("left hand side of assignment is not a left value!"))
                    .line_span(span.clone(), "here is the left hand side expression"),
            ),
        }
    }

    fn next_token(&mut self) -> ParseResult<&TokenSpan> {
        let tok = &self.tokens[self.cursor];
        if tok.token == Token::TokError {
            Err(ParseError::LexerError(self.peek_span().clone()))
        } else {
            if self.cursor < self.tokens.len() - 1 {
                self.cursor += 1;
            }
            Ok(tok)
        }
    }

    fn match_token(&mut self, tok: Token) -> ParseResult<()> {
        if self.peek_token() == tok {
            self.next_token()?;
            Ok(())
        } else {
            Err(ParseError::FailedToMatch(
                tok,
                self.peek_token(),
                self.peek_span().clone(),
            ))
        }
    }

    fn option<T, F>(&mut self, func: F) -> ParseResult<Option<T>>
    where
        F: Fn(&mut Parser) -> ParseResult<T>,
    {
        let last = self.cursor;
        match func(self) {
            Ok(res) => Ok(Some(res)),
            Err(err) => {
                // if it failed without consuming any token
                if self.cursor == last {
                    Ok(None) // return Err(ParseError::FailedToParse((), self.peek_token(), self.peek_span().clone()))
                } else {
                    Err(err) // otherwise fail
                }
            }
        }
    }

    fn surround<T, F>(&mut self, left: Token, right: Token, func: F) -> ParseResult<T>
    where
        F: Fn(&mut Parser) -> ParseResult<T>,
    {
        self.match_token(left)?;
        let res = func(self)?;
        self.match_token(right)?;
        Ok(res)
    }

    fn delimited_list<T, F>(
        &mut self,
        left: Token,
        delim: Token,
        right: Token,
        func: F,
    ) -> ParseResult<Vec<T>>
    where
        F: Fn(&mut Parser) -> ParseResult<T>,
    {
        let mut vec: Vec<T> = Vec::new();
        self.match_token(left)?;
        // allow leading delimiter
        if self.peek_token() == delim {
            self.next_token()?;
        }
        // allow empty list
        if self.peek_token() == right {
            self.next_token()?;
            return Ok(vec);
        }
        vec.push(func(self)?);
        while self.peek_token() == delim {
            self.next_token()?;
            vec.push(func(self)?);
        }
        // allow trailing delimiter
        if self.peek_token() == delim {
            self.next_token()?;
        }
        self.match_token(right)?;
        Ok(vec)
    }

    fn parse_lit_val(&mut self) -> ParseResult<LitVal> {
        match self.peek_token() {
            Token::Int => {
                let x = self.peek_slice().parse::<i64>().unwrap();
                self.next_token()?;
                Ok(LitVal::Int(x))
            }
            Token::Float => {
                let x = self.peek_slice().parse::<f64>().unwrap();
                self.next_token()?;
                Ok(LitVal::Float(x))
            }
            Token::Bool => {
                let x = self.peek_slice().parse::<bool>().unwrap();
                self.next_token()?;
                Ok(LitVal::Bool(x))
            }
            Token::Char => {
                let x = self.peek_slice().parse::<char>().unwrap();
                self.next_token()?;
                Ok(LitVal::Char(x))
            }
            _tok => Err(ParseError::FailedToParse(
                &"literal",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_llabel(&mut self) -> ParseResult<InternStr> {
        match self.peek_token() {
            Token::LowerIdent => {
                let res = InternStr::new(&self.peek_slice());
                self.next_token()?;
                Ok(res)
            }
            _tok => Err(ParseError::FailedToParse(
                &"lowercase label",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_ulabel(&mut self) -> ParseResult<InternStr> {
        match self.peek_token() {
            Token::UpperIdent => {
                let res = InternStr::new(&self.peek_slice());
                self.next_token()?;
                Ok(res)
            }
            _tok => Err(ParseError::FailedToParse(
                &"uppercase label",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_lident(&mut self) -> ParseResult<Ident> {
        match self.peek_token() {
            Token::LowerIdent => {
                let res = Ident::dummy(&self.peek_slice());
                self.next_token()?;
                Ok(res)
            }
            _tok => Err(ParseError::FailedToParse(
                "lowercase identifier",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_uident(&mut self) -> ParseResult<Ident> {
        match self.peek_token() {
            Token::UpperIdent => {
                let res = Ident::dummy(&self.peek_slice());
                self.next_token()?;
                Ok(res)
            }
            _tok => Err(ParseError::FailedToParse(
                "uppercase identifier",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_prim_opr(&mut self) -> ParseResult<PrimOpr> {
        match self.peek_token() {
            Token::PrimOpr => {
                let s = self.peek_slice();
                self.next_token()?;
                match s {
                    "@iadd" => Ok(PrimOpr::IAdd),
                    "@isub" => Ok(PrimOpr::ISub),
                    "@imul" => Ok(PrimOpr::IMul),
                    "@icmpls" => Ok(PrimOpr::ICmpLs),
                    "@icmpeq" => Ok(PrimOpr::ICmpEq),
                    "@icmpgr" => Ok(PrimOpr::ICmpGr),
                    _ => unreachable!(),
                }
            }
            _tok => Err(ParseError::FailedToParse(
                "primitive operator",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_polyvars(&mut self) -> ParseResult<Vec<Ident>> {
        self.option(|par| {
            par.delimited_list(Token::LBracket, Token::Comma, Token::RBracket, |par| {
                par.parse_uident()
            })
        })
        .map(|res| res.unwrap_or(Vec::new()))
    }

    fn parse_parameters(&mut self) -> ParseResult<Vec<Ident>> {
        self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
            par.parse_lident()
        })
    }

    fn parse_expr_args(&mut self) -> ParseResult<Vec<Expr>> {
        self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
            par.parse_expr()
        })
    }

    // parse_expr calls parse_expr2, and parse_expr2 calls parse_expr3
    fn parse_expr(&mut self) -> ParseResult<Expr> {
        let mut expr_stack: Vec<Expr> = Vec::new();
        let mut opr_stack: Vec<PrimOpr> = Vec::new();

        fn get_prior(opr: &PrimOpr) -> usize {
            match opr {
                PrimOpr::IAdd => 10,
                PrimOpr::ISub => 10,
                PrimOpr::IMul => 20,
                PrimOpr::ICmpLs => 5,
                PrimOpr::ICmpEq => 5,
                PrimOpr::ICmpGr => 5,
            }
        }

        fn squash(expr_stack: &mut Vec<Expr>, opr_stack: &mut Vec<PrimOpr>) {
            let rhs = expr_stack.pop().unwrap();
            let opr = opr_stack.pop().unwrap();
            let lhs = expr_stack.pop().unwrap();
            let span = Span {
                start: lhs.get_span().start,
                end: rhs.get_span().end,
            };
            let new_expr = Expr::Prim {
                prim: opr,
                args: vec![lhs, rhs],
                span,
            };
            expr_stack.push(new_expr);
        }

        loop {
            let expr = self.parse_expr2()?;
            expr_stack.push(expr);
            let opr = match self.peek_token() {
                Token::Plus => PrimOpr::IAdd,
                Token::Minus => PrimOpr::ISub,
                Token::Star => PrimOpr::IMul,
                Token::Less => PrimOpr::ICmpLs,
                Token::EqualEqual => PrimOpr::ICmpEq,
                Token::Greater => PrimOpr::ICmpGr,
                _ => {
                    while !opr_stack.is_empty() {
                        squash(&mut expr_stack, &mut opr_stack);
                    }
                    assert_eq!(expr_stack.len(), 1);
                    return Ok(expr_stack.pop().unwrap());
                }
            };
            while !opr_stack.is_empty() {
                let opr2 = opr_stack.last().unwrap();
                if get_prior(&opr2) > get_prior(&opr) {
                    squash(&mut expr_stack, &mut opr_stack);
                } else {
                    break;
                }
            }
            opr_stack.push(opr);
            self.next_token()?;
        }
    }

    fn parse_expr2(&mut self) -> ParseResult<Expr> {
        let start = self.start_pos();
        let mut expr = self.parse_expr3()?;
        loop {
            match self.peek_token() {
                Token::LParen => {
                    let args = self.parse_expr_args()?;
                    let end = self.end_pos();
                    let span = Span { start, end };
                    let new_expr = Expr::App {
                        func: Box::new(expr),
                        args,
                        span,
                    };
                    expr = new_expr;
                }
                Token::Dot => {
                    self.match_token(Token::Dot)?;
                    let field = self.parse_llabel()?;
                    let end = self.end_pos();
                    let span = Span { start, end };
                    let new_expr = Expr::Field {
                        expr: Box::new(expr),
                        field,
                        cons_info: None,
                        span,
                    };
                    expr = new_expr;
                }
                _ => {
                    break;
                }
            }
        }
        Ok(expr)
    }

    fn parse_expr3(&mut self) -> ParseResult<Expr> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Int | Token::Float | Token::Bool | Token::Char => {
                let lit = self.parse_lit_val()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Expr::Lit { lit, span })
            }
            Token::LowerIdent => {
                let ident = self.parse_lident()?;
                let end = self.end_pos();
                let span = Span { start, end };
                let var = Expr::Var { ident, span };
                Ok(var)
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
                Ok(Expr::Cons { cons, flds, span })
            }
            Token::PrimOpr => {
                let prim = self.parse_prim_opr()?;
                let args = self.parse_expr_args()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Expr::Prim { prim, args, span })
            }
            Token::Fn => {
                self.match_token(Token::Fn)?;
                let pars = self.parse_parameters()?;
                self.match_token(Token::FatArrow)?;
                let body = Box::new(self.parse_expr()?);
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Expr::Func { pars, body, span })
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
                Ok(Expr::Ifte {
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
                Ok(Expr::Case { expr, rules, span })
            }
            Token::Ref => {
                self.match_token(Token::Ref)?;
                let expr = Box::new(self.parse_expr()?);
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Expr::NewRef { expr, span })
            }
            Token::Caret => {
                self.match_token(Token::Caret)?;
                let expr = Box::new(self.parse_expr3()?);
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Expr::RefGet { expr, span })
            }
            Token::Begin => self.parse_block(Token::Begin),
            Token::LParen => self.surround(Token::LParen, Token::RParen, |par| par.parse_expr()),
            _tok => Err(ParseError::FailedToParse(
                "expression",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_stmt(&mut self) -> ParseResult<Stmt> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Let => {
                self.match_token(Token::Let)?;
                let ident = self.parse_lident()?;
                let typ: Option<Type> = self.option(|par| {
                    par.match_token(Token::Colon)?;
                    par.parse_type()
                })?;
                self.match_token(Token::Equal)?;
                let expr = self.parse_expr()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Stmt::Let {
                    ident,
                    typ,
                    expr,
                    span,
                })
            }
            Token::While => {
                self.match_token(Token::While)?;
                let cond = self.parse_expr()?;
                let body = self.parse_block(Token::Do)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Stmt::While { cond, body, span })
            }
            _tok => {
                let expr = self.parse_expr()?;

                match self.peek_token() {
                    Token::LeftArrow => {
                        self.match_token(Token::LeftArrow)?;
                        let expr2 = self.parse_expr()?;
                        let end = self.end_pos();
                        let span = Span { start, end };
                        Ok(Stmt::RefSet {
                            lhs: expr,
                            rhs: expr2,
                            span,
                        })
                    }
                    Token::ColonEqual => {
                        self.match_token(Token::ColonEqual)?;
                        let expr2 = self.parse_expr()?;
                        let end = self.end_pos();
                        let span = Span { start, end };
                        if matches!(expr, Expr::Field { .. }) {
                            Ok(Stmt::Assign {
                                lhs: expr,
                                rhs: expr2,
                                span,
                            })
                        } else {
                            Err(ParseError::NotALeftValue(expr.get_span().clone()))
                        }
                    }
                    _ => {
                        let end = self.end_pos();
                        let span = Span { start, end };
                        Ok(Stmt::Do { expr, span })
                    }
                }
            }
        }
    }

    fn parse_labeled_list<T, F>(
        &mut self,
        func: F,
        default: Option<fn(InternStr, Span) -> T>,
    ) -> ParseResult<Vec<Labeled<T>>>
    where
        F: Fn(&mut Parser) -> ParseResult<T>,
    {
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
                            Ok(Labeled { label, data, span })
                        } else {
                            if let Some(dft) = default {
                                let end = par.end_pos();
                                let span = Span { start, end };
                                let data = dft(label, span.clone());
                                Ok(Labeled { label, data, span })
                            } else {
                                Err(ParseError::FailedToParse(
                                    "labeled list",
                                    par.peek_token(),
                                    par.peek_span().clone(),
                                ))
                            }
                        }
                    })?;
                Ok(res)
            }
            Token::LParen => {
                // Cons(fld1, ..., fldn)
                let res: Vec<(T, Span)> =
                    self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
                        let start = par.start_pos();
                        let expr = func(par)?;
                        let end = par.end_pos();
                        let span = Span { start, end };
                        Ok((expr, span))
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
                Ok(res)
            }
            _tok => Ok(Vec::new()),
        }
    }

    fn parse_rule(&mut self) -> ParseResult<Rule> {
        let start = self.start_pos();
        let patn = self.parse_pattern()?;
        self.match_token(Token::FatArrow)?;
        let body = self.parse_expr()?;
        let end = self.end_pos();
        let span = Span { start, end };
        Ok(Rule { patn, body, span })
    }

    fn parse_pattern(&mut self) -> ParseResult<Pattern> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Int | Token::Float | Token::Bool | Token::Char => {
                let lit = self.parse_lit_val()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Pattern::Lit { lit, span })
            }
            Token::LowerIdent => {
                let ident = self.parse_lident()?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Pattern::Var { ident, span })
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
                let as_ident = self.option(|par| {
                    par.match_token(Token::As)?;
                    par.parse_lident()
                })?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Pattern::Cons {
                    cons,
                    patns,
                    as_ident,
                    span,
                })
            }
            Token::Wild => {
                self.match_token(Token::Wild)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Pattern::Wild { span })
            }
            _tok => Err(ParseError::FailedToParse(
                "pattern",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_block(&mut self, start: Token) -> ParseResult<Expr> {
        self.match_token(start)?;
        let mut vec: Vec<Stmt> = Vec::new();
        loop {
            if self.peek_token() == Token::End {
                self.match_token(Token::End)?;
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
                return Ok(res);
            } else {
                let stmt = self.parse_stmt()?;
                match (stmt, self.peek_token()) {
                    (stmt, Token::Semi) => {
                        self.match_token(Token::Semi)?;
                        vec.push(stmt);
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
                        return Ok(res);
                    }
                    (_stmt, _tok) => {
                        return Err(ParseError::FailedToMatch(
                            Token::Semi,
                            self.peek_token(),
                            self.peek_span().clone(),
                        ))
                    }
                }
            }
        }
    }

    fn parse_type(&mut self) -> ParseResult<Type> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::TyInt => {
                self.match_token(Token::TyInt)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Lit {
                    lit: LitType::TyInt,
                    span,
                })
            }
            Token::TyFloat => {
                self.match_token(Token::TyFloat)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Lit {
                    lit: LitType::TyFloat,
                    span,
                })
            }
            Token::TyBool => {
                self.match_token(Token::TyBool)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Lit {
                    lit: LitType::TyBool,
                    span,
                })
            }
            Token::TyChar => {
                self.match_token(Token::TyChar)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Lit {
                    lit: LitType::TyChar,
                    span,
                })
            }
            Token::TyUnit => {
                self.match_token(Token::TyUnit)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Lit {
                    lit: LitType::TyUnit,
                    span,
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
                    let end = self.end_pos();
                    let span = Span { start, end };
                    Ok(Type::Cons {
                        cons: ident,
                        args,
                        span,
                    })
                } else {
                    let end = self.end_pos();
                    let span = Span { start, end };
                    Ok(Type::Var { ident, span })
                }
            }
            Token::Fn => {
                self.match_token(Token::Fn)?;
                let pars =
                    self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
                        par.parse_type()
                    })?;
                let res = if self.peek_token() == Token::Arrow {
                    self.match_token(Token::Arrow)?;
                    Box::new(self.parse_type()?)
                } else {
                    let pos = self.end_pos();
                    let span = Span {
                        start: pos,
                        end: pos,
                    };
                    Box::new(Type::Lit {
                        lit: LitType::TyUnit,
                        span,
                    })
                };
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Type::Func { pars, res, span })
            }
            _tok => Err(ParseError::FailedToParse(
                "type",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_varient(&mut self) -> ParseResult<Varient> {
        let start = self.start_pos();
        let cons = self.parse_uident()?;
        let flds = self.parse_labeled_list(|par| par.parse_type(), None)?;
        let end = self.end_pos();
        let span = Span { start, end };
        Ok(Varient { cons, flds, span })
    }

    fn parse_func_sign(&mut self) -> ParseResult<FuncSign> {
        let start = self.start_pos();
        self.match_token(Token::Function)?;
        let func = self.parse_lident()?;
        let polys = self.parse_polyvars()?;
        let pars = self.delimited_list(Token::LParen, Token::Comma, Token::RParen, |par| {
            let ident = par.parse_lident()?;
            par.match_token(Token::Colon)?;
            let typ = par.parse_type()?;
            Ok((ident, typ))
        })?;
        let res = self
            .option(|par| {
                par.match_token(Token::Arrow)?;
                par.parse_type()
            })?
            .unwrap_or_else(|| {
                let pos = self.end_pos();
                let span = Span {
                    start: pos,
                    end: pos,
                };
                Type::Lit {
                    lit: LitType::TyUnit,
                    span,
                }
            });
        let end = self.end_pos();
        let span = Span { start, end };
        Ok(FuncSign {
            func,
            polys,
            pars,
            res,
            span,
        })
    }

    fn parse_decl(&mut self) -> ParseResult<Decl> {
        let start = self.start_pos();
        match self.peek_token() {
            Token::Function => {
                let sign = self.parse_func_sign()?;
                let body = self.parse_block(Token::Begin)?;
                let end = self.end_pos();
                let span = Span { start, end };
                Ok(Decl::Func { sign, body, span })
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
                Ok(Decl::Data {
                    ident,
                    polys,
                    vars,
                    span,
                })
            }
            _tok => Err(ParseError::FailedToParse(
                "declaration",
                self.peek_token(),
                self.peek_span().clone(),
            )),
        }
    }

    fn parse_module(&mut self) -> ParseResult<Module> {
        self.match_token(Token::Module)?;
        let name = self.parse_uident()?;
        self.match_token(Token::Where)?;
        let mut decls: Vec<Decl> = Vec::new();
        loop {
            match self.peek_token() {
                Token::Function | Token::Datatype => {
                    // toplevel error recovering
                    match self.parse_decl() {
                        Ok(res) => decls.push(res),
                        Err(err) => {
                            self.emit(&err);
                            while matches!(
                                self.peek_token(),
                                Token::Function | Token::Datatype | Token::EndOfFile
                            ) {
                                self.next_token()?;
                            }
                        }
                    }
                }
                _tok => break,
            }
        }
        self.match_token(Token::EndOfFile)?;
        Ok(Module { name, decls })
    }
}

pub fn parse_expr<'src, 'diag>(src: &'src str, diags: &'diag mut Vec<Diagnostic>) -> Option<Expr> {
    let mut par = Parser::new(src, diags);
    let res = par.parse_expr();
    res.ok()
}

pub fn parse_module<'src, 'diag>(
    src: &'src str,
    diags: &'diag mut Vec<Diagnostic>,
) -> Option<Module> {
    let mut par = Parser::new(src, diags);
    let res = par.parse_module();
    res.ok()
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
datatype List2[T] where
| Nil2
| Cons2 { head: T, tail: List2[T] }
end
function map2[T, U](f: fn(T) -> U, xs: List2[T]) -> List2[U]
begin
    match xs with
    | Nil2 => Nil2
    | Cons2 { head, tail } => 
        Cons2 { head: f(head), tail: map2(f,tail) }
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
    let r = x + 1;
    r
end
function id[T](x: T) -> T
begin
    let r = ref 42;
    while true do
        r := x;
    end;
    ^r
end
"#;
    let mut diags = Vec::new();
    let mut par = Parser::new(s, &mut diags);
    match par.parse_module() {
        Ok(res) => {
            assert!(diags.is_empty());
            println!("{:#?}", res);
        }
        Err(err) => {
            println!("{:#?}", err);
        }
    }
    for diag in diags {
        println!("{}", diag.report(s, 10));
    }
}
