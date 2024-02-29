use super::anf::*;
use crate::utils::ident::Ident;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{alpha1, digit1};
use nom::combinator::{map, opt, value};
use nom::multi::{many0, separated_list0};
use nom::IResult;

fn is_space_or_newline(ch: char) -> bool {
    match ch {
        ' ' | '\t' | '\n' | '\r' => true,
        _ => false,
    }
}

fn skip_space(input: &str) -> IResult<&str, &str> {
    take_while(is_space_or_newline)(input)
}

fn skip_space_tag<'a>(tok: &str, input: &'a str) -> IResult<&'a str, &'a str> {
    let (input, _) = skip_space(input)?;
    tag(tok)(input)
}

fn atom(input: &str) -> IResult<&str, Atom> {
    alt((
        map(ident, |x| Atom::Var(x)),
        map(int, |x| Atom::Int(x)),
        map(float, |x| Atom::Float(x)),
        map(bool, |x| Atom::Bool(x)),
        map(char, |x| Atom::Char(x)),
        map(tag("()"), |_| Atom::Unit),
    ))(input)
}

fn ident(input: &str) -> IResult<&str, Ident> {
    let (input, _) = skip_space(input)?;
    let (input, s1) = alpha1(input)?;
    let (input, s2) = take_while(char::is_alphanumeric)(input)?;
    let mut s: String = String::new();
    s.push_str(s1);
    s.push_str(s2);
    Ok((input, Ident::dummy(&s)))
}

fn int(input: &str) -> IResult<&str, i64> {
    let (input, _) = skip_space(input)?;
    let (input, s) = digit1(input)?;
    Ok((input, s.parse::<i64>().unwrap()))
}

fn float(input: &str) -> IResult<&str, f64> {
    let (input, _) = skip_space(input)?;
    let (input, s1) = digit1(input)?;
    let (input, _) = tag(".")(input)?;
    let (input, s2) = digit1(input)?;
    let mut s: String = String::new();
    s.push_str(s1);
    s.push('.');
    s.push_str(s2);
    Ok((input, s.parse::<f64>().unwrap()))
}

fn bool(input: &str) -> IResult<&str, bool> {
    let (input, _) = skip_space(input)?;
    alt((map(tag("true"), |_| true), map(tag("false"), |_| false)))(input)
}

fn char(input: &str) -> IResult<&str, char> {
    let (input, _) = skip_space(input)?;
    let (input, _) = tag("'")(input)?;
    let (input, s1) = alpha1(input)?;
    let (input, _) = tag("'")(input)?;
    let mut s: String = String::new();
    s.push_str("'");
    s.push_str(s1);
    s.push_str("'");
    Ok((input, s.parse::<char>().unwrap()))
}

fn prim_opr(input: &str) -> IResult<&str, PrimOpr> {
    let (input, _) = skip_space(input)?;
    alt((
        value(PrimOpr::IAdd, tag("@iadd")),
        value(PrimOpr::ISub, tag("@isub")),
        value(PrimOpr::IMul, tag("@imul")),
        value(PrimOpr::ICmpLs, tag("@icmpls")),
        value(PrimOpr::ICmpEq, tag("@icmpeq")),
        value(PrimOpr::ICmpGr, tag("@icmpgr")),
        value(PrimOpr::Move, tag("@move")),
        value(PrimOpr::Record, tag("@record")),
        value(PrimOpr::Select, tag("@select")),
    ))(input)
}

fn if_cond(input: &str) -> IResult<&str, IfCond> {
    let (input, _) = skip_space(input)?;
    alt((
        value(IfCond::BTrue, tag("btrue")),
        value(IfCond::BFalse, tag("bfalse")),
        value(IfCond::ICmpGr, tag("icmpgr")),
        value(IfCond::ICmpEq, tag("icmpeq")),
        value(IfCond::ICmpLs, tag("icmpls")),
    ))(input)
}

fn expr_decls(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("decl", input)?;
    let (input, decls) = many0(decl)(input)?;
    let (input, _) = skip_space_tag("in", input)?;
    let (input, cont) = expr(input)?;
    let (input, _) = skip_space_tag("end", input)?;
    Ok((
        input,
        Expr::Decls {
            decls,
            cont: Box::new(cont),
        },
    ))
}

fn expr_prim(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("let", input)?;
    let (input, bind) = ident(input)?;
    let (input, _) = skip_space_tag("=", input)?;
    let (input, prim) = prim_opr(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, args) = separated_list0(|input| skip_space_tag(",", input), atom)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    let (input, cont) = expr(input)?;
    Ok((
        input,
        Expr::Prim {
            bind,
            prim,
            args,
            cont: Box::new(cont),
        },
    ))
}

fn expr_call(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("let", input)?;
    let (input, bind) = ident(input)?;
    let (input, _) = skip_space_tag("=", input)?;
    let (input, func) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, args) = separated_list0(|input| skip_space_tag(",", input), atom)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    let (input, cont) = expr(input)?;
    Ok((
        input,
        Expr::Call {
            bind,
            func: Atom::Var(func),
            args,
            cont: Box::new(cont),
        },
    ))
}

fn expr_ifte(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("if", input)?;
    let (input, cond) = if_cond(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, args) = separated_list0(|input| skip_space_tag(",", input), atom)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag("then", input)?;
    let (input, trbr) = expr(input)?;
    let (input, _) = skip_space_tag("else", input)?;
    let (input, flbr) = expr(input)?;
    Ok((
        input,
        Expr::Ifte {
            cond,
            args,
            trbr: Box::new(trbr),
            flbr: Box::new(flbr),
        },
    ))
}

fn expr_switch(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("switch", input)?;
    let (input, arg) = atom(input)?;
    let (input, _) = skip_space_tag("of", input)?;
    let (input, brchs) = many0(|input| {
        let (input, _) = skip_space_tag("case", input)?;
        let (input, i) = int(input)?;
        let (input, _) = skip_space_tag(":", input)?;
        let (input, brch) = expr(input)?;
        Ok((input, (i as usize, brch)))
    })(input)?;

    let (input, dflt) = opt(|input| {
        let (input, _) = skip_space_tag("default", input)?;
        let (input, _) = skip_space_tag(":", input)?;
        let (input, brch) = expr(input)?;
        Ok((input, Box::new(brch)))
    })(input)?;
    let (input, _) = skip_space_tag("end", input)?;
    Ok((input, Expr::Switch { arg, brchs, dflt }))
}

fn expr_retn(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("return", input)?;
    let (input, res) = atom(input)?;
    let (input, _) = skip_space_tag(";", input)?;
    Ok((input, Expr::Retn { res }))
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((
        expr_decls,
        expr_prim,
        expr_call,
        expr_ifte,
        expr_switch,
        expr_retn,
    ))(input)
}

fn decl(input: &str) -> IResult<&str, Decl> {
    let (input, _) = skip_space_tag("fn", input)?;
    let (input, func) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, pars) = separated_list0(|input| skip_space_tag(",", input), ident)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag("begin", input)?;
    let (input, body) = expr(input)?;
    let (input, _) = skip_space_tag("end", input)?;
    Ok((input, Decl { func, pars, body }))
}

fn module(input: &str) -> IResult<&str, Module> {
    let (input, _) = skip_space_tag("module", input)?;
    let (input, name) = ident(input)?;
    let (input, _) = skip_space_tag("where", input)?;
    let (input, decls) = many0(decl)(input)?;
    Ok((input, Module { name, decls }))
}

pub fn parse_module(input: &str) -> Option<Module> {
    match module(input) {
        Ok((input, mut modl)) => {
            let (input, _) = skip_space(input).unwrap();
            if input == "" {
                super::rename::Renamer::run(&mut modl);
                Some(modl)
            } else {
                None
            }
        }
        Err(_) => None,
    }
}

#[test]
#[ignore = "just to see result"]
fn parser_test() {
    let s = r#"
module Test where
fn top1(x, y) begin
    return x;
end
fn top2(x) begin
    decl
        fn f(x, y, z) begin
            return z; 
        end
        fn g(x, y, z) begin
            ifte(x) {
                { return z; }
                { return z; }
            }
        end
        fn h(x) begin
            if btrue(x)
            then
                return 1;
            else
                switch x of
                case 2:
                    return 1;
                case 4:
                    return 2;
                end
        end
    in
        let x = @iadd(1, 2);
        let y = f(x, x, x);
        return 3;
    end
end
"#;
    let res = parse_module(s).unwrap();
    println!("{}", res);
}
