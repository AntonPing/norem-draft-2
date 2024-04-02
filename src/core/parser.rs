use super::cps::*;
use crate::syntax::prim::Prim;
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

fn prim_opr(input: &str) -> IResult<&str, Prim> {
    let (input, _) = skip_space(input)?;
    let (input, head) = tag("@")(input)?;
    let (input, body) = alpha1(input)?;
    let mut s = String::new();
    s.push_str(head);
    s.push_str(body);
    if let Ok(res) = s.parse() {
        Ok((input, res))
    } else {
        nom::combinator::fail("unknown primitive!")
    }
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
    let (input, _) = skip_space_tag("decls", input)?;
    let (input, funcs) = many0(func_decl)(input)?;
    let (input, conts) = many0(cont_decl)(input)?;
    let (input, _) = skip_space_tag("in", input)?;
    let (input, body) = expr(input)?;
    let (input, _) = skip_space_tag("end", input)?;
    let body = Box::new(body);
    Ok((input, Expr::Decls { funcs, conts, body }))
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
    let (input, rest) = expr(input)?;
    Ok((
        input,
        Expr::Prim {
            bind,
            prim,
            args,
            rest: Box::new(rest),
        },
    ))
}

fn expr_call(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("call", input)?;
    let (input, func) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, args) = separated_list0(|input| skip_space_tag(",", input), atom)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    if !args.is_empty() {
        let cont = args[0];
        let args = args[1..].iter().copied().collect();
        if let Atom::Var(cont) = cont {
            Ok((input, Expr::Call { func, cont, args }))
        } else {
            nom::combinator::fail("function call with a non-cont first argument!")
        }
    } else {
        nom::combinator::fail("function call without cont argument!")
    }
}

fn expr_record(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("record", input)?;
    let (input, bind) = ident(input)?;
    let (input, _) = skip_space_tag("=", input)?;
    let (input, _) = skip_space_tag("{", input)?;
    let (input, args) = separated_list0(
        |input| skip_space_tag(",", input),
        |input| {
            let (input, res) = opt(|input| skip_space_tag("{", input))(input)?;
            let (input, arg) = atom(input)?;
            Ok((input, (res.is_some(), arg)))
        },
    )(input)?;
    let (input, _) = skip_space_tag("}", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    let (input, rest) = expr(input)?;
    Ok((
        input,
        Expr::Record {
            bind,
            args,
            rest: Box::new(rest),
        },
    ))
}

fn expr_select(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("select", input)?;
    let (input, bind) = ident(input)?;
    let (input, _) = skip_space_tag("=", input)?;
    let (input, rec) = atom(input)?;
    let (input, _) = skip_space_tag("[", input)?;
    let (input, idx) = digit1(input)?;
    let (input, _) = skip_space_tag("]", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    let (input, rest) = expr(input)?;
    Ok((
        input,
        Expr::Select {
            bind,
            rec,
            idx: idx.parse().unwrap(),
            rest: Box::new(rest),
        },
    ))
}

fn expr_update(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("update", input)?;
    let (input, rec) = atom(input)?;
    let (input, _) = skip_space_tag("[", input)?;
    let (input, idx) = digit1(input)?;
    let (input, _) = skip_space_tag("]", input)?;
    let (input, _) = skip_space_tag("=", input)?;
    let (input, arg) = atom(input)?;
    let (input, _) = skip_space_tag(";", input)?;
    let (input, rest) = expr(input)?;
    Ok((
        input,
        Expr::Update {
            rec,
            idx: idx.parse().unwrap(),
            arg,
            rest: Box::new(rest),
        },
    ))
}

fn expr_jump(input: &str) -> IResult<&str, Expr> {
    let (input, _) = skip_space_tag("jump", input)?;
    let (input, cont) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, args) = separated_list0(|input| skip_space_tag(",", input), atom)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(";", input)?;
    Ok((input, Expr::Jump { cont, args }))
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
        expr_record,
        expr_select,
        expr_update,
        expr_call,
        expr_jump,
        expr_ifte,
        expr_switch,
        expr_retn,
    ))(input)
}

fn func_decl(input: &str) -> IResult<&str, FuncDecl> {
    let (input, _) = skip_space_tag("func", input)?;
    let (input, func) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, pars) = separated_list0(|input| skip_space_tag(",", input), ident)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(":", input)?;
    let (input, body) = expr(input)?;
    if !pars.is_empty() {
        let cont = pars[0];
        let pars = pars[1..].iter().copied().collect();
        Ok((
            input,
            FuncDecl {
                func,
                cont,
                pars,
                body,
            },
        ))
    } else {
        nom::combinator::fail("function definition without cont parameter!")
    }
}

fn cont_decl(input: &str) -> IResult<&str, ContDecl> {
    let (input, _) = skip_space_tag("cont", input)?;
    let (input, cont) = ident(input)?;
    let (input, _) = skip_space_tag("(", input)?;
    let (input, pars) = separated_list0(|input| skip_space_tag(",", input), ident)(input)?;
    let (input, _) = skip_space_tag(")", input)?;
    let (input, _) = skip_space_tag(":", input)?;
    let (input, body) = expr(input)?;
    Ok((input, ContDecl { cont, pars, body }))
}

fn module(input: &str) -> IResult<&str, Module> {
    let (input, _) = skip_space_tag("module", input)?;
    let (input, name) = ident(input)?;
    let (input, _) = skip_space_tag("where", input)?;
    let (input, decls) = many0(func_decl)(input)?;
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
func top1(x, y):
    return x;
func top2(x):
    decls
        func f(k, x, y, z):
            jump k(x);
        cont k(a):
            return a;
    in
        let x = @iadd(1, 2);
        call f(k, 1, 2, 3);
    end
"#;
    let res = parse_module(s).unwrap();
    println!("{}", res);
}
