module Fields where

datatype Foo where
| Foo1 { a: Int, b: Int }
| Foo2 { c: Int, d: Int }
end

function read_fst(x: Foo) -> Int
begin
    match x with
    | Foo1 { a, b } as foo => foo.a
    | Foo2 { c, d } as foo => foo.c
    end
end

datatype Bar where
| Bar { a: Int, b: Int }
end

function main() -> Int
begin
    let foo1 = Foo1 { a: 1, b: 2 };
    let foo2 = Foo2 { c: 3, d: 4 };
    let bar = Bar { a: 5, b: 6 };
    read_fst(foo1) + read_fst(foo2) + bar.a 
end

