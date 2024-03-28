module FieldMut where

datatype Foo where
| Foo1 { a: mut Int, b: Int }
| Foo2 { c: mut Int, d: Int }
end

function read_fst(x: Foo) -> Int
begin
    match x with
    | Foo1 { a, b } as foo => foo.a
    | Foo2 { c, d } as foo => foo.c
    end
end

function write_fst(x: Foo)
begin
    match x with
    | Foo1 { a, b } as foo =>
        begin
            foo.a := 42;
        end
    | Foo2 { c, d } as foo =>
        begin
            foo.c := 43;
        end
    end
end

function main() -> Int
begin
    let foo1 = Foo1 { a: 1, b: 2 };
    let foo2 = Foo2 { c: 3, d: 4 };
    write_fst(foo1);
    write_fst(foo2);
    read_fst(foo1) + read_fst(foo2)
end
