module RecordOpt where

datatype Foo where
| Foo { val: mut Int }
end

datatype Bar where
| Bar { val: Foo }
end

function main() -> Int
begin
    let foo = Foo { val: 42 };
    let bar = Bar { val: foo };
    bar.val.val := 43;
    let res = foo.val;
    res
end
