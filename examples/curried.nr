module curried where
function main() -> Int
begin
    let f = fn(x) => begin
        fn(y) => begin
            @iadd(x,y)
        end
    end;
    let g = f(1);
    let res = g(2);
    res
end