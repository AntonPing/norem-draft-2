module LoopFib where
function fib(n: Int) -> Int
begin
    let this = ref 1;
    let last = ref 0;
    let i = ref 1;
    while ^i < n do
        let temp = ^this + ^last;
        last := ^this;
        this := temp;
        i := ^i + 1;
    end;
    ^this
end
function main() -> Int
begin
    fib(10)
end
