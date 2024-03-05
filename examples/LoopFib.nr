module LoopFib where
function fib(n: Int) -> Int
begin
    let this = ref 1;
    let last = ref 0;
    let i = ref 1;
    while @icmpls(^i, n) do
        let temp = @iadd(^this, ^last);
        last := ^this;
        this := temp;
        i := @iadd(^i, 1);
    end;
    ^this
end
function main() -> Int
begin
    fib(10)
end