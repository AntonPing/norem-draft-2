module RecFib where
function fib(n: Int) -> Int
begin
    if @icmpls(n, 1) then
        0
    else if @icmpeq(n, 1) then
        1
    else
        @iadd(fib(@isub(n,1)), fib(@isub(n,2)))
end
function main() -> Int
begin
    fib(10)
end