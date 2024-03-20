module RecFib where
function fib(n: Int) -> Int
begin
    if n < 1 then
        0
    else if n == 1 then
        1
    else
        fib(n - 1) + fib(n - 2)
end
function main() -> Int
begin
    fib(10)
end
