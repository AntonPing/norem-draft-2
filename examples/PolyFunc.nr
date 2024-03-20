module PolyFunc where
function id[T](x: T) -> T begin
    x
end
function fst[T, U](x: T, y: U) -> T begin
    x
end
function snd[T, U](x: T, y: U) -> U begin
    y
end
function main() -> Int
begin
    id(1) + fst(2, 3.0) + snd(4.0, 5)
end
