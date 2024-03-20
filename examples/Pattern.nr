module Pattern where
datatype List[T] where
| Nil
| Cons(T, List[T])
end
function length[T](xs: List[T]) -> Int
begin
    match xs with
    | Nil => 0
    | Cons(x, xs) => length(xs) + 1
    end
end
function main() -> Int
begin
    length(Cons(1, Cons(2, Cons(3, Nil))))
end
