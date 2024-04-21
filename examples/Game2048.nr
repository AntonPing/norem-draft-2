module Game2048 where

datatype List[T] where
| Nil
| Cons(T, List[T])
end

function is_empty[T](xs: List[T]) -> Bool
begin
    match xs with
    | Nil => true
    | Cons(x, xs) => false
    end
end

function reverse_concat[T](xs: List[T], ys: List[T]) -> List[T]
begin
    match xs with
    | Nil => ys
    | Cons(x, rest) => reverse_concat(rest, Cons(x, ys))
    end
end

function reverse[T](xs: List[T]) -> List[T]
begin
    reverse_concat(xs, Nil)
end

function concat[T](xs: List[T], ys: List[T]) -> List[T]
begin
    reverse_concat(reverse(xs), ys)
end

function length[T](xs: List[T]) -> Int
begin
    match xs with
    | Nil => 0
    | Cons(x, xs) => length(xs) + 1
    end
end

function list_map[T, U](f: fn(T) -> U, xs: List[T]) -> List[U]
begin
    match xs with
    | Nil => Nil
    | Cons(x, rest) => Cons(f(x), list_map(f, rest))
    end
end

function list_flat_map[T, U](f: fn(T) -> Option[U], xs: List[T]) -> List[U]
begin
    match xs with
    | Nil => Nil
    | Cons(x, rest) => 
        match f(x) with
        | Some(res) => Cons(res, list_flat_map(f, rest))
        | None => list_flat_map(f, rest)
        end
    end
end

function list_iter[T](f: fn(T) -> (), xs: List[T]) -> ()
begin
    match xs with
    | Nil => ()
    | Cons(x, rest) =>
        begin
            f(x);
            list_iter(f, rest);
        end
    end
end

function list_count[T](f: fn(T) -> Bool, xs: List[T]) -> Int
begin
    match xs with
    | Nil => 0
    | Cons(x, rest) => if f(x) then list_count(f, rest) + 1 else list_count(f, rest)
    end
end

function list_all[T](f: fn(T) -> Bool, xs: List[T]) -> Bool
begin
    match xs with
    | Nil => true
    | Cons(x, rest) => if f(x) then list_all(f, rest) else false
    end
end

function repeat[T](x: T, n: Int) -> List[T]
begin
    if n < 1 then Nil
    else Cons(x, repeat(x, n - 1))
end

function repeat_init[T](f: fn() -> T, n: Int) -> List[T]
begin
    if n < 1 then Nil
    else Cons(f(), repeat_init(f, n - 1))
end

function transpose[T](mat: List[List[T]]) -> List[List[T]]
begin
    Nil
end

datatype Option[T] where
| None
| Some(T)
end

function next_random(n: Int) -> Int
begin
    // Borland C random number generator implementation
    (22695477 * n + 1) % 2147483648
end

datatype GameBoard where
| GameBoard {
    random: mut Int,
    matrix: mut List[List[Int]],
}
end

function count_zeros(matrix: List[List[Int]]) -> Int
begin
    let count = ref 0;
    list_iter(fn(row) =>
        list_iter(fn(elem) =>
            if elem == 0 then
                begin
                    count <- ^count + 1;
                end
            else (),
            row,
        ),
        matrix,
    );
    ^count
end

function print_matrix(matrix: List[List[Int]])
begin
    @cprint('\n');
    list_iter(fn(row) =>
        begin
            list_iter(fn(elem) =>
                begin
                    @iprint(elem);
                    @cprint(' ');
                end,
                row,
            );
            @cprint('\n');
        end,
        matrix,
    );
end

function squash_line(xs: List[Int]) -> List[Int]
begin
    match xs with
    | Nil => xs
    | Cons(x, Nil) =>
        if x == 0 then Nil else xs
    | Cons(x, rest1) =>
        if x == 0 then
            squash_line(rest1)
        else
            match squash_line(rest1) with
            | Nil => Cons(x, Nil)
            | Cons(y, rest2) =>
                if x == y then
                    Cons(x + y, rest2)
                else
                    Cons(x, Cons(y, rest2))
            end
    end
end

function game_step(board: GameBoard)
begin
    let rows = board.matrix;
    let rows = list_map(
        fn(row) => begin
            let head = squash_line(row);
            let tail = repeat(0, 4 - length(head));
            concat(head, tail)
        end,
        rows,
    );
    board.matrix := rows;
end

function create_new(board: GameBoard)
begin
    let rows = board.matrix;
    let zeros = count_zeros(board.matrix);
    if zeros == 0 then ()
    else
        begin
            let seed = ref (board.random % zeros);
            let rows = list_map(
                fn(row) => begin
                    list_map(
                        fn(elem) => begin
                            if elem == 0 then
                                begin
                                    let old = ^seed;
                                    seed <- ^seed - 1;
                                    if old == 0 then 1 else 0
                                end
                            else elem
                        end,
                        row,
                    )
                end,
                rows,
            );
            board.matrix := rows;
        end
end

function transpose_matrix(matrix: List[List[Int]]) -> List[List[Int]]
begin
    if is_empty(matrix) then
        Nil
    else
        begin
            let first_col = ref Nil;
            let rest_matrix = ref Nil;
            list_iter(
                fn(row) =>
                    match row with
                    | Cons(x, xs) =>
                        begin
                            // why can't I uncomment this line?
                            let m : List[Int] = ^first_col;

                            first_col <- Cons(x, ^first_col);
                            if is_empty(xs) then
                                ()
                            else
                                begin
                                    rest_matrix <- Cons(xs, ^rest_matrix);
                                end
                            ;
                        end
                    | Nil => ()
                    end
                ,
                matrix,
            );
            Cons(
                reverse(^first_col),
                transpose_matrix(reverse(^rest_matrix)),
            )
        end
end

function reverse_matrix(matrix: List[List[Int]]) -> List[List[Int]]
begin
    list_map(
        fn(row) => reverse(row),
        matrix,
    )
end


function main() -> Int
begin
    let seed = @iscan();
    let matrix = repeat(repeat(0, 4), 4);
    let game = GameBoard { random: seed, matrix };

    while count_zeros(game.matrix) != 0 do
        // print matrix
        print_matrix(game.matrix);
        // get input
        let input = @iscan();

        if input == 4 then
            begin
                game_step(game);
            end
        else if input == 8 then
            begin
                game.matrix := transpose_matrix(game.matrix);
                game_step(game);
                game.matrix := transpose_matrix(game.matrix);
            end
        else if input == 2 then
            begin
                game.matrix := transpose_matrix(game.matrix);
                game.matrix := reverse_matrix(game.matrix);
                game_step(game);
                game.matrix := reverse_matrix(game.matrix);
                game.matrix := transpose_matrix(game.matrix);
            end
        else if input == 6 then
            begin
                game.matrix := reverse_matrix(game.matrix);
                game_step(game);
                game.matrix := reverse_matrix(game.matrix);
            end
        else
            ();

        // generate new number
        create_new(game);

        // update random number
        game.random := next_random(game.random);
    end; 

    print_matrix(game.matrix);
    0
end
