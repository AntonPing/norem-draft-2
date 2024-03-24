module Reference where
function main() -> Int
begin
    let r = ref 42;
    r <- 43;
    let a = ^r;
    r <- 44;
    let b = ^r;
    a + b
end
