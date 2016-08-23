function hanoi(n: int) : int
requires n>0
ensures hanoi(n)==power(2,n)-1;
{
        if (n == 1) then 1 else 2*hanoi(n-1)+1
}
function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (b == 0) then 1 else power(a,b-1)*a
}