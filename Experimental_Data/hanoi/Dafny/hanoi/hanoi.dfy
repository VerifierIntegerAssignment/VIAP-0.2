method hanoi(x: int) returns (h: int)
requires x>=0
ensures h==power(2,x)-1;
{
    h := 1;    
    var i: int := 1;
    while (i < x)
    {
         h:=2*h+1;
         i:=i+1;
    }
}
function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (b == 0) then 1 else power(a,b-1)*a
}

