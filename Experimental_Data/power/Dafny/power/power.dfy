method power(a: int,b: int) returns (A: int)
requires a>=0
requires b>=0
ensures A == powerFun(a,b);
{
    A := 1;    
    var J: int := 0;
    while (J<b)
    {
     A := A * a; J := J + 1;
    }
}

function powerFun(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (a == 0) then 0 else if (b == 0) then 1 else powerFun(a,b-1)*a
}
