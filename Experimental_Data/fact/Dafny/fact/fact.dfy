method fact(X: int) returns (F: int)
requires X>=0
ensures factorial(X) == F;
{
    F := 1;    
    var i: int := 1;
    while (i < X)
    {
     F := F * i; i := i + 1;
    }
}
function factorial(n: int) : int
requires n>=0
{
        if (n == 0) then 1 else factorial(n-1)*n
}

