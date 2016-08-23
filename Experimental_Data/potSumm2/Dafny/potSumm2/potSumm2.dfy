method potSumm2(X: int) returns (sum: int)
requires X>=0
ensures sum == X*(X+1)*(2*X+1)/6;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i;
    }

}