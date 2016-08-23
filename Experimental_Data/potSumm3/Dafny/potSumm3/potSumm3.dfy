method potSumm3(X: int) returns (sum: int)
requires X>=0
ensures sum == X*(X+1)*X*(X+1)/4;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i;
    }

}