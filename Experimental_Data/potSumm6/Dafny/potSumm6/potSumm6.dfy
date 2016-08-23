method potSumm6(X: int) returns (sum: int)
requires X>=0
ensures sum == (6*X*X*X*X*X*X*X+21*X*X*X*X*X*X+21*X*X*X*X*X-7*X*X*X+X)/42;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i*i*i*i;
    }

}
