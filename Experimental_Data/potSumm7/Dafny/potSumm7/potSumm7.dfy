method potSumm7(X: int) returns (sum: int)
requires X>=0
ensures sum == (3*X*X*X*X*X*X*X*X+12*X*X*X*X*X*X*X+14*X*X*X*X*X*X-7*X*X*X*X+2*X*X)/24;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i*i*i*i*i;
    }

}
