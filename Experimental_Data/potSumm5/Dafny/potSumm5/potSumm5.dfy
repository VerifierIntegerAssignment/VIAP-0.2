method potSumm5(X: int) returns (sum: int)
requires X>=0
ensures sum == (2*X*X*X*X*X*X+6*X*X*X*X*X+5*X*X*X*X-X*X)/12;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i*i*i;
    }

}
