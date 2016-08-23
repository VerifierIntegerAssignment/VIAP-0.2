method potSumm8(X: int) returns (sum: int)
requires X>=0
ensures sum == (10*X*X*X*X*X*X*X*X*X+45*X*X*X*X*X*X*X*X+60*X*X*X*X*X*X*X+-42*X*X*X*X*X+20*X*X*X-3*X)/90;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i*i*i*i*i*i;
    }

}
