method potSumm10(X: int) returns (sum: int)
requires X>=0
ensures sum == (6*X*X*X*X*X*X*X*X*X*X*X+33*X*X*X*X*X*X*X*X*X*X+55*X*X*X*X*X*X*X*X*X-66*X*X*X*X*X*X*X+66*X*X*X*X*X-33*X*X*X+5*X)/66;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + i*i*i*i*i*i*i*i*i*i;
    }

}
