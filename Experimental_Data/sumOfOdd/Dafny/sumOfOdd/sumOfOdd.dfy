method sumOfOdd(X: int) returns (sum: int)
requires X>=0
ensures sum == X*X;
{

    sum := 0;    
    var i: int := 0;
    while (i < X)
    {
     i := i + 1; sum := sum + 2*i+1;
    }

}