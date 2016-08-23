function potSumm6(X: int) : int
requires X>=0
ensures potSumm6(X) == (6*X*X*X*X*X*X*X+21*X*X*X*X*X*X+21*X*X*X*X*X-7*X*X*X+X)/42;
{
  if (X==0) then 0 else potSumm6(X-1)+X*X*X*X*X*X
}
