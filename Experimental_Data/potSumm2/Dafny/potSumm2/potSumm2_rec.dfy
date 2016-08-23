function potSumm2(X: int) : int
requires X>=0
ensures potSumm2(X) == X*(X+1)*(2*X+1)/6;
{
  if (X==0) then 0 else potSumm2(X-1)+X*X
}