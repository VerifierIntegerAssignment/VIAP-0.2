function potSumm1(X: int) : int
requires X>=0
ensures potSumm1(X) == X*(X+1)/2;
{
  if (X==0) then 0 else potSumm1(X-1)+X
}
