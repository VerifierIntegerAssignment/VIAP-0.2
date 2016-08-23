function potSumm3(X: int) : int
requires X>=0
ensures potSumm3(X) == X*(X+1)*X*(X+1)/4;
{
  if (X==0) then 0 else potSumm3(X-1)+X*X*X
}