function potSumm9(X: int) : int
requires X>=0
ensures potSumm9(X) == (2*X*X*X*X*X*X*X*X*X*X+10*X*X*X*X*X*X*X*X*X+15*X*X*X*X*X*X*X*X-14*X*X*X*X*X*X+10*X*X*X*X-3*X*X)/20;
{
  if (X==0) then 0 else potSumm9(X-1)+X*X*X*X*X*X*X*X*X
}
