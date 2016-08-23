function potSumm7(X: int) : int
requires X>=0
ensures potSumm7(X) == (3*X*X*X*X*X*X*X*X+12*X*X*X*X*X*X*X+14*X*X*X*X*X*X-7*X*X*X*X+2*X*X)/24;
{
  if (X==0) then 0 else potSumm7(X-1)+X*X*X*X*X*X*X
}
