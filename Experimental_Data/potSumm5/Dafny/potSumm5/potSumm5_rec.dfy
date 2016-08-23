function potSumm5(X: int) : int
requires X>=0
ensures potSumm5(X) == (2*X*X*X*X*X*X+6*X*X*X*X*X+5*X*X*X*X-X*X)/12;
{
  if (X==0) then 0 else potSumm5(X-1)+X*X*X*X*X
}
