function potSumm4(X: int) : int
requires X>=0
ensures potSumm4(X) == (6*X*X*X*X*X+15*X*X*X*X+10*X*X*X-X)/30;
{
  if (X==0) then 0 else potSumm4(X-1)+X*X*X*X
}
