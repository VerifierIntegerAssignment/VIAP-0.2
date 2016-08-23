function potSumm8(X: int) : int
requires X>=0
ensures potSumm8(X) == (10*X*X*X*X*X*X*X*X*X+45*X*X*X*X*X*X*X*X+60*X*X*X*X*X*X*X+-42*X*X*X*X*X+20*X*X*X-3*X)/90;
{
  if (X==0) then 0 else potSumm8(X-1)+X*X*X*X*X*X*X*X
}
