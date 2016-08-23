function potSumm10(X: int) : int
requires X>=0
ensures potSumm10(X) == (6*X*X*X*X*X*X*X*X*X*X*X+33*X*X*X*X*X*X*X*X*X*X+55*X*X*X*X*X*X*X*X*X-66*X*X*X*X*X*X*X+66*X*X*X*X*X-33*X*X*X+5*X)/66;
{
  if (X==0) then 0 else potSumm10(X-1)+X*X*X*X*X*X*X*X*X*X
}
