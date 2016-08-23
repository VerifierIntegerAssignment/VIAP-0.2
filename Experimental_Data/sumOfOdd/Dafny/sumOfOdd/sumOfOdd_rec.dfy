function sumOfOdd(X: int) : int
requires X>=0
ensures sumOfOdd(X) == X*(X+2);
{
  if (X==0) then 0 else sumOfOdd(X-1)+2*X+1
}
