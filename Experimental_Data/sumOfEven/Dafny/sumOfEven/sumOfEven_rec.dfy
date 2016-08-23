function sumOfEven(X: int) : int
requires X>=0
ensures sumOfEven(X) == X*(X+1);
{
  if (X==0) then 0 else sumOfEven(X-1)+X*2
}