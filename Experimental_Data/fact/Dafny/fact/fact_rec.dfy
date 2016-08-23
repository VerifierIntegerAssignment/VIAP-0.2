function fact(n: int) : int
requires n>=0
{
        if (n == 0) then 1 else fact(n-1)*n
}
lemma factLemma(n: int)
requires n>=0
ensures fact(n) >=1;
{
}
