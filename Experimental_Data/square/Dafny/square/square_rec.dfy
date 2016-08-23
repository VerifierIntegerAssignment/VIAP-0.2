function square(M: int) : int
requires M>=0
ensures square(M) == M*M;
{
        squareM(M,M)
}
function squareM(M: int,N: int) : int
requires M>=0
requires N>=0
{
        if (N == 0) then M else squareM(M,N-1)+M
}