function addDafny(X: int,Y: int) : int
requires X>=0
requires Y>=0
ensures addDafny(X,Y) == X+Y;
{
        if (Y == 0) then X else if(X==0) then Y else addDafny(X,Y-1)+1
}