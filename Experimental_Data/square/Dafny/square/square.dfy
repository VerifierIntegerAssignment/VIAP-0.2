method squre(M: int) returns (s: int)
requires M>=0
ensures s == M*M;
{
    s := 0;    
    var i: int := 0;
    while(i<M)
    {
	s:=s+M;
	i:=i+1;
			
    }
}

