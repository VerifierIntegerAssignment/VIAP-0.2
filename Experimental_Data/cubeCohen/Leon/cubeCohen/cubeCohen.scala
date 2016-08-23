import leon.lang._

object cubeCohen {

    def cubeCohen(X: BigInt): BigInt=({
	require(X >= 0)
        var i: BigInt = 1
        var m: BigInt = 0
        var y: BigInt = 1
        var z: BigInt = 6
	while( i<=X )
        {
               	i=i+1
        	m=m+y
        	y=y+z
        	z=z+6
        }
      m
    })ensuring(_ >= X*X*X) 

}

