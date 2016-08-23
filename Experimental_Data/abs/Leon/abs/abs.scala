import leon.lang._

object abs {

	def abs(X: Int): Int = {
		if(X <= 0) -X else X
	} ensuring(res => res >= 0)

}
