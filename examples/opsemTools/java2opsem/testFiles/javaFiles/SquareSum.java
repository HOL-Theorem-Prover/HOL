/* sum of the square of the n first integers
 */

class SquareSum {

	/*@ requires (n >= 0); 
	  @ ensures \result == (n*(n+1)*((n*2)+1))/6;
	  @*/
	static int squareSum (int n) {
		int i=0;
		int s = 0;
		while (i<=n) {
			s = s+i*i;
			i = i+1;	
		}
		return s;
	}

}
