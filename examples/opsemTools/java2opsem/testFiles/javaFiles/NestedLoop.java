/*
 * two nested loops that add 1 to the result variable
 * return n*n
 */
public class NestedLoop {

	/*@ requires n>=0;
          @ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=1;
		while (i <= n) {
			int j=1;
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
	
}
