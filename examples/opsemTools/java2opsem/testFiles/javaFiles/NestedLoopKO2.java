/*
 * two nested loops that add 1 to the result variable
 * return n*n
 * 
 *  error has been inserted: variable j is  
 *  initialized only once so the inner j loop is 
 *  also executed only once
 *
 */
public class NestedLoopKO2 {

	/*@ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=1;
		int j=1;
		while (i <= n) {
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
	
}
