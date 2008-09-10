/*
 * two nested loops that add 1 to the result variable
 * return n*n
 * 
 * errors have been inserted lines 13 and 15
 */
public class NestedLoopKO1 {

	/*@ ensures \result == n*n;
	  @*/
	static int nestedLoop (int n) {
		int s = 0;
		int i=0; // 0 instead of 1
		while (i <= n) {
			int j=0; // 0 instead of 1
			while (j <= n) {
				s=s+1;
				j=j+1;
			}
			i=i+1;
		}
		return s;
	}
	
}
