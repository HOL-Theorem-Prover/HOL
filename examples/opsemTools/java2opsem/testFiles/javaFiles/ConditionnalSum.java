/*
 * if n<k, computes the sum of the n first integers
 * else computes n+k
 */
class ConditionnalSum {

	/*@ requires (n >= 0);
	  @ ensures
	  @	((n < k) ==> (\result == (n*(n+1))/2))
	  @  && (!(n<k) ==> (\result == n+k));
	  @*/
	int sum (int n, int k) {
		int s = 0;
		if (n >= k) {
			s = n + k;		
		}
		else {
			int i=0;
			while (i <= n) {
				s = s + i;
				i = i + 1;			
			}
		}
		return s;
	}

}
