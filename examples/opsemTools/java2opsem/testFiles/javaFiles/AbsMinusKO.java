class AbsMinusKO {
	
    /* returns |i-j|, the absolute value of i minus j */
	
	/* a "copy/paste" error has been inserted: 
	 *   line 23 is the same as line 20
	 */

	
    /*@ ensures
	  @ 	((i < j) ==> (\result == j-i)) 
                 && ((i >= j) ==> (\result == i-j));
	  @*/
	int absMinusKO (int i, int j) {
		int result;
		int k = 0;
		if (i <= j) {
			k = k+1;
		}
		if (k == 1 && i != j) {
			result = j-i;		
		}
		else {
			result = j-i;
		}
		return result;
	}

}
