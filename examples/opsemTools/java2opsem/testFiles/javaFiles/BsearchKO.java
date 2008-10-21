class BsearchKO {

    // an error has been inserted int the program on line 
    // 16 of the program
    // left = mid + 1; has been replaced with right = mid - 1;
	/*@ requires (\forall int i; (i >= 0 && i < a.length -1); a[i] <= a[i+1]);
	  @ ensures
	  @	((\result == -1) ==> (\forall int i; (i >= 0 && i < a.length); a[i] != x)) 
	  @ 	&& ((\result != -1) ==> (a[\result] == x));
	  @*/
	int binarySearch (int[] a, int x) {
		int result = -1;
		int mid = 0;
		int left = 0;
		int right = a.length -1;
		while (result == -1 && left <= right) {
			mid = (left + right) / 2;
			if (a[mid] == x) {
				result = mid;			
			}
			else {
				if (a[mid] > x) {
					right = mid - 1;				
				}
				else {
					 right = mid - 1;   
				}
			}
		}
		return result;
	}
}
