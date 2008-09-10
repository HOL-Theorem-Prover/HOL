// program that does nothing and has a false specification
// just to do some tests

class Ex1 {
	
	/*@ requires (k>3 || i>8) ;
	 @ ensures (k==6) ==> (result!=k+3 && result > i+j); 
	 @*/
	void sum (int k) {
		int result;
		int k = 0;
		result = k+j;
		k = 12 + 8;
		k = k + 3;
		if (i == j) {
			result = k;
		}
		if (i > j) {
			result = k+1;
		}
		if (i<=j+k) {
			int i = 3;
			result = result+i;
		}
		else {
			result=k;
		}
	}

}
