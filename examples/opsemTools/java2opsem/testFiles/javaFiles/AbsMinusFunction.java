class AbsMinusFunction {
	
    /* Example of function call */
    /* last part of AbsMinus program has been replaced 
       with a function */
	
    /*@ ensures
      ((i < j) ==> (\result == j-i)) 
      && ((i >= j) ==> (\result == i-j));
      @*/
    int absMinus (int i, int j) {
	int k = 0;
	if (i <= j) {
	    k = k+1;
	}
	return func1(i,j,k);
    }	
    
    int func1(int i, int j, int k) {	
	int result;
	if (k == 1 && i != j) {
	    result = j-i;		
	}
	else {
	    result = i-j;
	}
	return result;
    }
}
