// search of a value in an array
// PRECOND: the length of the arrays is 10
class Search {

    /*@ requires a.length==10;
      @ ensures
      @	((\result == -1) ==> (\forall int i; (i >= 0 && i < a.length); a[i] != x)) 
      @ 	&& ((\result != -1) ==> (a[\result] == x));
      @*/
    int search (int[] a, int x) {
	int result = -1;
	int left = 0;
	while (result == -1 && left < a.length) {
	    if (a[left] == x) {
		result = left;			
	    }
	    else {
		left=left+1;
	    }
	}
	return result;
    }
}
