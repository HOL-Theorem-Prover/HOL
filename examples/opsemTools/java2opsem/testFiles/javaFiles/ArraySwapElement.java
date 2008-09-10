/* swap two elements in an array */

class ArraySwapElement {
	
  /*@ requires (i>0 && i < a.length)
  @ && (j>0 && j < a.length);
  @ ensures a[i]==\old(a[j]) && a[j]==\old(a[i]);
  @*/
 void swap(int[] a, int i,int j ) {
		int tmp = a[i];
		a[i] = a[j];
		a[j] = tmp;
	}
}
