/* swap two arrays */

/* since Java implements a call by value parameter
 * passing, call to swap do nothing
 */

class ArraySwap {
	
  /*@ ensures a==\old(b) && b==\old(a);
  @*/
 void swap(int[] a, int[] b ) {
		int tmp = a;
		a = b;
		b = tmp;
	}
}
