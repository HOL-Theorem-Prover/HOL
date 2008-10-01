/* Example taken from Mantovani & al [SPIN'2006]
 * buble sort with a precondition:
 *     the array contains numbers between 0 and a.length 
 *     sorted in decreasing order
 */

class BubleSortMantovani {

	/*@ requires (\forall int i; 0<= i && i < a.length; a[i] == (a.length-1)-i);
      @ ensures (\forall int i; 0<= i && i < a.length-1; a[i]<=a[i+1]);
	  @*/

	static void sort(int[] a) {
		int i=0;
		while (i<a.length-1){
			int j=0;
			while (j < (a.length-i)-1) {
				if (a[j]>a[j+1]) {
					int aux = a[j];
					a[j]= a[j+1];
					a[j+1] = aux;
				}
				j=j+1;
			}
			i=i+1;
		}
	}

}
