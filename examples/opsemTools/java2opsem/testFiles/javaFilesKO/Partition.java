/* Partition of the QuickSort algortihm
 * returns p such that p delimits 2 parts of the array: 
 * elements on the left side of p are stricly less than a[p] 
 * while elements on the right side of p are greater or equals
 * to a[p]
 *
 * precondition: i<j and 0<=i,j<a.length
 * postcondition:
 *   0<=p<a.length and
 *   !i. 0<=i<p ==> a[i]<a[p] and 
 *   !i. p<i<a.length ==> a[i]>=a[p] 
 *   
 */

public class Partition {

    /*@ requires i<j && 0<=i && i<a.length && 0<=j && j<a.length;
        ensures 
          (0<=\result && \result<a.length) &&
          (\forall int i; 0<=i && i<\result;a[i]<a[\result]) &&
          (\forall int i; \result<i && i<a.length;a[i]>=a[\result]) ;
      @*/
	 int partition(int[] a,int i, int j) {
		int pivot = a[i];
		int p = i;
		int k = i+1;
		while (k <= j) {
			if (a[k] < pivot) {
				p=p+1;
				int tmp = a[p];
				a[p]=a[k];
				a[k]=tmp;
			}
			k=k+1;
		}
		int tmp2 = a[p];
		a[p]=a[i];
		a[i]=tmp2;

		return p;
	}

}
