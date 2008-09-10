/* buble sort program */
/* the postcondition is that the array is sorted */

class BubleSort {

	/*@ ensures
	  @	(\forall int i; (i >= 0 && i < a.length-1); a[i] <= a[i+1]); 
	  @*/
	void bubbleSort (int[] a) {
		int i = 0;
		int j = a.length -1;
		int aux = 0;
		int stop = 0;
		while (stop == 0) {
			stop = 1;
			i = 0;
			while (i < j) {
				if (a[i] > a[i+1]) {
					aux = a[i];
					a[i] = a[i+1];
					a[i+1] = aux;
					stop = 0;				
				}
				i = i + 1;			
			}
			j = j - 1;
		}
	}

}
