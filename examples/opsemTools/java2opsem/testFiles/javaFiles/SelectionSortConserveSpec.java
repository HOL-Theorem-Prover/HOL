/* selection sort program */

/* the postcondition is that the array is sorted and that
 * it contains the same values as before execution
 */

class SelectionSortConserveSpec {
	
	/*@ ensures
	  @	(\forall int i; (i >= 0 && i < a.length -1); a[i] <= a[i+1])
	  @ && (\forall int i; (i >= 0 && i < a.length-1);
	  @        (\exists int j; (i >= 0 && i < a.length-1);
	  @              \old(a[j]) == a[i]));
	  @*/
	void selectionSort (int[] a) {
		int i = 0;
		int j = 0;
		int indMin = 0;
		int aux = 0;
		while (i < a.length) {
			indMin = i;
			j = i + 1;
			while (j < a.length) {
				if (a[indMin] > a[j]) {
					indMin = j;				
				}
				j = j + 1;
			}
			aux = a[i];
			a[i] = a[indMin];
			a[indMin] = aux;
			i = i + 1;		
		}
	}

}
