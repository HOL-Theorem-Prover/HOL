/* 
 * Computes the sum of numbers from p to n.
 * The result is the sum of the numbers from 0 to n
 * minus the sum of numbers from 0 to p.
 */
public class SumFromPtoNKO {
    /*@ requires (n >= 0) && (p<=n);
    @ ensures \result == n*(n+1)/2 - p*(p+1)/2;
    @*/
int somme (int n,int p) {
          int i = p;
          int s = 0;
          while (i<=n) {
                  s = s+i;
                  i = i+1;
          }
          return s;
  }
}
