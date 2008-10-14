/* 
 * Computes the sum of the squares of numbers from p to n
 * The result is the sum of the squares from 0 to n
 * minus the sum of squares from 0 to p.
 */
public class SquareSumFromPtoN {
    /*@ requires (n >= 0) && (p<=n);
    @ ensures \result == ((n*(n+1)*((n*2)+1))/6- (p*(p+1)*((p*2)+1))/6);
    @*/
int somme (int n,int p) {
          int i = p;
          int s = 0;
          while (i<=n) {
                  s = s+i*i;
                  i = i+1;
          }
          return s;
  }
}
