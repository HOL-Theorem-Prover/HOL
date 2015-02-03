package expression.logical;

import expression.Expression;

/**  Logical expressions  
 * @author Hélène Collavizza
 * @date June 2008
 */

public abstract class LogicalExpression implements Expression {
	
    public abstract String toString();
    
    // equals function for hashmap
    public boolean equals(Object exp) {
    	return (exp instanceof Expression) && equals((Expression)exp);
    }
    
    public abstract boolean equals(Expression e);
    
    // hashCode function for hashmap
    public abstract int hashCode();
      
	public boolean isComparator() {
		return false;
	}
 
}
