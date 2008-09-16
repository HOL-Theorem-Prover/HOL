package expression.integer;

import expression.Expression;

/** Abstract class for integer expressions 
 * @author Hélène Collavizza
 * @date June 2008
 */

public abstract class  IntegerExpression implements Expression {

    // equals function for hashmap
    public boolean equals(Object exp) {
    	return (exp instanceof Expression) && equals((Expression)exp);
    }
    
    public abstract boolean equals(Expression e);
    
    // hashCode function for hashmap
    public abstract int hashCode();
    
}
