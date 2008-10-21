package expression.logical;

import expression.Expression;


/** class to represent logical expression <= 
 * @author Hélène Collavizza
 * @date June 2008
*/

public class LessEqualExpression extends Comparator{

    public LessEqualExpression(Expression a1, Expression a2) {
    	super(a1,a2);
    }

    public String toString() {
    	return "( " + arg1.toString() + "<=" + arg2.toString() + " )";
    }
    
    public boolean equals(Expression exp){
    	return (exp instanceof LessEqualExpression) && 
    	arg1.equals(((LessEqualExpression)exp).arg1) && arg2.equals(((LessEqualExpression)exp).arg2);
    }

}
