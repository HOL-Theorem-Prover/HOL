package expression.logical;

import expression.Expression;


/** class to represent logical expression or 
 * @author Hélène Collavizza
 * @date June 2008
*/

public class OrExpression extends BinaryLogicalOperator{

    public OrExpression(Expression a1, Expression a2) {
    	super(a1,a2);
    }

    public String toString() {
    	return "( " + arg1.toString() + " || " + arg2.toString() + " )";
    }

    public boolean equals(Expression exp){
    	return (exp instanceof OrExpression) && 
    	arg1.equals(((OrExpression)exp).arg1) && arg2.equals(((OrExpression)exp).arg2);
    }
 
}
