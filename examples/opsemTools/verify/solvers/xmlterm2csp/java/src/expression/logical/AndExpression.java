package expression.logical;

import expression.Expression;


/** class to represent logical expression and 
 * @author Hélène Collavizza
 * @date June 2008
*/

public class AndExpression extends BinaryLogicalOperator{

    public AndExpression(Expression a1, Expression a2) {
    	super(a1,a2);
     }

    public String toString() {
    	if (arg1==null) return arg2.toString();
    	return "( " + arg1.toString() + " && " + arg2.toString() + " )";
    }
    
    public boolean equals(Expression exp){
    	return (exp instanceof AndExpression) && 
    	arg1.equals(((AndExpression)exp).arg1) && arg2.equals(((AndExpression)exp).arg2);
    }
 

}