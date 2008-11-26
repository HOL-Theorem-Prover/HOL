package expression.logical;

import expression.Expression;

/** class to represent logical expression Equal
 * @author Hélène Collavizza
 * @date June 2008
 */

public class EqualExpression extends Comparator{

    public EqualExpression(Expression a1, Expression a2) {
    	super(a1,a2);
    }

    public String toString() {
	return "( " + arg1.toString() + "==" + arg2.toString() + " )";
    }

    public boolean equals(Expression exp){
    	return (exp instanceof EqualExpression) && 
    	arg1.equals(((EqualExpression)exp).arg1) && arg2.equals(((EqualExpression)exp).arg2);
    }

    public String abstractSyntax(){
   	 return "IDSExprEquality";
    }
    
 
}
