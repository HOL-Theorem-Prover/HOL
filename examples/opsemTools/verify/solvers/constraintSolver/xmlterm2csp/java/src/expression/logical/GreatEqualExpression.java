package expression.logical;

import expression.Expression;


/** class to represent logical expression >=  
 * @author Hélène Collavizza
 * @date June 2008
*/

public class GreatEqualExpression extends Comparator{

    public GreatEqualExpression(Expression a1, Expression a2) {
	super(a1,a2);
    }

    public String toString() {
	return "( " + arg1.toString() + " >= " + arg2.toString() + " )";
    }

    public boolean equals(Expression exp){
    	return (exp instanceof GreatEqualExpression) && 
    	arg1.equals(((GreatEqualExpression)exp).arg1) && arg2.equals(((GreatEqualExpression)exp).arg2);
    }

    public String abstractSyntax(){
      	 return "IDSExprSupEqual";
       }
}
