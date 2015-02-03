package expression.logical;

import expression.Expression;

/** class to represent logical expression > 
 * @author Hélène Collavizza
 * @date June 2008
*/

public class GreatExpression extends Comparator{

    public GreatExpression(Expression a1, Expression a2) {
	super(a1,a2);
    }

    public String toString() {
	return "( " + arg1.toString() + " > " + arg2.toString() + " )";
    }

    public boolean equals(Expression exp){
    	return (exp instanceof GreatExpression) && 
    	arg1.equals(((GreatExpression)exp).arg1) && arg2.equals(((GreatExpression)exp).arg2);
    }

    public String abstractSyntax(){
      	 return "IDSExprSup";
       }
}
