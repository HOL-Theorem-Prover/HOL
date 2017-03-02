package expression.logical;

import expression.Expression;


/** class to represent logical expression < 
 * @author Hélène Collavizza
 * @date June 2008
*/

public class LessExpression extends  Comparator{

    public LessExpression(Expression a1, Expression a2) {
    	super(a1,a2);
    }

    public String toString() {
	return "( " + arg1.toString() + "<" + arg2.toString() + " )";
    }

    public boolean equals(Expression exp){
    	return (exp instanceof LessExpression) && 
    	arg1.equals(((LessExpression)exp).arg1) && arg2.equals(((LessExpression)exp).arg2);
    }

}
