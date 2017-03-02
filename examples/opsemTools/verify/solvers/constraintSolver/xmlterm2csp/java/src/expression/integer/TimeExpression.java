package expression.integer;

import expression.Expression;


/**
 * class to represent expression time *
 * @author Hélène Collavizza
 * @date June 2008 
*/

public class TimeExpression extends BinaryIntegerExpression{

    public TimeExpression(Expression a1, Expression a2) {
    	super(a1,a2);
    }

	public String toString() {
		return "( " + arg1.toString() + " * " + arg2.toString() + " )";
    }
    
    public boolean equals(Expression exp){
    	return (exp instanceof TimeExpression) 
    	&& arg1.equals(((TimeExpression)exp).arg1) && arg2.equals(((TimeExpression)exp).arg2);
    }

}
