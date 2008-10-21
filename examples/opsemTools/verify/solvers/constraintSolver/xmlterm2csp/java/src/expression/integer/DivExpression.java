package expression.integer;

import expression.Expression;


/**
 * class to represent div expression / 
 * @author Hélène Collavizza
 * @date June 2008
 * */

public class DivExpression extends BinaryIntegerExpression{
	
	public DivExpression(Expression a1, Expression a2) {
		super(a1,a2);
	}

	public String toString() {
		return "( " + arg1.toString() + " * " + arg2.toString() + " )";
	}

	public boolean equals(Expression exp){
		return (exp instanceof DivExpression) 
		&& arg1.equals(((DivExpression)exp).arg1) && arg2.equals(((DivExpression)exp).arg2);
	}

}
