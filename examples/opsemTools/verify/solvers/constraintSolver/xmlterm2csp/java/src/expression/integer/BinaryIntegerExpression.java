package expression.integer;

import expression.Expression;
import expression.ExpressionVisitor;

/** class to represent binary integer expressions 
 * @author Hélène Collavizza
 * @date June 2008
 * */

public abstract class BinaryIntegerExpression extends IntegerExpression{

	Expression arg1;
	Expression arg2;

	public BinaryIntegerExpression(Expression a1, Expression a2) {
		arg1=a1;
		arg2=a2;
	}

	public Expression getArg1() {
		return arg1;
	}

	public Expression getArg2() {
		return arg2;
	}
	
	public int hashCode() {
		return (arg1.hashCode() + arg1.hashCode())%Integer.MAX_VALUE;
	}

	public abstract boolean equals(Expression exp);

	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

}
