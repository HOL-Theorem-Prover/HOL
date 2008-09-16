package expression.logical;

import expression.Expression;
import expression.ExpressionVisitor;

/** abstract class to represent comparison operators
 * @author Hélène Collavizza
 * @date June 2008
 */
public abstract class Comparator extends LogicalExpression {

	Expression arg1;
	Expression arg2;
	
	public Comparator(Expression a1, Expression a2) {
		arg1 = a1;
		arg2=  a2;
	}
	
	public Expression arg1() {
		return arg1;
	}

	public Expression arg2() {
		return arg2;
	}

	public boolean isComparator() {
		return true;
	}	

	public boolean isStrictComparator() {
		return (this instanceof LessExpression) ||
		       (this instanceof GreatExpression);
	}

	public boolean isEqualComparator() {
		return  (this instanceof EqualExpression);
	}
	
	public int hashCode() {
		return (arg1.hashCode() + arg2.hashCode())%Integer.MAX_VALUE;
	}

	public abstract boolean equals(Expression exp);


	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

}