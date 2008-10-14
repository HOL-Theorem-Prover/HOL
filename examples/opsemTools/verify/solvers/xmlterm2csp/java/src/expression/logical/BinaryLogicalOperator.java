package expression.logical;


import expression.Expression;
import expression.ExpressionVisitor;

/** Abstract class to represent binary logical operators 
 * @author Hélène Collavizza
 * @date June 2008
*/

public abstract class BinaryLogicalOperator extends LogicalExpression{

	Expression arg1;
	Expression arg2;

	protected BinaryLogicalOperator() {
		super();
	}

	public BinaryLogicalOperator(Expression a1, Expression a2) {
		arg1=a1;
		arg2=a2;
	}

	public int hashCode() {
		return (arg1.hashCode() + arg2.hashCode())%Integer.MAX_VALUE;
	}

	public abstract boolean equals(Expression exp);
	
	public Expression arg1() {
		return arg1;
	}

	public Expression arg2() {
		return arg2;
	}
	
	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

}
