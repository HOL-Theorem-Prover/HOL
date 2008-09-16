package expression.logical;

import expression.Expression;
import expression.ExpressionVisitor;

/** class to represent logical expression =>
 * @author Hélène Collavizza
 * @date June 2008

 */
public class ImpliesExpression extends BinaryLogicalOperator {

	public ImpliesExpression(LogicalExpression a1, Expression a2) {
		super(a1,a2);
	}

	public String toString() {
		return  "(" + arg1.toString() + "==>" + arg2.toString() + " )";
	}

	public int hashCode() {
		return (arg1.hashCode() + arg1.hashCode())%Integer.MAX_VALUE;
	}

	public boolean equals(Expression exp){
		return (exp instanceof ImpliesExpression) && 
		arg1.equals(((ImpliesExpression)exp).arg1) && arg2.equals(((ImpliesExpression)exp).arg2);
	}

	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}


}
