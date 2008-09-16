package expression.logical;


import expression.Expression;
import expression.ExpressionVisitor;

/** class to represent logical expression not
 * @author Hélène Collavizza
 * @date June 2008
*/

public class NotExpression extends BinaryLogicalOperator{

	public NotExpression(Expression a1) {
		super(a1,null);
	}
	
	public String toString() {
		return  "!( " + arg1.toString()+ " )";
	}

	public int hashCode() {
		return arg1.hashCode() ;
	}

	public boolean equals(Expression exp){
		return (exp instanceof NotExpression) &&  arg1.equals(((NotExpression)exp).arg1) ;
	}

	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}


}
