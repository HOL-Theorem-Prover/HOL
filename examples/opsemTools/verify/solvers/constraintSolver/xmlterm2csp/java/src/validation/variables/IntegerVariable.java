package validation.variables;

import expression.Expression;
import expression.ExpressionVisitor;
import expression.integer.IntegerExpression;


/** class to represent integer variables
 * inherit from Expression
 * @author Hélène Collavizza
 * @date June 2008
 */

public class IntegerVariable  extends IntegerExpression {

	public String name; 
	
	public IntegerVariable(String n) {
		name = n;
	}

	public String name() {
		return name;
	}

	public boolean equals(Object exp){
		if (!(exp instanceof IntegerVariable)) return false;
		IntegerVariable v = (IntegerVariable)exp;
		return name.equals(v.name)  ;
	}

	public int hashCode() {
		return name.hashCode() ;
	}

	public String toString() {
		return name;
	}

	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

	@Override
	public boolean equals(Expression e) {
		if (!(e instanceof IntegerVariable)) return false;
		IntegerVariable v = (IntegerVariable)e;
		return name.equals(v.name)  ;
	}


}
