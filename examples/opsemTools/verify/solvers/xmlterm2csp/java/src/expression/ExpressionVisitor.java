
package expression;

import validation.variables.IntegerVariable;
import expression.integer.BinaryIntegerExpression;
import expression.integer.IntegerLiteral;
import expression.logical.Comparator;
import expression.logical.ImpliesExpression;
import expression.logical.BinaryLogicalOperator;
import expression.logical.NotExpression;


/**
 * Interface for visitors
 * 
 * Each solver must implement this interface in order 
 * to define the concrete syntax of the expressions
 * 
 * Used in ConstraintBlock.addConstraint 
 * See for example method addSimple in class JSolverConstraintBlock.java
 *  
 * @author Lydie Blanchet: Polytech'Nice Sophia Antipolis
 */
public interface ExpressionVisitor {

	Object visit(IntegerVariable variable, Object data);

	Object visit(IntegerLiteral literal, Object data);
	
	Object visit(BinaryIntegerExpression expression, Object data);

	Object visit(BinaryLogicalOperator expression, Object data);

	Object visit(Comparator expression, Object data);

	Object visit(NotExpression expression, Object data);
		
}
