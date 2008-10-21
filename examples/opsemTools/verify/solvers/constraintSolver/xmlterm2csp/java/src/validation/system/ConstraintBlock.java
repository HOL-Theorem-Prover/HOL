package validation.system;

import expression.Expression;
import expression.logical.AndExpression;


/** To manage constraints of a program block
 * un-implemented methods depend on the concrete solver used
* @author Hélène Collavizza
 * @date June 2008
 *  */
public abstract class ConstraintBlock {

	/** add a constraint into a concrete solver*/
	protected abstract void addSimple(Expression e,IntegerVarBlock i);
	
	public void add(Constraint c,IntegerVarBlock i){
		Expression e = c.getExpression();
		if (isAnd(e))
			addMultiple(e,i);
		else addSimple(e,i);
	}
	
	// to add a conjunction as a list of conjuncts
	private void addMultiple(Expression e,IntegerVarBlock i) {
		Expression arg1 = ((AndExpression)e).arg1();
		Expression arg2 = ((AndExpression)e).arg2();
		if (isAnd(arg1))
			addMultiple(arg1,i);
		else addSimple(arg1, i);
		if (isAnd(arg2))
			addMultiple(arg2,i);
		else addSimple(arg2, i);
	}
	
	private boolean isAnd(Expression e){
		return (e instanceof AndExpression);
	}
	
}
