package solvers.jsolver;

import ilog.rules.validation.concert.IloException;
import ilog.rules.validation.solver.IlcConstraint;
import ilog.rules.validation.solver.IlcSolver;

import java.util.ArrayList;

import validation.system.ConstraintBlock;
import validation.system.IntegerVarBlock;
import expression.Expression;


/** a class to store constraints of a Java block
 * allow to perform backtrak on the blocks
* @author Hélène Collavizza
 * @date June 2008
 *  */
public class JSolverConstraintBlock  extends ConstraintBlock{
	
    // the JSolver constraints
	private ArrayList<IlcConstraint> constr; 	
	
	// the concrete solver
	private JSolver s; 

	protected JSolverConstraintBlock(JSolver s) {
		this.s = s;
		constr = new ArrayList<IlcConstraint>();
	}
	
	
	//--------------------------
	// methods to handle constraints

	// adding constraints
	
	/** add constraints */
	protected void addSimple(Expression e,IntegerVarBlock intVar) {
		// the visitor to parse Constraints and build IlcConstraint
		JSolverExpressionVisitor visitor =new JSolverExpressionVisitor((JSolverIntVarBlock)intVar,s);
		Object constr = e.structAccept(visitor, null);
		addIlcConstraint((IlcConstraint)constr);
	}

	
	/** add a ilog constraint */
	private void addIlcConstraint(IlcConstraint c){
		getIlcSolver().add(c);
		constr.add(c); 
	}
	

	/** returns the concrete JSolver
	 * used when parsing IntegerExpression
	 */
	public IlcSolver getIlcSolver() {
		return s.getIlcSolver();
	}


	/** to remove all the constraints */
	public void reset() {
		IlcSolver solver = getIlcSolver();
		// restoring constraints
		for (int i = constr.size()-1; i>=0; i--) {
			IlcConstraint c = constr.get(i);
			try {
				solver.remove(c);
			} catch (IloException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			constr.remove(i);
		}
	}
}
