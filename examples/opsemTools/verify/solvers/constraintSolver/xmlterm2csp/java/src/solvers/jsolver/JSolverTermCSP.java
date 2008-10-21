package solvers.jsolver;



import solvers.Solver;
import validation.system.TermCSP;

/** a concrete class for term CSP
 * with JSolver concrete solver
 * 
* @author Hélène Collavizza
 * @date June 2008 
 */
public class JSolverTermCSP extends TermCSP
{
			
	public JSolverTermCSP(String n, int f) {
		super(n,Solver.JSOLVER,f);
	}

	/** used for JSolverLinearIntegerValidationCSP
	 */
	protected JSolverTermCSP(String n, int solver, int f) {
		super(n,solver,f);
	}

	@Override
	protected void setIntVarBlock(Solver s, int f) {
		JSolver js = (JSolver)s.getConcreteSolver();
		intVar = new JSolverIntVarBlock(js,f);
	}
	

	@Override
	protected void setConstraintBlock(Solver s) {
		JSolver js = (JSolver)s.getConcreteSolver();
		constr = new JSolverConstraintBlock(js);		
	}


	@Override
	public String toString() {
		return s.toString();
	}

	@Override
	protected void resetConstraintBlock() {
		((JSolverConstraintBlock)constr).reset();
	}


}
