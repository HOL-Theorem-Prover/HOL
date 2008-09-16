package solvers.gecodej;



import solvers.Solver;
import validation.system.TermCSP;

/** a concrete class for term CSP
 * with GecodeJ concrete solver
* @author Hélène Collavizza
 * @date June 2008 *
 */
public class GecodeJTermCSP extends TermCSP
{
			
	public GecodeJTermCSP(String n, int f) {
		super(n,Solver.GECODEJ,f);
	}

	/** used for JSolverLinearIntegerValidationCSP
	 */
	protected GecodeJTermCSP(String n, int solver, int f) {
		super(n,solver,f);
	}

	@Override
	protected void setIntVarBlock(Solver s, int f) {
		GecodeJ js = (GecodeJ)s.getConcreteSolver();
		intVar = new GecodeJIntVarBlock(js,f);
	}
	

	@Override
	protected void setConstraintBlock(Solver s) {
		GecodeJ js = (GecodeJ)s.getConcreteSolver();
		constr = new GecodeJConstraintBlock(js);		
	}


	@Override
	public String toString() {
		return s.toString();
	}

	@Override
	protected void resetConstraintBlock() {
		((GecodeJConstraintBlock)constr).reset();
	}


}
