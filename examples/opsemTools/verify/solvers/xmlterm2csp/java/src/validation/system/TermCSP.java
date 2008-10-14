package validation.system;


import solvers.Solver;
import validation.solution.SolutionValue;
import validation.solution.SolverStatus;
import validation.variables.IntegerVariable;


/** A CSP searching solution for a term
 * 
 * Takes as inputs had hoc types Constraint, Expression, Variable
 * used to parse the xml intermediate form
 * Store this information in a concrete solver
 * 
 * Derive this class to create a concrete TermCSP
 * 
* @author Hélène Collavizza
 * @date June 2008
 *  */

public abstract class TermCSP {
    
	// constant to know the current status of solving
	public static final int SOLVE_OK = 0; // a solution
	public static final int SOLVE_KO = 1; // no solution
	public static final int TIMEOUT = 2; // time out

//	// delta to decide if there was a timeout
//	private static final int DELTA=50;

	/** the solver*/
	protected Solver s;
	
	protected SolverStatus status;
	
	/** the CSP name */
	protected String name;
	
	/** the constraints  */
	protected ConstraintBlock constr;
	
	/** the variables */
	protected IntegerVarBlock intVar;
	
	
	/** A term CSP with a name and a solver*/ 
	public TermCSP(String n,int solverType,int f) {
		name = n;
		status = new SolverStatus(n);
		s = new Solver(solverType);
		setConstraintBlock(s);
		setIntVarBlock(s,f);
	}
		
	/** to be redefined to set a concrete solver 
	 * for the constraint block */
	protected abstract void setConstraintBlock(Solver s) ;

	/** to be redefined to reset the concrete solver 
	 * remove all constraints  */
	protected abstract void resetConstraintBlock() ;

	/** to be redefined to set a concrete solver 
	 * for the integer variable block block */
	protected abstract void setIntVarBlock(Solver s, int f);

	
	//////////////////////////////////////
	// methods for solving
	
	/** to enable a search process */
	public void startSearch() {
		s.startSearch();
	}
	
	/** to stop the search */
	public void stopSearch(){
		s.stopSearch();
	}

	/** true if current CSP as a next solution 
	 * PRE: search has been started
	 */
	public boolean next() {
		status.moreSolve();
		boolean next = s.next();
		status.addElapsedTime(s.getSolveTime());
		if (!next)
			status.moreFail();
		return next;
	}
	
	/** to find the next solution using a timeout 
	 * @param n timeout value
	 * @return SOLVE_OK, SOLVE_KO or  TIMEOUT 
	 */
	public int next(int n) {
		// to set up the status
		status.moreSolve();
		int result;
		boolean ne = s.next();
		if (s.hasBeenInterrupted()){
			result = TIMEOUT;
			status.addElapsedTime(n);
		}
		else {
			status.addElapsedTime(s.getSolveTime());
			if (ne)
				result = SOLVE_OK;
			else { 
				result = SOLVE_KO;
				status.moreFail();
			}
		}
//		// resolution has been stopped with time out
//		// need to compare time for solving and n
//		// a delta is used because values can differ slightly
//		if (Math.abs(n-s.getSolveTime())<=DELTA) {
//			result=TIMEOUT;
//			System.out.println("Time out with JSolver ...");
//		}
		return result;
	}
	
	// to test if the current system has a solution
	public boolean hasSolution() {
		boolean has = false;
		startSearch();
		has = next();
		stopSearch();
		return has;
	}
	
//	/** to know the current elapsed time */
//	public double getElapsedTime() {
//		return status.getElapsedTime();
//	}
	
	/** to know the current  time */
	public double getTime() {
		return status.getTime();
	}
	
	/** to return the status */
	public SolverStatus getStatus() {
		return status;
	}

	
	//////////////////////////////////////
	// methods for adding constraints

	/** add a constraint */
	public  void addConstraint(Constraint c) {
		constr.add(c,intVar);
	}

	//////////////////////////////////////
	// methods to manage variables
	
	/** add integer variable */
	public  void addVar(IntegerVariable v) {
		intVar.addVar(v);
	}

	/** add integer variable */	
	public  void addVar(String n){
		intVar.addVar(n);
	}
	
	//////////////////////////////////////
	// methods to manage solutions

	// PRECOND: a search must have been started
	public SolutionValue solution() {
		SolutionValue intVal = intVar.solution();
		return intVal;
	}
	
	
}
