package solvers;

import solvers.gecodej.GecodeJ;
import solvers.jsolver.JSolver;

/** class to represent a solver 
 * * @author Hélène Collavizza
 * @date June 2008
 */

public class Solver {

    // name of existing solvers
    public final static  int JSOLVER=1; //jsolver
    public final static  int ILOG=2; // ilog solver
    public final static  int CPLEX=3; // ilog cplex
    public final static  int JSOLVER_LINEAR=4; // jsolver for linear system
    public final static  int GECODEJ=5; // java interface of gecode

	/** solver name */
	private String name;
	
    /** the concrete solver */
	private ConcreteSolver s;
	
	public Solver(int n) {
		name = solverName(n);
		// only one solver
		s = createConcreteSolver(n);
	}
	
	// methods to handle concrete solver
	
	/** to set the concrete solver */
	private ConcreteSolver createConcreteSolver(int n){
		if (n==GECODEJ)
			return new GecodeJ();
		return new JSolver();
	}
	
	/** to set the solver name */
	private String solverName(int n) {
		switch (n) {
		case JSOLVER : return "JSolver4Verif";
		case ILOG: return "Ilog solver";
		case CPLEX: return "Ilog cplex";
		case GECODEJ: return "Gecode Java interface";
		}
		return "unknown solver";
	}
	
	public ConcreteSolver getConcreteSolver() {
		return s;
	}
	
	// methods to manage CSP resolution

	/** to enable a search process */
	public void startSearch() {
		s.startSearch();
	}
	
	/** to stop the search */
	public void stopSearch() {
		s.stopSearch();
	}

	/** true if current CSP has a next solution */
	public boolean next() {
		return s.next();
	}
	
	public void setTimeLimit(int n) {
		s.setTimeLimit(n);
	}
	
	public boolean hasBeenInterrupted() {
		return s.hasBeenInterrupted();
	}
	
	public double getSolveTime(){
		return s.getSolveTime();
	}
	

	public String toString() {
		return  s.toString();
	}
}
