package solvers.jsolver;


import ilog.rules.validation.concert.IloException;
import ilog.rules.validation.solver.IlcSolver;
import solvers.ConcreteSolver;
import expression.integer.BinaryIntegerExpression;
import expression.integer.MinusExpression;
import expression.integer.PlusExpression;
import expression.integer.TimeExpression;
import expression.logical.AndExpression;
import expression.logical.BinaryLogicalOperator;
import expression.logical.Comparator;
import expression.logical.EqualExpression;
import expression.logical.GreatExpression;
import expression.logical.LessEqualExpression;
import expression.logical.LessExpression;
import expression.logical.OrExpression;

/** class to define a concrete solver with JSolver
* @author Hélène Collavizza
 * @date June 2008
  *
 */
public class JSolver implements ConcreteSolver {
	
	protected IlcSolver solver; // the concrete solver
	
	// time of the last solve
	double solveTime;

	public JSolver() {
		try {
			solver = new IlcSolver();
			solveTime=0;
		} catch (IloException e) {
			System.out.println("error when creating JSolver solver" );
			e.printStackTrace();
		}
	}
	
	//	to search the next solution
	// PRECOND: a search has been started
	public boolean next() {
		boolean next = false;
		double before = solver.getElapsedTime();
//		solver.setPropagationTimeLimit(10000);
		try {
			next = solver.next();
		} catch (IloException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		solveTime = solver.getElapsedTime() - before;
		return next;
	}

	//	to start the search
	public void startSearch() {
		try {
			solver.newSearch();
		} catch (IloException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	//	to stop the search
	public void stopSearch() {
		try {
			solver.endSearch();
		} catch (IloException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	// to set a time limit
	public void setTimeLimit(int n) {
		getIlcSolver().setPropagationTimeLimit(n);
	}
	
	public double getSolveTime() {
		return solveTime;
	}
	
	// to know if the solver has been interrupted by the timeout
	public boolean hasBeenInterrupted() {
		return getIlcSolver().propagationHasBeenInterrupted();
	}
	
	// the concrete solver
	public  IlcSolver getIlcSolver() {
		return solver;
	}

	public String toString() {
		return solver.toString();
	}

	/////////////////////////////
	// Method to give the concrete syntax of the expressions
	
	// integer expressions
    public String getConcreteSyntax(BinaryIntegerExpression e) {
		if (e instanceof PlusExpression)
			return "sum";
		if (e instanceof MinusExpression)
			return "diff";
		if (e instanceof TimeExpression)
			return "prod";
		return "div";
    }
	
	// comparison expressions
	public String getConcreteSyntax(Comparator e) {
		if (e instanceof LessExpression)
			return "lt";
		if (e instanceof LessEqualExpression)
			return "le";
		if (e instanceof EqualExpression)
			return "eq";
		if (e instanceof GreatExpression)
			return "gt";
		return "ge";
	}

	// Boolean operators
	public String getConcreteSyntax(BinaryLogicalOperator e) {
		if (e instanceof OrExpression)
			return "or";
		if (e instanceof AndExpression)
			return "and";
		return "imply";
	}


}
