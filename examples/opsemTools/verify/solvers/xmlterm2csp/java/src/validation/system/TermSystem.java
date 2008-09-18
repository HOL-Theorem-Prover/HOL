package validation.system;


import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;

import validation.solution.Solution;
import validation.solution.SolverStatus;
import validation.variables.IntegerSymbolTable;
import validation.variables.IntegerVariable;
import expression.Expression;

/** To store and manage constraint systems
 * this is an abstract class, need to define abstract methods to
 *  set the concrete CSP
* @author Hélène Collavizza
 * @date June 2008
 */ 

public abstract class TermSystem {
				
	// name of the file to verify
	private String name;
	
	// path to directory xmlterm2csp
	private String path;

	// the CSP that contains the term
	protected TermCSP csp;
	
	//	 abstract integer variables
	private IntegerSymbolTable intVar;	
	
	public  TermSystem(String n,String pa,int f) {
		name = n;
		path = pa;
		intVar = new IntegerSymbolTable();
		setCSP(n,f);
 	}
	
	/** must be implemented in child classes to 
	 *  define a concrete TermSystem, which means 
	 *  with a concrete solver
	 */
	protected abstract void setCSP(String n,int f);


	// methods to manage constraints and variables
	//////////////////////////////////////////////
	
	// methods to add constraints
	///////////////////////////
	
	/** add constraint c 
	 */
	public void addConstraint(Constraint c) {
		csp.addConstraint(c);
	}
	/** add expression e as a constraint 
	 */
	public void addConstraint(Expression e) {
		addConstraint(new Constraint(e));
	}
	
	/** to reset the constraint block as empty 
	 * i.e to have the same variables (intVar) with an empty
	 * set of constraints
	 * Used to validate the several specification cases
	 * @param n
	 * @return
	 */
	public void resetConstraintBlock() {
		csp.resetConstraintBlock();
	}
	
	// methods to add variables
	///////////////////////////
	
	
	// add an integer variable with name n
	public IntegerVariable addIntVar(String n) {
		IntegerVariable v = intVar.addVar(n);
		csp.addVar(v.name());
		return v;
	}

	// to know if the system constains variable n
	public boolean containsIntVar(String n){
		return intVar.containsKey(n);
	}
	
	/** returns the integer variable associated to the current renaming
	 * of variable with root name n */
	public IntegerVariable getIntVar(String n){
		return intVar.get(n);
	}
	

	// methods to solve the CSPs
	////////////////////////////

	/** get the solver status */
	public SolverStatus getSolverStatus() {
		return csp.status;
	}
	
	/** true if the csp  has a solution */
	public boolean hasSolution(){
		return csp.hasSolution();
	}
	
	/** solve the system and
	 * put the solution into result
	 */
	public void solve(Solution result,boolean print ) {
//		System.out.println(csp);
		// needs to get the variables values when the 
		// seach is active
		csp.startSearch();
		if (csp.next()){
			result.setSolution(false,csp.solution()) ; 
		}
		result.setTime(csp.s.getSolveTime());
		csp.stopSearch();
		if (print)
			System.out.println(result);
		printResult(result);
	}
	
	/** solve the system with a timeout and
	 * put the solution into result
	 */
	public void solve(Solution result,boolean print, int timeout ) {
//		System.out.println(csp);
		// set a time limit for solving
		csp.s.setTimeLimit(timeout);
		csp.startSearch();
		int solv = csp.next(timeout);
		if (solv==TermCSP.TIMEOUT) {
			System.out.println("\n###############" +
					 "\nTimeout with external solver ...");
			result.setTimeOut();
			result.setTime(timeout);
		}
		else {
			result.setTime(csp.s.getSolveTime());
			if (solv==TermCSP.SOLVE_OK){
				result.setSolution(false,csp.solution()) ; 
			}
		}
		csp.stopSearch();
		if (print)
			System.out.println(result);
		printResult(result);
	}
	
	/** to enable the search */
	private void startSearch(){
		csp.startSearch();
	}
	
	/** to stop the search */
	private void stopSearch(){
		csp.stopSearch();
	}
	
	//-----------------------------------
	// methods for printing
	////////////////////////////

	public String toStringCSP(){
		return csp.toString();
	}

	public String printStatus() {
		return csp.status.toString();
	}
	// to print the result time of the verification of
	// all specification cases 
    // the file will be read by HOL
	// to get the overall resolution time of CSP
	
	public void printStatusToFile() {
		// the output file
		PrintWriter fileOut=null;
		try {
			fileOut = new PrintWriter(new File(path + "/results/" + name + ".res"));
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (fileOut!=null) {
			// to follow the grammar of solutions
			fileOut.println("No solution");
			fileOut.println("Resolution time: " + csp.status.getTime() + "s");
           fileOut.close();
		}
		else 
			System.err.println("it was impossible to open the"+
					 " file to print results");
	}

	//to print the result into a file
	//this file will be read with hol
	private void printResult(Solution result) {
		// the output file
		PrintWriter fileOut=null;
		try {
			fileOut = new PrintWriter(new File(path + "/results/" + name + ".res"));//xmlterm2csp/
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (fileOut!=null) {
			result.toString(fileOut);
            fileOut.close();
		}
		else 
			System.err.println("it was impossible to open the"+
					 " file to print results");
	}
	
	public 	String toString() {
		String s = "";
		s += "\nConstraint system\n------------------------\n" 
			+ csp.toString();
		return s + "------------------------\n"  ;
	}

}
