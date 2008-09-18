package validation;

import java.io.File;

import solvers.Solver;
import validation.visitor.XMLVisitAndValidate;
import exception.AnalyzeException;
import exception.ConstraintException;
import exception.ValidationException;

/** class to represent a validation from a xml file
* @author Hélène Collavizza
 * @date June 2008
*/


public class Validation {

	private String name; // name of xml file
	private String path; // path to directory xmlterm2csp
	private int format; // integer format size
	private boolean all; // to know if we want to verify if a path is possible
	private int solver;// solver name
	private int timeout; // timeout for solve in mili second
						// -1 if no timeout
	
	public Validation(String n, String pa,String s,int f,boolean p, int t) {
		name = n;
		path = pa;
		format = f;  
		all = p;
		solver = getSolver(s);
		timeout = t;
	}
	
	// constructors with default solver = JSolver
	public Validation(String n, String pa,int f,boolean p) {
		this(n,pa,"JSOLVER",f,p,-1);
	}

	public Validation(String n, String pa,boolean p) {
		this(n,pa,"JSOLVER",8,p,-1);
	}
	
	public Validation(String n,String pa) {
		this(n,pa,"JSOLVER",8,false,-1);
	}


	
	// parse the xml file
	// if testPath then test if the current path is feasible
	// else validate the path in the program decribed by
	// a precondition, a path, a final state and a postcondition
	protected void verify() throws AnalyzeException,ConstraintException, ValidationException {
		// visite du xml et generation du fichier de contrainte
		XMLVisitAndValidate xvv = new XMLVisitAndValidate(name,path,format,solver);
		if (all)
			xvv.validateAll(timeout);
		else
			xvv.validate(timeout);
	}


	public String toString() {
		String s = "bench name : " + name;
		return s;
	}

	private int getSolver(String s){
		int solver;
		if (s.equals("JSolver")) solver = Solver.JSOLVER;
		else if (s.equals("JSolverLinear")) solver = Solver.JSOLVER_LINEAR;
		else if (s.equals("ILOG")) solver = Solver.ILOG;
		else if (s.equals("CPLEX")) solver = Solver.CPLEX;
		else solver = Solver.GECODEJ;
		return solver;
	}

}

