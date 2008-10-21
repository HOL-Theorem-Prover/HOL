package solvers.jsolver;

import ilog.rules.validation.concert.IloException;
import ilog.rules.validation.solver.IlcIntExpr;
import ilog.rules.validation.solver.IlcIntVar;
import ilog.rules.validation.solver.IlcSolver;

import java.util.ArrayList;
import java.util.HashMap;

import validation.solution.SolutionValue;
import validation.system.IntegerVarBlock;
import validation.variables.IntegerVariable;

/** a class to store integer variables of a Java block
 * as IlcSolver integer variables
 * @author Hélène Collavizza
 * @date June 2008
 *  
 */
public class JSolverIntVarBlock implements IntegerVarBlock {

	private int vMin;
	private int vMax;

	// variables
	protected ArrayList<IlcIntVar> var; // the JSolver variables
	
	protected HashMap<String, Integer> varIndex; // variable index/name association table 
	protected int indexVar; // current index of variable
		
	// the concrete solver
	public JSolver s; 
	
	protected JSolverIntVarBlock(JSolver s,int f) {
		this.s=s;
		var = new ArrayList<IlcIntVar>();
		varIndex = new HashMap<String, Integer>();
		indexVar=0;
		// integers coded on f bits
		long val = (long) Math.pow(2, f-1);
		vMin = -(int)val;
		vMax = (int)(val-1);
	}

	//--------------------------
	// methods to handle variables
	
	/** add integer variable */
	public void addVar(IntegerVariable v) {
		addVar(v.name());
	}

	
	/** add a variable indexed with its name
	 * @param name
	 * @param vMin
	 * @param vMax
	 */
	public void addVar(String name){
		try {
			IlcIntVar v = getIlcSolver().intVar(vMin,vMax,name);
			addVar(v,name);
		} catch (IloException e) {
			System.err.println("error when adding var in JSolver constraint system" );
			e.printStackTrace();
		}
	}

	/** add a variable and associate it to a name and an index */
	private void addVar(IlcIntVar v,String name) {
		var.add(indexVar, v);
		varIndex.put(name,new Integer(indexVar));
		indexVar++;
	}
	
	// to add a constant and returns the IlcIntExpr
	public IlcIntExpr addConstant(int val) {
		return getIlcSolver().constant(val);
	}	
	
	/* returns a solution */
	public SolutionValue solution() {
		return new SolutionValue(var);
	}


	/** returns a variable accessed by its name */
	protected IlcIntVar getVar(String name) {
//		System.out.println("!!!!!!!!!!!!!!!" + name);
		int index = varIndex.get(name).intValue();
		return var.get(index);
	}
	

	/** print the variables */
	public String printVar() {
		String s="";
		for (IlcIntVar v : var)
			s += v.toString() + "\n";
		return s;
	}


	/** returns the JSolver variable of name "name"
	 * used when parsing IntegerExpression to build expressions
	 * with concrete JSolver syntax of variables
	 */
	public IlcIntVar getJSolverVar(String name) {
		return getVar(name);
	}

	/** returns the concrete JSolver
	 * used when parsing IntegerExpression
	 */
	public IlcSolver getIlcSolver() {
		return ((JSolver)s).getIlcSolver();
	}

}
