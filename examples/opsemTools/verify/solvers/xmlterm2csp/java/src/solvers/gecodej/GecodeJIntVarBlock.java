package solvers.gecodej;



import java.util.HashMap;

import org.gecode.Expr;
import org.gecode.IntVar;
import org.gecode.VarArray;

import validation.solution.SolutionValue;
import validation.system.IntegerVarBlock;
import validation.variables.IntegerVariable;

/** a class to store integer variables of a Java block
 * as IlcSolver integer variables
 * @author Hélène Collavizza
 * @date June 2008 */

public class GecodeJIntVarBlock implements IntegerVarBlock {

	private int vMin;
	private int vMax;

	// variables
	protected VarArray<IntVar> var; // the GecodeJ variables
	
	// 
	
	protected HashMap<String, Integer> varIndex; // variable index/name association table 
	protected int indexVar; // current index of variable
		
	// the concrete solver
	public GecodeJ s; 
	
	protected GecodeJIntVarBlock(GecodeJ s,int f) {
		this.s=s;
		var = new VarArray<IntVar>();
		// to share variables with the concrete solver
		s.setIntVar(var);
		varIndex = new HashMap<String, Integer>();
		indexVar=0;
		// integers coded on f bits
		long val = (long) Math.pow(2, f-1);
		vMin = (int)val;
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
		IntVar v = new IntVar(getGecodeJSolver(),name,vMin,vMax);
		addVar(v,name);
	}

	/** add a variable and associate it to a name and an index */
	private void addVar(IntVar v,String name) {
		var.add(indexVar, v);
		varIndex.put(name,new Integer(indexVar));
		indexVar++;
	}
	
	// to add a constant and returns the IlcIntExpr
	public Expr addConstant(int val) {
		return new Expr(val);
	}	
	
	/* returns a solution */
	public SolutionValue solution() {
		return new SolutionValue(getGecodeJSolver().var);
	}


	/** returns a variable accessed by its name */
	protected IntVar getVar(String name) {
//		System.out.println("!!!!!!!!!!!!!!!" + name);
		int index = varIndex.get(name).intValue();
		return var.get(index);
	}
	

	/** print the variables */
	public String printVar() {
		String s="";
		for (IntVar v : var)
			s += v.toString() + "\n";
		return s;
	}


	/** returns the GcodeJ variable of name "name"
	 * used when parsing IntegerExpression to build expressions
	 * with concrete GcodeJ syntax of variables
	 */
	public IntVar getGecodeJVar(String name) {
		return getVar(name);
	}

	/** returns the concrete GecodeJ
	 * used when parsing IntegerExpression
	 */
	public GecodeJ getGecodeJSolver() {
		return ((GecodeJ)s).getGecodeJSolver();
	}

}
