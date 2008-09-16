package solvers.gecodej;


import static org.gecode.GecodeEnumConstants.INT_VAL_MIN;
import static org.gecode.GecodeEnumConstants.INT_VAR_SIZE_MIN;

import org.gecode.DFSIterator;
import org.gecode.IntRelType;
import org.gecode.IntVar;
import org.gecode.Space;
import org.gecode.VarArray;

import solvers.ConcreteSolver;
import expression.integer.BinaryIntegerExpression;
import expression.integer.MinusExpression;
import expression.integer.PlusExpression;
import expression.logical.AndExpression;
import expression.logical.BinaryLogicalOperator;
import expression.logical.Comparator;
import expression.logical.EqualExpression;
import expression.logical.GreatExpression;
import expression.logical.LessEqualExpression;
import expression.logical.LessExpression;
import expression.logical.OrExpression;

/** class to define a concrete solver with the Java interface of 
 *  Gecode
 * @author Hélène Collavizza
 * @date June 2008
 */
public class GecodeJ extends Space implements ConcreteSolver  {

	DFSIterator<Space> search;// to launch the search
   // the GecodeJ variables which are shared with GecodeJIntVarBlock
	//required beacuse the solution returned by next wil be
	// of type GecodeJ. So we can get the variable values
	protected VarArray<IntVar> var; 

	
	public GecodeJ() {
		super("GecodeJ solver");
	}
	
	// constructor required for copy (needed by search)
    public GecodeJ(Boolean shared, GecodeJ c) {
        super(shared,c);
        var = new VarArray<IntVar>(this, shared, c.var);
    }

	//	to search the next solution
	// PRECOND: a search has been started
	public boolean next() {
		boolean n = search.hasNext();
		Space s = search.next(); 
		var = ((GecodeJ)s).var;
		return n;
	}

	//	to start the search
      // default is DFS search
	public void startSearch() {
		// to branch and not only propagate
		org.gecode.Gecode.branch(this, var, INT_VAR_SIZE_MIN, INT_VAL_MIN);
		org.gecode.Options o = new org.gecode.Options();
		search = new DFSIterator<Space>(this,o);
	}

	//	to stop the search
	public void stopSearch() {
	}
	
	// the concrete solver
	public  GecodeJ getGecodeJSolver() {
		return this;
	}
	
	// to set a time limit
	public void setTimeLimit(int n) {
		//TODO
	}

	// to know if the solver has been interrupted by the timeout
	public boolean hasBeenInterrupted() {
		//TODO
		return false;
	}

	protected void setIntVar(VarArray<IntVar> v){
		var = v;
	}
	
	public String toString() {
        String res = "Current status of variables in GecodeJ\n";

        for (int i=0;i<var.size();i++){
        	IntVar v = var.get(i);
        	res += v.getName() +": ";
        	if (v.assigned())
        		res += v.val();
        	else 
        		res += "[" + v.min() + "," +
        		+ v.max() + "]";
            res+=" ";
        }
        return res;
	}

	/////////////////////////////
	// Method to give the concrete syntax of the expressions
	
	// integer expressions
    public String getConcreteSyntax(BinaryIntegerExpression e) {
		if (e instanceof PlusExpression)
			return "plus";
		if (e instanceof MinusExpression)
			return "minus";
		// PB: pas de produit ni de division
		return "no Expr operator";
//		if (e instanceof TimeExpression)
//			return "prod";
//		return "div";
    }
	
	// comparison expressions
	public IntRelType getConcreteSyntax(Comparator e) {
		if (e instanceof LessExpression)
			return IntRelType.IRT_LQ;
		if (e instanceof LessEqualExpression)
			return IntRelType.IRT_LE;
		if (e instanceof EqualExpression)
			return IntRelType.IRT_EQ;
		if (e instanceof GreatExpression)
			return IntRelType.IRT_GQ;
		return IntRelType.IRT_GR;
	}

	// Boolean operators
	public String getConcreteSyntax(BinaryLogicalOperator e) {
		if (e instanceof OrExpression)
			return "or";
		if (e instanceof AndExpression)
			return "and";
		return "imp";
	}

	public double getSolveTime() {
		// TODO Auto-generated method stub
		return 0;
	}
	
}
