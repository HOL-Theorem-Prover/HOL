package solvers.gecodej;

import java.util.ArrayList;

import org.gecode.BExpr;

import validation.system.ConstraintBlock;
import validation.system.IntegerVarBlock;
import expression.Expression;


/** a class to store constraints of a Java block
 * allow to perform backtrak on the blocks
 * @author Hélène Collavizza
 * @date June 2008 */

public class GecodeJConstraintBlock  extends ConstraintBlock{
	
    // the GecodeJ expressions that must be posted
	private ArrayList<BExpr> expr; 	
	
	// the concrete solver
	private GecodeJ s; 

	protected GecodeJConstraintBlock(GecodeJ s) {
		this.s = s;
		expr = new ArrayList<BExpr>();
	}
	
	
	//--------------------------
	// methods to handle constraints

	// adding constraints
	
	/** add constraints */
	protected void addSimple(Expression e,IntegerVarBlock intVar) {
		// the visitor to parse Constraints and build IlcConstraint
		GecodeJExpressionVisitor visitor =new GecodeJExpressionVisitor((GecodeJIntVarBlock)intVar,s);
		System.out.println(e);
		Object constr = e.structAccept(visitor, null);
		addConstraint((BExpr)constr);
	}

	
	/** add a ilog constraint */
	private void addConstraint(BExpr c){
		System.out.println(getGecodeJSolver());
		System.out.println("expr : " + c);
		org.gecode.Gecode.post(getGecodeJSolver(),c);
		expr.add(c); 
	}
	

	/** returns the concrete JSolver
	 * used when parsing IntegerExpression
	 */
	public GecodeJ getGecodeJSolver() {
		return s.getGecodeJSolver();
	}


	/** to remove all the constraints */
	public void reset() {
		//TODO
		
//		IlcSolver solver = getIlcSolver();
//		// restoring constraints
//		for (int i = expr.size()-1; i>=0; i--) {
//			IlcConstraint c = expr.get(i);
//			try {
//				solver.remove(c);
//			} catch (IloException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//			expr.remove(i);
//		}
	}
}
