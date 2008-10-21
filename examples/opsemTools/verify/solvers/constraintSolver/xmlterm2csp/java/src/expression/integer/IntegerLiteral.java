package expression.integer;


import solvers.jsolver.JSolverIntVarBlock;
import ilog.rules.validation.solver.IlcIntExpr;
import expression.Expression;
import expression.ExpressionVisitor;

/** class to represent integer constants 
 * @author Hélène Collavizza
 * @date June 2008 
 */

public class IntegerLiteral extends IntegerExpression{
    String value;
    
    public IntegerLiteral(String v) {
    	value = v;
    }
    
    public IntegerLiteral() {
    	this("0");
    	
        }
    public String toString() {
    	return value + " ";
    }
    
    public int intValue() {
    	return (new Integer(value)).intValue();
    }
    
    public boolean equals(Expression exp){
    	return (exp instanceof IntegerLiteral) && value.equals(((IntegerLiteral)exp).value) ;
    }
        
	public Object structAccept(ExpressionVisitor visitor, Object data) {
		return visitor.visit(this, data);
	}

	@Override
	public int hashCode() {
		return value.hashCode();
	}
	
    // to create a concret constant in the concrete solver
	public IlcIntExpr toIlcInt(JSolverIntVarBlock s) {
		int val = new Integer(value).intValue();
		return s.addConstant(val);
	}
	


}
