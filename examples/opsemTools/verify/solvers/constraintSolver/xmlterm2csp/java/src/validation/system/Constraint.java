package validation.system;

import expression.Expression;

/**
 * Class to represent constraints
 * @author Hélène Collavizza
 * @date June 2008
 */
public class Constraint {
    private Expression expr; 

    public Constraint() {
    	expr=null;
    }

    public Constraint(Expression b) {
    	expr=b;
    }

    public String toString() {
    	String result = "";
    	if (expr!=null) result = expr.toString();
    	return result;
    }
        
    public Expression getExpression(){
    	return expr;
    }
    
    
}
