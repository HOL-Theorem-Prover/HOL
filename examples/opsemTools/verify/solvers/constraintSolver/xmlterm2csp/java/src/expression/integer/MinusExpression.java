package expression.integer;


import expression.Expression;


/** class to represent expression -
 * @author Hélène Collavizza
 * @date June 2008 
 */

public class MinusExpression extends BinaryIntegerExpression{

    public MinusExpression(Expression a1, Expression a2) {
    	super(a1,a2);
     }


    public String toString() {
    	return "( " + arg1.toString() + " - "+ arg2.toString() + " )";
    }
    
    public boolean equals(Expression exp){
    	return (exp instanceof MinusExpression) && 
    	arg1.equals(((MinusExpression)exp).arg1) && arg2.equals(((MinusExpression)exp).arg2);
    }

	
}
