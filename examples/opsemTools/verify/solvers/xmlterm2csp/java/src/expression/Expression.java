package expression;


/** interface for expressions 
 * To build expressions in a concrete CSP solver syntax, 
 * need to implement ExpressionVisitor
 * @author Hélène Collavizza
 * @date June 2008

 */

public interface Expression {
	
	public String toString();
	
	public Object structAccept(ExpressionVisitor visitor, Object data);

}
    