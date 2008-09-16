package validation.variables;

import java.util.HashMap;

/** class to store integer variables of the validation system
* @author Hélène Collavizza
 * @date June 2008
 */

public class IntegerSymbolTable {

	// Integer variables indexed by their complete name
	private HashMap<String,IntegerVariable> var;


	public IntegerSymbolTable() {
		var = new HashMap<String,IntegerVariable>();
	}
	
	
	/** add a variable */
	public IntegerVariable addVar(String n)  {
		IntegerVariable v =new IntegerVariable(n);
		var.put(n, v);
		return v;
	}
	
	/** returns true if the table contains a variable with root name n */
	public boolean containsKey(String n){
		return var.containsKey(n);
	}
	
	/** returns the integer variable associated to the name n */
	public IntegerVariable get(String n){
		IntegerVariable v = var.get(n);
		return v;
	}


}