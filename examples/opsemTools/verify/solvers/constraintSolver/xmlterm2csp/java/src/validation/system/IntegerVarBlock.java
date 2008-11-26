package validation.system;


import validation.solution.SolutionValue;
import validation.variables.IntegerVariable;

/** a class to store integer variables of a Java block
 * allow to perform backtrak on the blocks
 * @author helen
 *
 */
public interface IntegerVarBlock {

	
	//--------------------------
	// methods to handle variables

	/** add integer variable */
	public  void addVar(IntegerVariable v)	;

	/** add integer variable */	
	public  void addVar(String n);

	/** print the variables */
	public String printVar() ;

	/** if next(), return a solution 
	 * */
	public SolutionValue solution() ;

}
