package solvers;

/** interface that must be implemented by concrete solvers
 * 
* @author Hélène Collavizza
 * @date June 2008 *
 */
public interface ConcreteSolver {

	public String toString();
	
//	/** concrete syntax of the comparators operators */
//	public String getConcreteSyntax(Comparator e);
//	
//	/** concrete syntax of the binary integer operators */
//	public String getConcreteSyntax(BinaryIntegerExpression e);
//
//	/** concrete syntax of the Boolean operators */
//	public String getConcreteSyntax(BinaryLogicalOperator e);

	/** to enable a search process */
	public void startSearch();
	
	/** to stop the search */
	public void stopSearch();

	/** true if current CSP as a next solution */
	public boolean next() ; 
	
	/** to set a time out */
	public void setTimeLimit(int n);
	
	/** to know if the search has been interrupted by the timeout */
	public boolean hasBeenInterrupted();
	
	/** to get the time of the last call to next() */
	public double getSolveTime();
	
}
