package validation.solution;

import java.io.PrintWriter;


/** class to represent a solution of the validation :
 * by default, the solution is empty
 * @author Hélène Collavizza
 * @date June 2008
 *
 */
public  class Solution  {
	
	// resolution time required to build this solution
	protected double time;
	
	// true if there is no solution
	protected boolean empty;

	// true if the solution can't be computed because of a time out
	protected boolean timeout;

	// the variables values
	protected SolutionValue sol;
	
	public Solution(){
		time = 0;
		empty=true;
		timeout=false;
	}
		
	/** to be overided by child classes 
	* by default, solution is empty */
	public  boolean empty() {
		return empty;
	}
		
	public void setTime(double t){
		time = t;
	}

	public double getTime(){
		return time/1000;
	}
	
	public void reset() {
		time=0;
		empty=true;
	}
	
	public void setSolution(boolean ok, SolutionValue s) {
		empty=ok;
		sol = s;		
	}
 
	// to set the solution when solve has a time out
	public void setTimeOut() {
		timeout=true;
		empty=false;
	}
	
	/** to be completed by child classes */
	public String toString() {
		String s = "---------\n";
		if (timeout)
			s+="Timeout\n";
		else
			if (empty()) 
				s+= "No solution";
			else {
				s+= "Solution: \n";
				s+=sol.toString();
			}
		s+= "\nResolution time : " + getTime() + "s\n";
		return s + "---------\n";
	}
	
	
	/** to be completed by child classes */
	public void toString(PrintWriter file) {
		String s = "";
		if (timeout)
			s+="Timeout";
		else 
			if (empty()) 
				s+= "No solution";
			else {
				s+="Solution:\n";
				s+=sol.toString();
			}
		s+= "\nResolution time : " + getTime() + "s\n";
		file.println( s + "");
	}
}

