package validation.solution;

/** a class to store and compute 
 * information about resolusion in a solver
 * @author Hélène Collavizza
 * @date June 2008 */

public class SolverStatus {
		
	// name of the system
	private String name;
	
	// current solving time 
	private double time;
	
	// number of solving
	private int solve;

	// number of fails
	private int fail;

	public SolverStatus(String n) {
		name=n;
		time=0;
		solve=0;
		fail=0;
	}
	
	public void addElapsedTime(double t) {
		time=time+t;
	}
	
	public double getTime() {
		return time/1000;
	}
	
	public void moreFail() {
		fail++;
	}
	
	public int getFail() {
		return fail;
	}
	
	public void moreSolve() {
		solve++;
	}
	public int getSolve() {
		return solve;
	}
	
	public String toString(){
		String s= "#########################\n";
		s+= "  Number of solve " + getSolve() +"\n";
		s+="  Number of fail " + getFail() +"\n";
		s+="  Total solving time " + getTime() +"s";
		s+= "\n#########################";
		return s;
	}
}
