package solvers.jsolver;

import validation.system.TermSystem;

/** a class for a term system using JSolver 
 * this class only define the constructor to build concrete CSP
 * 
 * @author Hélène Collavizza
 * @date June 2008
 */
public class JSolverTermSystem extends TermSystem {

	
	public JSolverTermSystem(String name, String pa, int f) {
		super(name,pa,f);
	}
	
	
	public String toString() {
		return super.toString() + " using JSolver";
	}

	
	@Override
	protected void setCSP(String n, int f) {
		csp = new JSolverTermCSP("complete",f);
	}
	

}
