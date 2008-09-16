package solvers.gecodej;

import validation.system.TermSystem;

/** a class for a term system using GecodeJ 
 * this class only define the constructor to build concrete CSP
 * 
* @author Hélène Collavizza
 * @date June 2008 *
 */
public class GecodeJTermSystem extends TermSystem {

	
	public GecodeJTermSystem(String name, String pa,int f) {
		super(name,pa,f);
	}
	
	public String toString() {
		return super.toString() + " using GcodeJ";
	}
	
	@Override
	protected void setCSP(String n, int f) {
		csp = new GecodeJTermCSP("complete",f);
	}
	

}
