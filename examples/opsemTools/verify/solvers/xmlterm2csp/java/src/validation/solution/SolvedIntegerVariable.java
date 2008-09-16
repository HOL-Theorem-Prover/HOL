package validation.solution;


/** class to represent an integer variable with its name and
 *  its domain
 * @author Hélène Collavizza
 * @date June 2008
 */
public class SolvedIntegerVariable {
	
	private String name;

	private int min;
	private int max;
	
	public SolvedIntegerVariable(int mi, int ma, String n){
		min = mi;
		max = ma;
		name = n;
	}
	
	
	public String toString() {
		String s = "(" + name + ",";
		if (min==max) s+=  min;
		else s+= "[" + min + ".." + max + "]";
		return s + ")";
	}
	

}
