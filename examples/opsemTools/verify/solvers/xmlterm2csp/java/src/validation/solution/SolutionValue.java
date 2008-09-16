package validation.solution;


import ilog.rules.validation.solver.IlcIntVar;

import java.util.ArrayList;

//import org.gecode.IntVar;
//import org.gecode.VarArray;

/** a class to store the value of a solution (its variables with
 * their domains)
* @author Hélène Collavizza
 * @date June 2008
 */
public class SolutionValue {

	private ArrayList<SolvedIntegerVariable> variables; 
	
	public SolutionValue() {
		variables=null;
	}
	
	public SolutionValue(ArrayList<IlcIntVar> s){
		variables = new ArrayList<SolvedIntegerVariable>();
		for(IlcIntVar v: s){
			SolvedIntegerVariable vv;
			vv = new SolvedIntegerVariable(v.getDomainMin(),v.getDomainMax(),v.getName());
			variables.add(vv);
		}
	}
	
	//TODO : pourquoi dit-il constructeur dupliqué si on ne met pas le paramètre t ?
	public SolutionValue(ArrayList<IlcIntVar[]> tab,boolean t){
		variables = new ArrayList<SolvedIntegerVariable>();
		for(IlcIntVar[] v: tab){
			for (int i=0;i<v.length;i++) {
				SolvedIntegerVariable vv;
				vv = new SolvedIntegerVariable(v[i].getDomainMin(),v[i].getDomainMax(),v[i].getName());
				variables.add(vv);
			}
		}
	}
	
//	// to create solution for GecodeJ
//	public SolutionValue(VarArray<IntVar> s){
//		variables = new ArrayList<SolvedIntegerVariable>();
//		for(IntVar v: s){
//			SolvedIntegerVariable vv;
//			vv = new SolvedIntegerVariable(v.min(),v.max(),v.getName());
//			variables.add(vv);
//		}
//	}
	
		
	public void add(SolutionValue val){
		for (SolvedIntegerVariable s : val.variables) {
			variables.add(s);
		}
	}
	
	public String toString() {
		String s="";
		for(SolvedIntegerVariable v: variables){
			s+=v.toString()+"\n";
		}
		return s;
	}
	

}
