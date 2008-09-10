package java2opSem;



import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.checker.*;
import org.multijava.mjc.*;


/** to visit a JML specification and build a HOL term
 * 
 * uses jml-release.jar for parsing JML specifications
 * see http://sourceforge.net/project/showfiles.php?group_id=65346&package_id=62764&release_id=594123
 * for downloading JML tools
 * 
 * see http://www.cs.ucf.edu/~leavens/JML/
 * for information about JML
 * 
 * The HOL terms that correspond to the JML specification
 * of methods in a class are stored in a Map<String,String>.
 * The key is the name of the method and the associated 
 * value is the HOL term 
 * 
 * Since precondition, program and postcondition are evaluated
 * on a state (i.e finiteMap (name, value)), the term associated 
 * with the pre and the post condition is a lambda expression
 * on state.
 * 
 * Examples
 *   (i>=0 && j>=0 && k>= 0) is translated as:
 *         (\state.
 *         ScalarOf (state ' "i") >= 0 /\ ScalarOf (state ' "j") >= 0 /\
 *          ScalarOf (state ' "k") >= 0)
 *   (a[i] >= 0)  is translated as:
 *         (\state.
 *           (ArrayOf (state ' "a") ' (ScalarOf (state ' "i"))) >= 0)
 *
 * See details in README.txt.
 *
 * @version August 2008
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis
 */

public class Jml2opSemVisitor implements JmlVisitor {

	// jml.get("foo") returns the String which corresponds
	// to the jml specification of method foo
	private Map<String,String> jml;
	
	// current specification
	private String currentSpec = "";
	
	// true when parsing ensures statement
	// the postcondition is a lambda on 2 states
	// since it can express a relation between 
	// state before and state after execution of
	// the method
	private boolean isEnsures;
	
	// true when parsing expression inside
	// \old statement
	// inside \old, the state is the state before execution
	// of the method
	private boolean isOld;
	
	// set of variables declared as parameters
	// of the method
	// when parameter variables appear in 
	// ensures statements, then their old values
	// are used (i.e \old is implicit)
	// see http://www.eecs.ucf.edu/~leavens/JML//OldReleases/jmlrefman.pdf
	// p 77.
	private ArrayList<String> parameterVar;
	
	// to deal with negative numbers
	private boolean minus = false;
	
	// set of variables declared in JML ForAll or Exists
	// when parsing JML ForAll or Exists, the variable
	// associated with a quantifier does not depend 
	// on the current state
	// so we do not generate a lambda expression on state.	
	private ArrayList<String> quantifiedVar;
	
	// becomes true when the JML specification contains nodes
	// which are not yet handled
	private boolean error=false; 

    // constructor 
	// param is the list of parameters that have been found
	// during parsing of method signature
	public Jml2opSemVisitor (ArrayList<String> param) {
		jml = new HashMap<String,String>();
		quantifiedVar = new ArrayList<String>();
		isEnsures = false;
		isOld = false;
		parameterVar = param;
	}
	
	// ########### Functions for accessing specifications #####
	// to return the set of jml specifications
	public Map<String,String> getJml() {
		return jml;
	}

	public boolean hasError() {
		return error;
	}
	
	// ########### Functions for writing ##############
	
	private void write(String s) {
		this.currentSpec +=  s;
	}
	private void writeln(String s) {
		this.currentSpec += "\n" + s;
	}
	
	// to print the name of the state
	// state in requires statement
	// state1 in ensures statement inside a \old
	// state2 in ensures statement if not inside a \old
	private String stateName(){
		if (!isEnsures) return "state ";
		if (isOld) return "state1 ";
		return "state2 ";
	}

	// to print the name of the state for a variable.
	// the stae is:
	//    - state in requires statement
	//    - state1 in ensures statement inside a \old
	//    or if the variable is a parameter
	//    - state2 in ensures statement if not inside a \old
	private String stateName(String name){
		if (!isEnsures) return "state ";
		if (isOld) return "state1 ";
		// parameters are evaluated on initial state
		if (parameterVar.contains(name))
			return "state1 ";
		return "state2 ";
	}
	
	// general functions to visit the JML specification
	// ================================================
	
	// to visit the specification of all methods
	public void visitJmlClassDeclaration(JmlClassDeclaration self) {
		acceptAll(self.methods() );
	}

	public void visitJmlCompilationUnit(JmlCompilationUnit self) {
		JTypeDeclarationType[] tdecls = self.combinedTypeDeclarations();
		for (int i = 0; i < tdecls.length ; i++) {
		    tdecls[i].accept(this);
		}
	}
	
	public void visitJmlSpecification(JmlSpecification self) {
		JmlSpecCase[] specCases = self.specCases();
		visitSpecCases(specCases);
	}
	
	// private method to visit all specification cases
    private void visitSpecCases(JmlSpecCase[] specCases) {
		if (specCases != null) {
		    for (int i = 0; i < specCases.length; i++) {
		    	specCases[i].accept(this);
		    }
		}
	}

    // private method to visit all elements of an ArrayList
	private void acceptAll(ArrayList all ) {	
    	if (all != null) {
    		for (int i = 0; i < all.size(); i++) {
				JPhylum j = (JPhylum) all.get(i);
				j.accept(this);
			}
    	}
    }
	
	// add a specification for the current method
    public void visitJmlMethodDeclaration(JmlMethodDeclaration self ) {
    	String name = self.ident();
     	if (self.hasSpecification()) {
     		self.methodSpecification().accept(this);
     	}
     	jml.put(name, currentSpec);
     	currentSpec = "";
    }
    	
	public void visitJmlGenericSpecBody(JmlGenericSpecBody self) {
		JmlSpecBodyClause[] specClauses = self.specClauses();
		JmlGeneralSpecCase[] specCases = self.specCases();
		
		if (specClauses != null) {
		    for (int i = 0; i < specClauses.length; i++) {
			specClauses[i].accept(this);
		    }
		}
		if (specCases != null)
		    visitSpecCases(specCases);
	}

	public void visitJmlGenericSpecCase(JmlGenericSpecCase self) {
		JmlSpecVarDecl[] specVarDecls = self.specVarDecls();
		JmlRequiresClause[] specHeader = self.specHeader();
		JmlSpecBody specBody = self.specBody();
		
		if (specVarDecls != null) {
		    for (int i = 0; i < specVarDecls.length; i++) {
			specVarDecls[i].accept(this);
		    }
		}

		if (specHeader != null) {
		    for (int i = 0; i < specHeader.length; i++) {
			specHeader[i].accept(this);
		    }
		}

		if (specBody != null)
		    specBody.accept(this);
	}
	
	// requires clause
	public void visitJmlRequiresClause(JmlRequiresClause self) {
		self.predOrNot().accept(this);
		write("EndRequires");
	}
	
	// ensure clause
	public void visitJmlEnsuresClause(JmlEnsuresClause self) {
		isEnsures = true;
		self.predOrNot().accept(this);
		isEnsures = false;
	}
	
	// \result variable in JML specification
	// TODO: case where result is an array 
	public void visitJmlResultExpression(JmlResultExpression self) {
		write("ScalarOf (" + stateName() + "' \"Result\")");
	}
	
	public void visitJmlPredicate(JmlPredicate self) {
		self.specExpression().accept(this);
	}
	
	public void visitJmlSpecExpression(JmlSpecExpression self) {
		self.expression().accept(this);
	}
	
	public void visitParenthesedExpression(JParenthesedExpression self) {
		write("(");
		self.expr().accept(this);
		write(")");
	}
	
	// relational expressions
	public void visitJmlRelationalExpression(JmlRelationalExpression self) {
		String type="";
		switch(self.oper()) {
			case 14: type = "<"; break;
			case 15: type = "<="; break;
			case 16: type = ">"; break;
			case 17: type = ">="; break;
			case 30: type = ") ==> ("; break;
		}
		write("(");
		self.left().accept(this);
		write(type);
		self.right().accept(this);
		write(")");

	}
	
	public void visitEqualityExpression(JEqualityExpression self) {
		if (self.oper() == JEqualityExpression.OPE_NE) {
			write("~");
		}
		write("(");
		self.left().accept(this);
		write("=");
		self.right().accept(this);
		write(")");
	}
	
	// logical expressions
	public void visitConditionalOrExpression(JConditionalOrExpression self) {
		self.left().accept(this);
		write("\\/");
		self.right().accept(this);
	}
	
	public void visitConditionalAndExpression(JConditionalAndExpression self) {
		self.left().accept(this);
		write("/\\");
		self.right().accept(this);
	}
	
	// integer expressions
	public void visitOrdinalLiteral(JOrdinalLiteral self) {
		write((minus ? "~" : "") + self.toString());
	}
	
	public void visitAddExpression(JAddExpression self) {
		self.left().accept(this);
		write("+");
		self.right().accept(this);
	}
	
	public void visitDivideExpression(JDivideExpression self) {
		self.left().accept(this);
		write("/");
		self.right().accept(this);
	}
	
	public void visitMinusExpression(JMinusExpression self) {
		self.left().accept(this);
		write("-");
		self.right().accept(this);
	}
	
	public void visitMultExpression(JMultExpression self) {
		self.left().accept(this);
		write("*");
		self.right().accept(this);		
	}
		
	public void visitUnaryExpression(JUnaryExpression self) {
		String type = "";
		switch(self.oper()) {
			case 13: type = "~"; break;
			case 2: minus = true;
		}
		if (! minus) write(type);
		self.expr().accept(this);
		minus = false;
	}

	
	// variables
	public void visitJmlVariableDefinition(JmlVariableDefinition self) {
		write(self.ident());
	}

	// visit a variable name
	// if it is an access to the array length, then it ss
	// evaluated on "state" when parsing the precondition
	// else it is evaluated on state1
	public void visitNameExpression(JNameExpression self) {
		// access to array length
		if (self.getPrefix() != null && self.getName() == "length") {
			String st ;
			// if in precondition, the length is evaluated 
			// on state else on state1
			if (isEnsures)
				st = "state1 ";
			else 
				st = "state ";
			write("ScalarOf (" + st + "' \"" + self.getPrefix() + "Length\")" );
		}
		else {
			String name = self.toString();
			if (quantifiedVar.contains(name))
				write(name);
			else
				write("ScalarOf (" + stateName(name) + "' \"" + name + "\")");
		}
	}
	
	
	// \old statement
	// to use the value of the variable before execution
	// of the method	
	// self.specExpression() is the JmlSpecExpression
	// inside the \old statement
	// Restriction: the expression can't be a quantified 
	// expression
	public void visitJmlOldExpression(JmlOldExpression self) {
        isOld = true;
        self.specExpression().accept(this);
        isOld = false;
	}

	// to visit JML forall and exists statements
	// spec-quantified-expr ::= "(" quantifier quantified-var-decl "; [ [ predicate ] ";" ] spec-expression ")"
	// is translated as:
	//     ! v1 v2 ... vn . predicate(v1,...,vn) ==> spec-expression
	// when quantifier is \forall
	// and as
	//     ? v1 v2 ... vn . predicate(v1,...,vn) /\ spec-expression
	// where v1 v2 ... vn are the variables declared in quantified-var-decl
	public void visitJmlSpecQuantifiedExpression(JmlSpecQuantifiedExpression self) {

		// quantifier
		boolean isForAll = self.isForAll();
		if (isForAll)
			write("(!");
		else write("(?");

		// quantified-var-decl
		JVariableDefinition[] tab = self.quantifiedVarDecls();
		for (int i = 0; i < tab.length; i++) {
			quantifiedVar.add(tab[i].ident());
			write(tab[i].ident() + " ");
			// tab[i].accept(this);
		}
		
		// write "." after the name of the quantified variables
		write(". ");

		// predicate statisfied by the quantified variables
		if (self.hasPredicate()) {
			write("(");
			self.predicate().accept(this);
			write(")");
			// print logical operator that links the predicate
			// on quantified variables to the spec-expression
			if (isForAll)
				write("==>");
			else
				write("/\\");
		}
		
		// spec-expression
		write("(");
		self.specExpression().accept(this);
		write("))");
		
		// remove local variables associated with the quantifier
		// from the list of quantified variables
		for (int i = 0; i < tab.length; i++) {
			quantifiedVar.remove(tab[i].ident());
		}

	}
	
	// arrays
	/**  (a[i] >= 0)
	 *   is translated as:
	 *      (\state.
	 *           (ArrayOf (state' "a") ' (ScalarOf (state' "i"))) >= 0)
 	 * in a requires statement
	 * and as 
	 *         (\state1 state2.
	 *           (ArrayOf (state2' "a") ' (ScalarOf (state2' "i"))) >= 0)
	 * in ensures statement
     */
	public void visitArrayAccessExpression(JArrayAccessExpression self) {
		// name of the array
		String name = self.prefix().toString();
		// the state on which expression must be evaluated
		String st = stateName();
		// for statements such as \old(a)[i]
		if (self.prefix() instanceof JmlOldExpression){
			System.out.println("old in an array");
			name = ((JmlOldExpression)self.prefix()).specExpression().toString();
			st = "state1 ";
		}
		write ("(ArrayOf (" + st + "' \"" + name + "\") ' ");
		write("(");
		// visit the array index
		self.accessor().accept(this);
		write(")");
		write(")");
	}
	//====================================================
	// here are non implemented methods 
	// to parse all possible nodes in JML
	// this is required because Jml2opSem implements JmlVisistor

	public void visitArrayDimsAndInit(JArrayDimsAndInits self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitBooleanLiteral(JBooleanLiteral self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}
		
	public void visitArrayInitializer(JArrayInitializer self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitArrayLengthExpression(JArrayLengthExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAbruptSpecBody(JmlAbruptSpecBody self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAbruptSpecCase(JmlAbruptSpecCase self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAccessibleClause(JmlAccessibleClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAssertStatement(JmlAssertStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAssignableClause(JmlAssignableClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAssumeStatement(JmlAssumeStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAxiom(JmlAxiom self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlBehaviorSpec(JmlBehaviorSpec self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlBreaksClause(JmlBreaksClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlCallableClause(JmlCallableClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlCapturesClause(JmlCapturesClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlClassBlock(JmlClassBlock self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlClassOrGFImport(JmlClassOrGFImport self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlCodeContract(JmlCodeContract self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlConstraint(JmlConstraint self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlConstructorDeclaration(JmlConstructorDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlConstructorName(JmlConstructorName self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlContinuesClause(JmlContinuesClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlDebugStatement(JmlDebugStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlDeclaration(JmlDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlDivergesClause(JmlDivergesClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlDurationClause(JmlDurationClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlDurationExpression(JmlDurationExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlElemTypeExpression(JmlElemTypeExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExample(JmlExample self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExceptionalBehaviorSpec(JmlExceptionalBehaviorSpec self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExceptionalExample(JmlExceptionalExample self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExceptionalSpecBody(JmlExceptionalSpecBody self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExceptionalSpecCase(JmlExceptionalSpecCase self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExpression(JmlExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlExtendingSpecification(JmlExtendingSpecification self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlFieldDeclaration(JmlFieldDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlForAllVarDecl(JmlForAllVarDecl self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlFormalParameter(JmlFormalParameter self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlFreshExpression(JmlFreshExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlGeneralSpecCase(JmlGeneralSpecCase self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlGuardedStatement(JmlGuardedStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlHenceByStatement(JmlHenceByStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInGroupClause(JmlInGroupClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInformalExpression(JmlInformalExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInformalStoreRef(JmlInformalStoreRef self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInitiallyVarAssertion(JmlInitiallyVarAssertion self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInterfaceDeclaration(JmlInterfaceDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInvariant(JmlInvariant self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInvariantForExpression(JmlInvariantForExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlInvariantStatement(JmlInvariantStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlIsInitializedExpression(JmlIsInitializedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlLabelExpression(JmlLabelExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlLetVarDecl(JmlLetVarDecl self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlLockSetExpression(JmlLockSetExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlLoopInvariant(JmlLoopInvariant self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlLoopStatement(JmlLoopStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMapsIntoClause(JmlMapsIntoClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMaxExpression(JmlMaxExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMeasuredClause(JmlMeasuredClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMethodName(JmlMethodName self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMethodSpecification(JmlMethodSpecification self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlModelProgram(JmlModelProgram self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMonitorsForVarAssertion(JmlMonitorsForVarAssertion self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlName(JmlName self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNode(JmlNode self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNonNullElementsExpression(JmlNonNullElementsExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNondetChoiceStatement(JmlNondetChoiceStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNondetIfStatement(JmlNondetIfStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNormalBehaviorSpec(JmlNormalBehaviorSpec self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNormalExample(JmlNormalExample self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNormalSpecBody(JmlNormalSpecBody self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNormalSpecCase(JmlNormalSpecCase self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNotAssignedExpression(JmlNotAssignedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlNotModifiedExpression(JmlNotModifiedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlOnlyAssignedExpression(JmlOnlyAssignedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlPackageImport(JmlPackageImport self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlReachExpression(JmlReachExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlReadableIfVarAssertion(JmlReadableIfVarAssertion self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlRedundantSpec(JmlRedundantSpec self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlRefinePrefix(JmlRefinePrefix self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlRepresentsDecl(JmlRepresentsDecl self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlReturnsClause(JmlReturnsClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSetComprehension(JmlSetComprehension self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSetStatement(JmlSetStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSignalsClause(JmlSignalsClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSignalsOnlyClause(JmlSignalsOnlyClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSpaceExpression(JmlSpaceExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSpecBody(JmlSpecBody self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSpecStatement(JmlSpecStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlSpecVarDecl(JmlSpecVarDecl self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlStoreRef(JmlStoreRef self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlStoreRefExpression(JmlStoreRefExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlStoreRefKeyword(JmlStoreRefKeyword self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlTypeExpression(JmlTypeExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlTypeOfExpression(JmlTypeOfExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlUnreachableStatement(JmlUnreachableStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlVariantFunction(JmlVariantFunction self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlWhenClause(JmlWhenClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlWorkingSpaceClause(JmlWorkingSpaceClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlWorkingSpaceExpression(JmlWorkingSpaceExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlWritableIfVarAssertion(JmlWritableIfVarAssertion self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitAssertStatement(JAssertStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitAssignmentExpression(JAssignmentExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitBitwiseExpression(JBitwiseExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitBlockStatement(JBlock self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitBreakStatement(JBreakStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitCastExpression(JCastExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitCatchClause(JCatchClause self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitCharLiteral(JCharLiteral self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitClassBlock(JClassBlock self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitClassDeclaration(JClassDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitClassExpression(JClassExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitClassOrGFImport(JClassOrGFImport self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitCompoundAssignmentExpression(JCompoundAssignmentExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;	
	}

	public void visitCompoundStatement(JCompoundStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitConditionalExpression(JConditionalExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitConstructorBlock(JConstructorBlock self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitConstructorDeclaration(JConstructorDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitContinueStatement(JContinueStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitDoStatement(JDoStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitEmptyStatement(JEmptyStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitExplicitConstructorInvocation(JExplicitConstructorInvocation self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitExpressionListStatement(JExpressionListStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitExpressionStatement(JExpressionStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitFieldDeclaration(JFieldDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitFieldExpression (JClassFieldExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitForStatement(JForStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitFormalParameters(JFormalParameter self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitGenericFunctionDecl(MJGenericFunctionDecl self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitIfStatement(JIfStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitInitializerDeclaration(JInitializerDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitInstanceofExpression(JInstanceofExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitInterfaceDeclaration(JInterfaceDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitLabeledStatement(JLabeledStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitLocalVariableExpression(JLocalVariableExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitMathModeExpression(MJMathModeExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitMethodCallExpression(JMethodCallExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitMethodDeclaration(JMethodDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitModuloExpression(JModuloExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitNewAnonymousClassExpression(JNewAnonymousClassExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitNewArrayExpression(JNewArrayExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitNewObjectExpression(JNewObjectExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitNullLiteral(JNullLiteral self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitPackageImport(JPackageImport self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitPackageName(JPackageName self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitPostfixExpression(JPostfixExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitPrefixExpression(JPrefixExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitRealLiteral(JRealLiteral self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitRelationalExpression(JRelationalExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitReturnStatement(JReturnStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitShiftExpression(JShiftExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitStringLiteral(JStringLiteral self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitSuperExpression(JSuperExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitSwitchGroup(JSwitchGroup self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitSwitchLabel(JSwitchLabel self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitSwitchStatement(JSwitchStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitSynchronizedStatement(JSynchronizedStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitThisExpression(JThisExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitThrowStatement(JThrowStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitTopLevelMethodDeclaration(MJTopLevelMethodDeclaration self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitTryCatchStatement(JTryCatchStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitTryFinallyStatement(JTryFinallyStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitTypeDeclarationStatement(JTypeDeclarationStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitTypeNameExpression(JTypeNameExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitUnaryPromoteExpression(JUnaryPromote self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitVariableDeclarationStatement(JVariableDeclarationStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitVariableDefinition(JVariableDefinition self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitWarnExpression(MJWarnExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitWhileStatement(JWhileStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlAssignmentStatement(JmlAssignmentStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlMethodNameList(JmlMethodNameList self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlOnlyAccessedExpression(JmlOnlyAccessedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlOnlyCalledExpression(JmlOnlyCalledExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlOnlyCapturedExpression(JmlOnlyCapturedExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlPreExpression(JmlPreExpression self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlPredicateKeyword(JmlPredicateKeyword self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitCompilationUnit(JCompilationUnit self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}

	public void visitJmlRefiningStatement(JmlRefiningStatement self) {
		System.out.println("Visiting method for class " + self.getClass() + "is not yet implemented"); 
		error=true;
	}
}


