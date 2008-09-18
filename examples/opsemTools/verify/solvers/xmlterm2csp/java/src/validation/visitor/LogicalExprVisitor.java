package validation.visitor;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

import validation.system.TermSystem;
import validation.util.ChildIterator;
import exception.AnalyzeException;
import exception.ConstraintException;
import expression.Expression;
import expression.logical.AndExpression;
import expression.logical.EqualExpression;
import expression.logical.ImpliesExpression;
import expression.logical.LessEqualExpression;
import expression.logical.LessExpression;
import expression.logical.LogicalExpression;
import expression.logical.NotExpression;
import expression.logical.OrExpression;
import expression.logical.GreatEqualExpression;
import expression.logical.GreatExpression;


/** Class to parse XML logical expressions and create LogicalExpression
 * @author Hélène Collavizza
 * @date June 2008
 */

public class LogicalExprVisitor extends XMLVisitor {
	

	// <!ENTITY % ExprLogical "(IDSExprLogicalOr|IDSExprLogicalAnd|IDSExprLogicalNot
	// |IDSExprParenthesis|IDSExprEquality|IDSExprSup|IDSExprInf)">  
	// if b, then save sub-expressions in boolean table of p
	public static LogicalExpression parse(Node n,TermSystem p) throws AnalyzeException,  ConstraintException {
//		System.out.println("parse logical " + n.getNodeName());
		LogicalExpression result = null;
		if (isLogicalRelation(n)){
			result = logicalRelation(n,p);
		}
		else if (isLogicalOperator(n)){
			result = logicalOperator(n,p);
		}
		else if (isLogicalNot(n)) {
			result = logicalNot(n,p);
		}
		else if (isLogicalImplies(n)) {
			result = logicalImplies(n,p);
		}
		else exception(1);
//		System.out.println("parse logical result " + result);

		return result;
	}

	/* <!ELEMENT IDSExprLogicalNot (%ExprLogical;)> */
	static private LogicalExpression logicalNot(Node n,TermSystem p) 
	throws AnalyzeException, ConstraintException {
		ChildIterator child = new ChildIterator(n);
		Node next = child.next();
		LogicalExpression first = parse(next,p);
		return new NotExpression(first);
	}

	// <!ELEMENT IDSExprLogicalOr (%ExprLogical;,(%ExprLogical;)+)>
	//   <!ELEMENT IDSExprLogicalAnd (%ExprLogical;,(%ExprLogical;)+)> 
	static private LogicalExpression logicalOperator(Node n,TermSystem p) 
	throws AnalyzeException, ConstraintException {
		String operator = ((Element) n).getTagName();
		ChildIterator child = new ChildIterator(n);
		Node next = child.next();
		LogicalExpression first = parse(next,p);
		if (!child.hasMoreChild()) exception(1);
		LogicalExpression second = logicalOperatorAux(child,p, operator);
		LogicalExpression result = null;
		if (isOr(operator))result = new OrExpression(first,second);
		else if (isAnd(operator)) result = new AndExpression(first,second);
		return result;
	}

	// méthode récursive pour analyser tous les arguments
	// PRECOND : child a encore un fils
	static private LogicalExpression logicalOperatorAux(ChildIterator child,TermSystem p,  String op)
	throws AnalyzeException, ConstraintException {

		Node next = child.next();
		LogicalExpression result = null;
		LogicalExpression first = parse(next,p);
		result = first;
		if (child.hasMoreChild()) {
			LogicalExpression second = logicalOperatorAux(child,p,op);
			if (isOr(op)) result = new OrExpression(first,second);
			else if (isAnd(op))result = new AndExpression(first,second);
			return result;
		}
		return first;
	}

	//    <!-- couple d'expressions entieres pour les operations de comparaison --> 
	// <!ENTITY % Compare "(%ExprInt;,%ExprInt;)">
	// <!-- operateurs de comparaison -->
	// <!ELEMENT IDSExprEquality (%Compare;)>
	// <!ELEMENT IDSExprSup (%Compare;)>
	// <!ELEMENT IDSExprInf (%Compare;)>
	static private LogicalExpression logicalRelation(Node n,TermSystem p) throws AnalyzeException, 
	ConstraintException {
		String op = ((Element) n).getTagName();
		ChildIterator child = new ChildIterator(n);
		if (!child.hasMoreChild()) exception(2);
		Node next = child.next();
		Expression first = IntExprVisitor.parse(next,p);
		if (!child.hasMoreChild()) exception(2);
		next = child.next();
		Expression second = IntExprVisitor.parse(next,p);
		return relation(p,op,first,second);
	}
	
	/** this method takes a comparison operator with its parameters
	 * It returns the corresponding LogicalExpression
	 */
	static private LogicalExpression relation(TermSystem p,String op,Expression first,Expression second) {	
		LogicalExpression result=null;
		if (isEqual(op)) {
			result = new EqualExpression(first,second);
		}
		else if (isLess(op)) 
			result = new LessExpression(first,second);
		else if (isLessEqual(op)) 
			result = new LessEqualExpression(first,second);
		else if (isGreat(op))
			result = new GreatExpression(first,second);
		else if (isGreatEq(op))
			result = new GreatEqualExpression(first,second);
		return result;
	}
	
	

	static private LogicalExpression logicalImplies(Node n,TermSystem p) throws AnalyzeException, 
	ConstraintException {
		ChildIterator child = new ChildIterator(n);
		if (!child.hasMoreChild()) exception(1);
		Node next = child.next();
		LogicalExpression first = parse(next,p);
		if (!child.hasMoreChild()) exception(3);
		next = child.next();
		LogicalExpression second = parse(next,p);
		return new ImpliesExpression(first,second);
	}


	//----------------------------------------------------------
	// gestion des tag
	static protected boolean isLogicalOperator(Node n) {
		return isTag(n,"ExprLogicalAnd")||isTag(n,"ExprLogicalOr");
	}
	static protected boolean isOr(String n) {
		return n.equals("ExprLogicalOr") ;
	}
	static protected boolean isAnd(String n) {
		return n.equals("ExprLogicalAnd") ;
	}
	static protected boolean isLogicalNot(Node n) {
		return isTag(n,"ExprLogicalNot");
	}

	static protected boolean isLogicalRelation(Node n) {
		return isTag(n,"ExprGreat")
		|| isTag(n,"ExprLess")
		||isTag(n,"ExprEqual")
		|| isTag(n,"ExprLessEq")
		|| isTag(n,"ExprGreatEq");
	}

	static protected boolean isEqual(String n) {
		return n.equals("ExprEqual") ;
	}
	static protected boolean isGreat(String n) {
		return n.equals("ExprGreat") ;
	}
	static protected boolean isGreatEq(String n) {
		return n.equals("ExprGreatEq") ;
	}
	static protected boolean isLess(String n) {
		return n.equals("ExprLess") ;
	}
	static protected boolean isLessEqual(String n) {
		return n.equals("ExprLessEq") ;
	}

	static protected boolean isLogicalImplies(Node n) {
		return isTag(n,"ExprLogicalImplies");
	}

	
	//----------------------------------------------------------
	// g�re les exceptions
	static protected void exception(int n)  throws AnalyzeException{
		String s=" In LogicalExprVisitor ";
		switch (n) {
		case 1: s+="logical operation ";break;
		case 2: s+="integer value  ";break;
		case 3: s+="second part of implies  ";break;
		case 4: s+="integer identifier ";break;
		case 5: s+="logical expression ";break;
		case 6: throw new AnalyzeException("can't enumerate on the condition in JMLForAll or JMLExist");
		case 7: s+="array identifier expected in AllDiff expression";
		}
		throw new AnalyzeException(s + " expected");
	}


}
