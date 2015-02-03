package validation.visitor;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

import validation.system.TermSystem;
import validation.util.ChildIterator;
import exception.AnalyzeException;
import exception.ConstraintException;
import expression.Expression;
import expression.integer.DivExpression;
import expression.integer.IntegerLiteral;
import expression.integer.MinusExpression;
import expression.integer.PlusExpression;
import expression.integer.TimeExpression;


/** 
 * Class to parse XML integer expressions and create IntegerExpression
 * @author Hélène Collavizza
 * @date June 2008
 */

public class IntExprVisitor extends XMLVisitor {

	// <!ENTITY % ExprInt "(IDSExprIdent|IDSExprPlus|IDSExprMinus|IDSExprTimes|IDSExprDecimalIntegerLiteral
	// |IDSExprParenthesis|IDSExprJMLResult)">
	 static protected Expression parse(Node n,TermSystem p) throws AnalyzeException,  ConstraintException {
		Expression result = null;
//		System.out.println(n.getNodeName());
		if (isIntIdent(n)) {
			String name = parseIdent(n);
			if (!p.containsIntVar(name))	
				result = p.addIntVar(name);
			else
				result = p.getIntVar(name);    
		}
		else if (isIntOperator(n)){
			result = intOperator(n,p);
		}
		else if (isIntegerLiteral(n)){
			result= intLiteral(n);
		}	
		else exception(1);
		return result;
	}

	// <!ELEMENT IDSExprPlus (%ExprInt;,(%ExprInt;)+)>
	// <!ELEMENT IDSExprMinus (%ExprInt;,(%ExprInt;)+)>
	// <!ELEMENT IDSExprTimes (%ExprInt;,(%ExprInt;)+)>
	static private Expression intOperator(Node n,TermSystem p) 
	throws AnalyzeException, ConstraintException {
		String operator = ((Element) n).getTagName();
		ChildIterator child = new ChildIterator(n);
		Node next = child.next();
		Expression first = parse(next,p);
		if (!child.hasMoreChild()) exception(1);
		Expression second = intOperatorAux(child,p, operator);
		Expression expr = null;
		if (isPlus(operator)) expr = new PlusExpression(first,second);
		else if (isMinus(operator)) expr = new MinusExpression(first,second);
		else if (isTimes(operator)) expr = new TimeExpression(first,second);
		else expr = new DivExpression(first,second);
//		ExpressionName result = p.exprTable.addExpression(expr);
//		return result;
		return expr;
	}

	// m�thode r�cursive pour analyser tous les arguments
	static private Expression intOperatorAux(ChildIterator child,TermSystem p, String op)
	throws AnalyzeException, ConstraintException {

		Node next = child.next();
		Expression first = parse(next,p);
		if (child.hasMoreChild()) {
			Expression second = intOperatorAux(child,p,op);
			Expression expr = null;
			if (isPlus(op)) expr = new PlusExpression(first,second);
			else if (isMinus(op))expr = new MinusExpression(first,second);
			else if (isTimes(op)) expr = new TimeExpression(first,second);
			else expr = new DivExpression(first,second);
			return expr;
			//return p.exprTable.addExpression(expr);
		}
		return first;
	}

	// <!ELEMENT IDSExprDecimalIntegerLiteral EMPTY>
	// <!ATTLIST IDSExprDecimalIntegerLiteral value CDATA #IMPLIED>
	static private Expression intLiteral(Node n) {
		String val = ((Element) n).getAttribute("value");
		return new IntegerLiteral(val);
	}

	//----------------------------------------------------------
	// gestion des tag
	static protected boolean isIntegerLiteral(Node n) {
		return  isTag(n,"ExprIntegerLiteral");
	}

	static protected boolean isIntOperator(Node n) {
		return isTag(n,"ExprPlus") || isTag(n,"ExprMinus")
		|| isTag(n,"ExprTimes")|| isTag(n,"ExprDiv");
	}
	static protected boolean isPlus(String n) {
		return n.equals("ExprPlus") ;
	}
	static protected boolean isMinus(String n) {
		return n.equals("ExprMinus") ;
	}

	static protected boolean isTimes(String n) {
		return n.equals("ExprTimes") ;
	}
	static protected boolean isDiv(String n) {
		return n.equals("ExprDiv") ;
	}
	
	//----------------------------------------------------------
	// exceptions
	static protected void exception(int n)  throws AnalyzeException{
		String s=" In IntEprVisistor ";
		switch (n) {
		case 1: s+="integer operation ";break;
		case 2: s+="in array access, integer expression ";break;
		}
		throw new AnalyzeException(s + " expected");
	}


}
