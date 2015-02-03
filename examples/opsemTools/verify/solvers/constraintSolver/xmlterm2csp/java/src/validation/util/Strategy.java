package validation.util;

import java.util.ArrayList;

import org.w3c.dom.Node;

import validation.system.TermSystem;
import validation.visitor.LogicalExprVisitor;
import exception.AnalyzeException;
import exception.ConstraintException;
import expression.Expression;
import expression.logical.AndExpression;
import expression.logical.ImpliesExpression;
import expression.logical.LogicalExpression;
import expression.logical.NotExpression;
import expression.logical.OrExpression;

/** 
 * Class to take the negation of a Boolean expression
 * Does not compute a complete DNF but if the input is of the form
 *      t1 /\ t2 /\ ... /\ tn
 * returns the list of disjuncts [~t1,~t2, ...,~tn]
 * This disjuncts will be treated successively during
 * the verification
 * 
 * @author Hélène Collavizza
 * @date June 2008
 * 
 */
public class Strategy {

    // take a Boolean formula and return the negation of the formula
	// as a list of conjunctions
	// Do not compute a complete DNF
	public static ArrayList<LogicalExpression> negate(TermSystem p,Node next){
		ArrayList<LogicalExpression> result = new ArrayList<LogicalExpression>();
			Node saveNext = next.cloneNode(true);
			LogicalExpression exp;
			try {
				exp = LogicalExprVisitor.parse(saveNext,p);
				addConjunct(exp,result);
			} catch (AnalyzeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (ConstraintException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		return result;
	}
	
	private static void addConjunct(LogicalExpression e,ArrayList<LogicalExpression> result){
		if (e instanceof AndExpression) {
			AndExpression a = (AndExpression)e;
			addConjunct((LogicalExpression)((AndExpression)a).arg1(),
					result);
			addConjunct((LogicalExpression)((AndExpression)e).arg2(),
					result);
		} 
		else result.add(negateCase(e));
	}	
		
	// for the moment, only not and JMLImplies expressions are treated
	private static LogicalExpression negateCase(LogicalExpression e){
		// returns the expression itself
		if (e instanceof NotExpression) {
			return (LogicalExpression)((NotExpression)e).arg1();
		}
		// a=>b is (not a or b) so returns return (a and not b)
		else if (e instanceof ImpliesExpression){
			Expression a1 = ((ImpliesExpression)e).arg1();
			LogicalExpression a2 = (LogicalExpression)((ImpliesExpression)e).arg2();
			return new AndExpression(a1,negateCase(a2));
		}
		// returns the negation
		else return new NotExpression(e);
	}

	// PRECOND: e is in Disjunctive Normal Form
	// @return: the list of all terms in the disjunction
	public static ArrayList<Expression> extractDisjunct(Expression e){
		ArrayList<Expression> result = new ArrayList<Expression>();
		if (!(e instanceof OrExpression))
			result.add(e);
		else 
			addDisjunct(result,e);
		return result;
	}
	
	private static void addDisjunct(ArrayList<Expression> result, Expression e) {
		if (!(e instanceof OrExpression))
			result.add(e);
		else {
			Expression arg1 = ((OrExpression)e).arg1();
			addDisjunct(result,arg1);
			Expression arg2 = ((OrExpression)e).arg2();
			addDisjunct(result,arg2);
		}
	}



}

