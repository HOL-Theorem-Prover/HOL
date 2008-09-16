package solvers.gecodej;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import org.gecode.BExpr;
import org.gecode.Expr;

import validation.variables.IntegerVariable;
import expression.Expression;
import expression.ExpressionVisitor;
import expression.integer.BinaryIntegerExpression;
import expression.integer.IntegerLiteral;
import expression.integer.PlusExpression;
import expression.logical.AndExpression;
import expression.logical.BinaryLogicalOperator;
import expression.logical.Comparator;
import expression.logical.EqualExpression;
import expression.logical.NotExpression;
import expression.logical.OrExpression;


/**
 * visitor to create GecodeJ constraints from the
 * internal constraints
 * @author Lydie Blanchet, Hélène Collavizza
 *
 */
public class GecodeJExpressionVisitor implements ExpressionVisitor {

	protected GecodeJIntVarBlock intVar;
	private GecodeJ js; // the abstract JSolver

	public GecodeJExpressionVisitor(GecodeJIntVarBlock i, GecodeJ js) {
		intVar = i;
		this.js = js;
	}
		
	public Object visit(IntegerVariable variable, Object data) {
		return new Expr(intVar.getGecodeJVar(variable.name()));
	}

	public Object visit(IntegerLiteral literal, Object data) {
		int val = literal.intValue();
		return intVar.addConstant(val);
	}
	

	// invoke method "name" and returns a Expr
	// using java reflect
	private Expr invokeExpr(Expr first,String name,Object[] args) {
		Expr exp = null;
		try {
			Class sc = Class.forName("org.gecode.Expr");
			Class intExp = Class.forName("org.gecode.Expr");
			Class[] param = {intExp};
			Method m = sc.getDeclaredMethod(name, param);
			exp = (Expr)m.invoke(first, args);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return exp;
	}
	
	// invoke method "name" and returns a BExpr
	// using java reflect
	private BExpr invokeBExpr(BExpr first,String name,Object[] args) {
		BExpr exp = null;
		try {
			Class sc = Class.forName("org.gecode.BExpr");
			Class intExp = Class.forName("org.gecode.BExpr");
			Class[] param = {intExp};
			Method m = sc.getDeclaredMethod(name, param);
			exp = (BExpr)m.invoke(first, args);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return exp;
	}
	
	
	public Object visit(BinaryIntegerExpression expression, Object data) {
		Expr[] args = new Expr[1];
		Expr first = (Expr)expression.getArg1().structAccept(this, data);
		args[0] = (Expr)expression.getArg2().structAccept(this, data);
		return invokeExpr(first,js.getConcreteSyntax(expression),args);
	}



	
	// to visit a binary operator
	// simplifies "or" and "and" expressions when on argument is empty
	public Object visit(BinaryLogicalOperator exp, Object data) {
		BExpr[] args = new BExpr[1];
		BExpr first = (BExpr)exp.arg1().structAccept(this, data);
		args[0]  = (BExpr)exp.arg2().structAccept(this, data);
		if ((exp instanceof AndExpression) && (first==null ||args[0]==null ))
			return null;
		if ((exp instanceof OrExpression) && first==null) 
			return args[0];
		if ((exp instanceof OrExpression) && args[0]==null) 
			return first;
		return invokeBExpr(first,js.getConcreteSyntax(exp), args);
	}

	// or
	public Object visit(NotExpression expression, Object data) {
		System.err.println("not not yet handled");
		return null;
	}

    // to visit comparison expressions
	public Object visit(Comparator expression, Object data) {
		Expr arg1 = (Expr)expression.arg1().structAccept(this, data);
		Expr arg2 = (Expr)expression.arg2().structAccept(this, data);
		return new BExpr(arg1,js.getConcreteSyntax(expression),arg2);
	}

	public static void main(String[] s) {
		GecodeJ js = new GecodeJ();
		GecodeJIntVarBlock intVar = new GecodeJIntVarBlock(js,8);
		intVar.addVar("a");
		intVar.addVar("b");
		GecodeJExpressionVisitor v = new GecodeJExpressionVisitor(intVar,js);
		IntegerVariable a = new IntegerVariable("a");
		IntegerVariable b = new IntegerVariable("b");
		Expression e1 = new PlusExpression(a,b);
		Expression e2 = new EqualExpression(e1,b);
		System.out.println(e2.structAccept(v, null));
	}
}
