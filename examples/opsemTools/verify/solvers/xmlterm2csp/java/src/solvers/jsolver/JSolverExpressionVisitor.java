package solvers.jsolver;

import ilog.rules.validation.solver.IlcConstraint;
import ilog.rules.validation.solver.IlcIntExpr;
import ilog.rules.validation.solver.IlcSolver;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import validation.variables.IntegerVariable;
import expression.ExpressionVisitor;
import expression.integer.BinaryIntegerExpression;
import expression.integer.IntegerLiteral;
import expression.logical.AndExpression;
import expression.logical.BinaryLogicalOperator;
import expression.logical.Comparator;
import expression.logical.LogicalExpression;
import expression.logical.NotExpression;
import expression.logical.OrExpression;


/**
 * visitor to create JSolver constraints from the
 * internal constraints
 * @author Lydie Blanchet, Hélène Collavizza
 *
 */
public class JSolverExpressionVisitor implements ExpressionVisitor {

	protected JSolverIntVarBlock intVar;
	private IlcSolver s; // the concrete solver
	private JSolver js; // the abstract JSolver

	public JSolverExpressionVisitor(JSolverIntVarBlock i, JSolver js) {
		intVar = i;
		this.js = js;
		s=js.getIlcSolver();
	}
		
	public Object visit(IntegerVariable variable, Object data) {
		return intVar.getJSolverVar(variable.name());
	}

	public Object visit(IntegerLiteral literal, Object data) {
		int val = literal.intValue();
		return intVar.addConstant(val);
	}
	

	// invoke method "name" and returns a IlcIntExpr
	// using java reflect
	private IlcIntExpr invokeIlcIntExpr(String name,Object[] args) {
		IlcIntExpr exp = null;
		try {
			Class sc = Class.forName("ilog.rules.validation.solver.Ilc" +
			"Solver");
			Class intExp = Class.forName("ilog.rules.validation.solver.IlcIntExpr");
			Class[] param = {intExp,intExp};
			Method m = sc.getDeclaredMethod(name, param);
			exp = (IlcIntExpr)m.invoke(s, args);
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
		IlcIntExpr[] args = new IlcIntExpr[2];
		args[0] = (IlcIntExpr)expression.getArg1().structAccept(this, data);
		args[1] = (IlcIntExpr)expression.getArg2().structAccept(this, data);
		return invokeIlcIntExpr(js.getConcreteSyntax(expression),args);
	}


	/** invoke method "name" and returns a IlcConstraint
	* the method is either in class "IlcIntExpr" (b=true)
	* or in class "IlcConstraint" (b=false) 
	* using java reflect */
	protected IlcConstraint invokeIlcConstraint(String name,Object[] args,boolean b) {
		String className = (b) ? "ilog.rules.validation.solver.IlcIntExpr"
				: "ilog.rules.validation.solver.IlcConstraint";
		IlcConstraint exp = null;
		try {
			Class sc = Class.forName("ilog.rules.validation.solver.IlcSolver");
			Class intExp = Class.forName(className);
			Class[] param = {intExp,intExp};
			Method m = sc.getDeclaredMethod(name, param);
			exp = (IlcConstraint)m.invoke(s, args);
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
	
	// to visit a binary operator
	// simplifies "or" and "and" expressions when on argument is empty
	public Object visit(BinaryLogicalOperator exp, Object data) {
		IlcConstraint[] args = new IlcConstraint[2];
		args[0] = (IlcConstraint)exp.arg1().structAccept(this, data);
		args[1] = (IlcConstraint)exp.arg2().structAccept(this, data);
		if ((exp instanceof AndExpression) && (args[0]==null ||args[1]==null ))
			return null;
		if ((exp instanceof OrExpression) && args[0]==null) 
			return args[1];
		if ((exp instanceof OrExpression) && args[1]==null) 
			return args[0];
		return invokeIlcConstraint(js.getConcreteSyntax(exp), args,false);
	}

	// not
	public Object visit(NotExpression expression, Object data) {
		return s.not((IlcConstraint)((LogicalExpression)expression.arg1()).structAccept(this, data));
	}

    // to visit comparison expressions
	public Object visit(Comparator expression, Object data) {
		IlcIntExpr[] args = new IlcIntExpr[2];
		args[0] = (IlcIntExpr)expression.arg1().structAccept(this, data);
		args[1] = (IlcIntExpr)expression.arg2().structAccept(this, data);
		return invokeIlcConstraint(js.getConcreteSyntax(expression), args,true);
	}

}
