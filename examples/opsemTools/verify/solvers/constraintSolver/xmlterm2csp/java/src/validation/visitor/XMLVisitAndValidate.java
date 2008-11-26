package validation.visitor;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.SAXException;

//import solvers.gecodej.GecodeJTermSystem;
import solvers.jsolver.JSolverTermSystem;
import validation.solution.Solution;
import validation.system.TermSystem;
import validation.util.ChildIterator;
import validation.util.Strategy;
import exception.AnalyzeException;
import exception.ConstraintException;
import exception.ValidationException;
import expression.Expression;
import expression.logical.LogicalExpression;

/** main class to enable parsing and 
 * searching for a solution
* @author Hélène Collavizza
 * @date June 2008
*/

public class XMLVisitAndValidate extends XMLVisitor {

	String fileName;
	
	// the system for validation 
	private TermSystem constSyst ;
	
	// DOM structure of XML file
	private Document document; 

	// default constructor
	public XMLVisitAndValidate(String n, String pa,int f, int solver) {
		initConstSyst(n,pa,f,solver);
		fileName=pa + "/xml/" + n + ".xml";
		// open xml file
		File in  = new File(fileName);
		initDocument(in);
	}
	
	/** set the constraint system solver according solver name */
	/** default is JSolver */
	private void initConstSyst(String n,String pa,int format,int solver) {
//		switch (solver) {
//		case 5: 
//			constSyst=new GecodeJTermSystem(n,pa,format);
//		break;
//		default:
//			constSyst=new JSolverTermSystem(n,pa,format);
//		}
		constSyst=new JSolverTermSystem(n,pa,format);
	}

	// gets DOM structure from XML file
	private void initDocument(File in) {
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		factory.setValidating(false);   
		factory.setNamespaceAware(false);
		try {
			DocumentBuilder builder = factory.newDocumentBuilder();
			document = builder.parse(in);
		} catch (SAXException sxe) {
			// Error generated during parsing
			System.err.println("exception SAX");
			Exception  x = sxe;
			if (sxe.getException() != null)
				x = sxe.getException();
			x.printStackTrace();
		} catch (ParserConfigurationException pce) {
			// Parser with specified options can't be built
			System.err.println("exception config");
			pce.printStackTrace();
		} catch (IOException ioe) {
			// I/O error
			System.out.println("Can't read xml input file");
			ioe.printStackTrace();
		}
	}

	/** parse "document" and returns the corresponding LogicalExpression
	 * @throws AnalyzeException
	 * @throws ConstraintException
	 */
	private LogicalExpression parse() 
	throws AnalyzeException,ConstraintException,ValidationException {
		// starting node of validation
		ChildIterator child = new ChildIterator(document);
		Node next = child.next();
		
		if (!isTerm(next)) exception(1);
		child= new ChildIterator(next);
		next = child.next();
	
		return LogicalExprVisitor.parse(next, constSyst);
	}

	/**validate "document"
	 * add constraints in ConstSyst and solve it
	 * successively validate all the cases of the DNF
	 * @throws AnalyzeException
	 * @throws ConstraintException
	 */
	public void validate(int timeout) 
	throws AnalyzeException,ConstraintException,ValidationException {
		// build the LogicalExpression
		LogicalExpression e = parse();
		// get the list of terms in the DNF
		ArrayList<Expression> cases = Strategy.extractDisjunct(e);

		// validate each case
		System.out.println("\n\nSearching solutions for term in " + fileName);
		boolean multi = cases.size()>1;
		if (multi) 
			System.out.println("There are " + cases.size() + " cases to solve");

		// verify all the cases 
		// stop on the first case which has a solution (i.e counter-example)
		int i = 0;
		Solution result = new Solution();
		while (i<cases.size() && result.empty()) {
			result = new Solution();
			Expression c = cases.get(i);
			constSyst.addConstraint(c);
			if (multi) 
				System.out.println("Case # " + (i+1));
			System.out.println(constSyst);
			if (timeout==-1)
				constSyst.solve(result,true);
			else 
				constSyst.solve(result,true,timeout);
			constSyst.resetConstraintBlock();
			i++;
		}
		System.out.println(constSyst.printStatus());
		// if there is no solution, print the status
		// to know the overall time for solving all cases
		if (result.empty())
			constSyst.printStatusToFile();
	}
	
	/** 
	 * idem as validate but stop when a first solution 
	 * has been found
	 * Used to test if a path is possible 
	 * @throws ValidationException 
	 * @throws ConstraintException 
	 * @throws AnalyzeException 
	 *
	 */
	public void validateAll(int timeout) throws AnalyzeException, ConstraintException, ValidationException {
		// build the LogicalExpression
		LogicalExpression e = parse();
		
		// validate all the cases 
		// stop on the first case which has a solution (i.e counter-example)
		ArrayList<Expression> cases = Strategy.extractDisjunct(e);
		System.out.println("\n\nSearching solutions for term in " + fileName);
		boolean multi = cases.size()>1;
		if (multi) 
			System.out.println("There are " + cases.size() + " cases to solve");

		int i=0;
		while (i<cases.size()) {
			Expression c = cases.get(i);
			Solution result = new Solution();
			constSyst.addConstraint(c);
			System.out.println(constSyst);
			if (timeout==-1)
				constSyst.solve(result,false);
			else
				constSyst.solve(result,false,timeout);
			constSyst.resetConstraintBlock();
			i++;
		}
		//TODO: write the solutions of all cases

	}
}
