package validation.visitor;


import org.w3c.dom.Element;
import org.w3c.dom.Node;

import exception.AnalyzeException;



/** parent class to manage parsing of XML nodes
* and to manage exceptions
* parsing methods are static to be more efficient
*  @author Hélène Collavizza
 * @date June 2008
*/

public class XMLVisitor {


	//------------------------------------------------------------
	// identifier parsing

	// <!ELEMENT ExprIdent EMPTY>
	// <!ATTLIST ExprIdent name CDATA #IMPLIED>
	static protected String parseIdent(Node n) throws AnalyzeException {
		if (!isIntIdent(n)) exception(3);
		return ((Element) n).getAttribute("name");
	}
	

	//------------------------------------------------------------
	// methods to identify nodes
	static protected boolean isElement(Node n) {
		return (n.getNodeType()==Node.ELEMENT_NODE);
	}

	static protected boolean isTag(Node n, String s) {
		return isElement(n)&&(((Element) n).getTagName()).equals(s);
	}
	
	static protected String nodeName(Node n) {
		if (!isElement(n)) return "Not an element";
		else return ((Element) n).getTagName();
	}

	static protected boolean isTerm(Node n) {
		return isTag(n,"Term");
	}
	
	static protected boolean isIntIdent(Node n) {
		return isTag(n,"ExprIdent");
	}

	
	//----------------------------------------------------------
	// methods to handle exceptions
	static protected void exception(int n)  throws AnalyzeException{
		String s=" In XMLVisitor ";
		switch (n) {
		case 1: s="Term ";break;
		}
		throw new AnalyzeException(s + " expected");
	}

}

