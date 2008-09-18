package validation.util;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import exception.AnalyzeException;

/**
 * Class to easily get childs in a XML tree
 * Main advantage is to not pass through comments and line returns 
* @author Hélène Collavizza
 * @date June 2008 
 * 
 * Typical use:
 *   ChildIterator c = new ChildIterator(n);
 *   while (c.hasMoreChild()){
 *      ....
 *      c.next();
 *   }
 */
public class ChildIterator implements Cloneable{
    private int i;
    private NodeList child;
    private int size;

    private ChildIterator(int i, NodeList child, int size) {
    	this.i = i;
    	this.child=child;
    	this.size=size;
    }

    public ChildIterator(Node c) {
    	this(-1,c.getChildNodes(),c.getChildNodes().getLength());
    }
   
    
    // ---------------
    public Object clone() {
    	return new ChildIterator(i,child,size);
    }

    // to step forward the next ELEMENT_NODE
    // comments are printed
    public Node next() throws AnalyzeException {
	i++;
	Node n=null; ;
	while (i<size&& child.item(i).getNodeType()!=Node.ELEMENT_NODE) {
	    n=child.item(i);
	    if (n.getNodeType()==Node.COMMENT_NODE)
		echoComment(n);
	    i++;
	}
	if (i<size) n=child.item(i);
	return n;
    }

    // to get the next data
    public Node nextData() throws AnalyzeException {
	i++;
	Node n= null;
	while (i<size&& child.item(i).getNodeType()!=Node.TEXT_NODE) {
	    i++;
	}
	if (i<size) n=child.item(i);
	return n;
    }

    // to know if there more childs of type ELEMENT_NODE
    public boolean hasMoreChild() {
	int j = i;
	j++;
	while (j<size&& child.item(j).getNodeType()!=Node.ELEMENT_NODE) {
	    j++;
	}
	return j<size;
    }
				   
   // to print comments of XML file
    private void echoComment(Node n) {
	System.out.println("comment line : " +  n.getNodeValue());
    }
    
    public String toString() {
    	int j = i;
    	j++;
    	while (j<size&& child.item(j).getNodeType()!=Node.ELEMENT_NODE) {
    	    j++;
    	}
    	if (j<size) 
    		return child.item(j).getNodeName();
    	return "no more node";
    }

}
