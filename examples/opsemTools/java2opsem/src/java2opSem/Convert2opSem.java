package java2opSem;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import java2opSem.ExceptionJava2opSem;
import java2opSem.Java2opSemVisitor;


import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;

/** main class to convert a Java file with a JML specification
 *  as a RSPEC (pre,prog,post)
 *  precond and postcond are requires and ensures statements of 
 *  the JML specification in HOL syntax,
 *  and prog is the program written in opSem syntax
 * 
 * @version August 2008
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis
 */
public class Convert2opSem extends ASTVisitor {

	CompilationUnit root;// the AST
	String filename;
	File fileToConvert;
	
	public Convert2opSem(String fileName) throws ExceptionJava2opSem {
		super();
		this.filename = fileName;
		fileToConvert = new File(fileName);
		char[] source = new char[100000];
		FileReader r;
		try {
			r = new FileReader(fileToConvert);
			r.read(source);
		} catch (FileNotFoundException e) {
			throw new ExceptionJava2opSem("No such file : " + fileToConvert);
		} catch (IOException e) {
			throw new ExceptionJava2opSem("Cannot read file : " + fileToConvert);
		}
		ASTParser parser = ASTParser.newParser(AST.JLS3);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setSource(source);
		parser.setResolveBindings(true);
		root = (CompilationUnit) parser.createAST(null);
	}
	
	
	public void convert() throws ExceptionJava2opSem{
		Java2opSemVisitor j = new Java2opSemVisitor(filename);
		root.accept(j);
		j.close();
	}
}
