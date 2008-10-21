package java2opSem;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Map;
import java2opSem.ExceptionJava2opSem;

import org.jmlspecs.checker.*;
import org.multijava.mjc.CModifier;
import org.multijava.mjc.Constants;
import org.multijava.mjc.JavadocLexer;
import org.multijava.mjc.Main;
import org.multijava.mjc.ParsingController;

import antlr.RecognitionException;
import antlr.TokenStreamException;


/** main class to build a HOL term from a JML specification
 * 
 * @version August 2008
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis
 */
public class Jml2opSem {

	JmlCompilationUnit rootJml;
	File file;
	
	// contains the string that represent the 
	// jml specifications of all methods in the file
	public Map<String,String> jmlSpec;

	private ParsingController parsingController;
	private TokenStreamSelector lexingController;
	private JmlLexer jmlLexer;
	private JavadocLexer docLexer;
	private JmlMLLexer jmlMLLexer;
	private JmlSLLexer jmlSLLexer;
	public JmlParser parser;

	public Jml2opSem(File file) throws ExceptionJava2opSem {
		super();
		this.file = file;
		Main compiler = new Main( new CModifier( Constants.ACCESS_FLAG_ARRAY,Constants.ACCESS_FLAG_NAMES ) );
		Reader r = null;
		try {
			r = new FileReader(file);
		} catch (FileNotFoundException e) {
			throw new ExceptionJava2opSem("Cannot read " + file + ".");
		}
		parsingController = new ParsingController( r, null );
		lexingController = new TokenStreamSelector();
		boolean allowUniverses = true; 
		jmlLexer = new JmlLexer( parsingController, lexingController, 
				true, true, allowUniverses, compiler );
		docLexer = new JavadocLexer( parsingController );
		jmlMLLexer = new JmlMLLexer( parsingController, lexingController, 
				true, true, allowUniverses, compiler );
		jmlSLLexer = new JmlSLLexer( parsingController, lexingController, 
				true, true, allowUniverses, compiler );
		try {
			lexingController.addInputStream( jmlLexer, "jmlTop" );
			lexingController.addInputStream( jmlMLLexer, "jmlML" );
			lexingController.addInputStream( jmlSLLexer, "jmlSL" );
			lexingController.addInputStream( docLexer, "javadoc" );
			lexingController.select( "jmlTop" );
			parsingController.addInputStream( lexingController, "jml" );
			parsingController.addInputStream( docLexer, "javadoc" );
			parsingController.selectInitial( "jml" );

			final boolean ACCEPT_MULTIJAVA = true;
			final boolean ACCEPT_RELAXEDMULTIJAVA = false;
			parser = 
				new JmlParser(compiler, 
						parsingController.initialOutputStream(),
						parsingController,
						false,
						ACCEPT_MULTIJAVA, 
						ACCEPT_RELAXEDMULTIJAVA,
						allowUniverses );
			rootJml  = (JmlCompilationUnit) parser.jCompilationUnit();
//TODO: 	parser.jAssertStatement(); //  fait avancer à la fin du fichier
		} catch (Exception e) {
			String message = "It was impossible to build the AST for file " + file + "\n";
			message+="Possible errors in the program: \n";
			message+="   - only integers and arrays of integers are allowed\n";
			message+="   - in \"if statements\", then and else blocks must be enclosed with {}\n";
			message+="   - \"for loops\" are not allowed (use \"while loops\" instead)\n";
			message+="   - JavaDoc comments are not allowed\n";
			message+="   - i++ or i-- are not permitted\n";
			message+="Possible error in JML specification: \n";
			message+="   - requires clause must precede ensures clause\n";
			message+="   - clauses must terminate with \";\"\n";
			message+="   see http://www.cs.ucf.edu/~leavens/JML/ for JML syntax";
			throw new ExceptionJava2opSem(message);
		}
	}
	
	
	// ########### Function to start parsing
	public void parse(ArrayList<String> param) throws ExceptionJava2opSem {
		Jml2opSemVisitor v = new Jml2opSemVisitor(param);
		rootJml.accept(v);
		if (v.hasError()) 
			throw new ExceptionJava2opSem("\nJML specification contains statements that are not yet implemented.");
		else
			jmlSpec = v.getJml();
	}

	// ########### Functions for accessing specifications #####

	// return the JML specification of method s
	public String getJml(String s) {
		return jmlSpec.get(s);
	}
	
	// return the requires clause of specification of method s
	public String getRequires(String s) {
		String spec = jmlSpec.get(s);
		int endRequires = spec.indexOf("EndRequires");
		if (endRequires!=-1)
			return spec.substring(0,endRequires);
		return "T";
	}
	
	// return the requires clause of specification of method s
	public String getEnsures(String s) {
		String spec = jmlSpec.get(s);
		int endRequires = spec.indexOf("EndRequires");
		if (endRequires!=-1)
			return spec.substring(endRequires + 11);
		if (spec.isEmpty()) 
			return "T";
		return spec;
	}


}


