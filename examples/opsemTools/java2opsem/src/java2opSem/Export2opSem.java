package java2opSem;


import java2opSem.Convert2opSem;
import java2opSem.ExceptionJava2opSem;

/** main class to export a Java file and its JML specification
 * into a ml file
 * Java files are in directory javaFiles/ and result files
 * are in directory opsemFiles/
 * 
 * main takes the name of the program to be exported as argument 
 *     java Export2opSem javaFiles/Foo.java
 * will export file javaFiles/Foo.java into file opsemFiles/Foo.ml
 * 
 * @version August 2008
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis
 */
public class Export2opSem {

	public static void main(String[] args) {
		try {
			if (args.length==0)
				System.err.println("Give a file name to convert");
			else {
				System.out.println("Starting conversion of file " + args[0]);
				Convert2opSem c = new Convert2opSem(args[0]);
				c.convert();
			}
		} catch (ExceptionJava2opSem e) {
			System.err.println(e.getMessage());
		}

	}

}
