package validation;

import exception.AnalyzeException;
import exception.ConstraintException;
import exception.ValidationException;

/**
 * Main class to launch the validation of a XML file 
 * obtained from a HOL term
 * 
 * If tm is the HOL term, then the validation search solutions
 * of "exist tm" which is the existential closure of term tm
 * 
 * @author Hélène Collavizza
 * @date June 2008
 */
public class ValidationLauncher {

	public static String help() {
		String s = "Use :\n";
		s += "ValidationLauncher <path> <file>: validate term in <path/file> using JSolver and integers coded on 8 bits";
		s += "\nValidationLauncher <path> <file> <int_value>: validate term in <file> using JSolver and integers coded on";
		s += "\n<int_value> bits";
		s += "\nValidationLauncher <path> <file> -all: test if term in <path/file> has a solution using JSolver and integers coded on 8 bits";
		s += "\nValidationLauncher <path> <file> -all <int_value>: test if term in <path/file> has a solution using JSolver";
		s += "\nand integers coded on <int_value> bits";
		s += "\nValidationLauncher <path> <file> -solver <solverName>: validate term in <path/file> using <solverName> and integers coded on 8 bits";
		s += "\nValidationLauncher <path> <file> <int_value> -solver <solverName> : validate term in <file> using <solverName> and integers coded on";
		s += "\n<int_value> bits";
		s += "\nValidationLauncher <path> <file> -all -solver <solverName>: test if term in <path/file> has a solution using <solverName> and integers coded on 8 bits";
		s += "\nValidationLauncher <path> <file> -all <int_value> -solver <solverName>: test if term in <file> has a solution using <solverName>";
		s += "\nand integers coded on <int_value> bits";
		
		s+= "\n\nAll options above can be used with -timeout <int_value> \n";
		s+= "as last argument where <int_value> is a time in mili second";
		return s;
	}

	public static void main(String[] ss) {
		try{
			Validation p = null;
			String name; // name of the file to 
			String path; // path of directory xmlterm2csp
			// default values
			boolean isPath=false;
			String solver = "JSolver";
			int format = 8;
			int timeout = -1; // default = no timeout
			
			int l =ss.length;
			if (l<2) 
				System.out.println(help());
			else {
				path = ss[0];
				name = ss[1];
				if (l>=3 && ss[2].equals("-all"))
					isPath=true;
				// if there is option timeout, truncate the length
				if (l>3 && ss[l-2].equals("-timeout")) {
					timeout = new Integer(ss[l-1]).intValue();
					l=l-2;
				}
				switch (l) {
				case 2: //nothing to do, default values
					break;
				case 3:
					if (!isPath)
						format = new Integer(ss[2]).intValue();
					break;
				case 4:
					if (ss[2].equals("-solver"))
						solver = ss[3];
					else 
						format = new Integer(ss[3]).intValue();
					break;
				case 5:
					solver = ss[4];
					if (!isPath)
						format = new Integer(ss[2]).intValue();
					break;
				default: // length 6
					solver = ss[5];
					format = new Integer(ss[3]).intValue();
				break;
				}
//				System.out.println("Options are: file " + name + " path " + path + " solver :" + 
//						solver + " format " + format + " isPath " + isPath + 
//						" timeout " + timeout);
				p = new Validation(name,path,solver,format,isPath,timeout);
			}
			if (p!=null) {
				try{
					p.verify();
				}catch (AnalyzeException a) {
					System.out.println(a);
				}catch (ConstraintException a) {
					System.out.println(a);
				}catch (ValidationException a) {
					System.out.println(a);
				}

			}
		}
		catch (StackOverflowError e) {
			System.out.println(" stack overflow " + e);
			e.printStackTrace();
			System.out.println(e.getMessage());
			System.out.println(e.getCause());
		}
	}
}

