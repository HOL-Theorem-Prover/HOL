package exception;

/** exceptions during XML parsing
 * @author Hélène Collavizza
 * @date June 2008
 * */

public class AnalyzeException extends Exception {
    String message;
    
    public AnalyzeException(String s) {
	super();
	message = s;
    }

    public String toString() {
	return super.toString() + "XML PARSING ERROR : " + message;
    }
}
