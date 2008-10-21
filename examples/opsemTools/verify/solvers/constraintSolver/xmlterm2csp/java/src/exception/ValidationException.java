package exception;

/** exceptions when showing the validity of the term
 * @author Hélène Collavizza
 * @date June 2008
*/
public class ValidationException extends Exception {
    String message;
    
    public ValidationException(String s) {
	super();
	message = s;
    }

    public String toString() {
	return super.toString() + "DYNAMIC EXECUTION ERROR : " + message;
    }
}
