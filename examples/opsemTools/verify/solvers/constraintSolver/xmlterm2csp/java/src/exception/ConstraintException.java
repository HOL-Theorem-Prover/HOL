package exception;

/** exceptions during constraint building
 * @author Hélène Collavizza
 * @date June 2008
 * */

public class ConstraintException extends Exception {
    String message;
    
    public ConstraintException(String s) {
	super();
	message = s;
    }

    public String toString() {
	return super.toString() + "  CONSTRAINT BUILDING ERROR : " + message;
    }
}
