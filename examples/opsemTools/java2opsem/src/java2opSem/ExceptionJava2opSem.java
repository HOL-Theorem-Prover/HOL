package java2opSem;

/**
 * @author Hélène Collavizza
 * from an original student work by Eric Le Duff and Sébastien Derrien
 * Polytech'Nice Sophia Antipolis
 *
 */
public class ExceptionJava2opSem extends Exception {

	private static final long serialVersionUID = 1L;

	public ExceptionJava2opSem(String msg) {
		super(msg);
	}

	public String getError() {
	    return ("Error : " + getMessage() + "\n" + "Export cancelled");
	}
}
