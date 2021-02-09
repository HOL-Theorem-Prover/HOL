package edu.stanford.nlp.sempre.interactive.lassie;

import edu.stanford.nlp.sempre.*;
import edu.stanford.nlp.sempre.interactive.lassie.LassieUtils;
import edu.stanford.nlp.sempre.interactive.lassie.HOLOntology;

import fig.basic.LispTree;
import fig.basic.LogInfo;
import fig.basic.Option;

import java.util.List;
import java.util.LinkedList;
import java.util.Arrays;

/**
 * Given a set, returns an element of that set. Kills derivations which
 * execute to empty sets. Sets which execute to something bigger than a
 * singleton trigger a warning, written to the socket file, which
 * locates and describes the ambiguity. In the case that SEMPRE returns
 * no derivations, Lassie can use this information to describe the cause
 * of missing derivations. The grammar rule using this SemanticFn might
 * look like
 *
 * (rule $MyType ($MyTypeCandidates) (ChoiceFn))
 *
 * where $MyTypeCandidates is a call formula returning a
 * StringValue. $MyType will be a StringValue as well.
 */

public class ChoiceFn extends SemanticFn {
    public static class Options {
	@Option(gloss = "Verbose") public int verbose = 0;
    }    
    public static Options opts = new Options();

    Formula formula;
    String[] elements;
    
    public ChoiceFn() { }

    public ChoiceFn(Formula formula) {
	this.formula = formula;
    }
    	
    // Get the string in the uttrance which is at the origin of this derivation
    public static String getUttString(Callable c) {
	if (c.getChildren().size() == 0) return ((ValueFormula) ((Derivation) c).formula).value.pureString();
	else {
	    String uttString = getUttString(c.child(0));
	    for (int i = 1; i < c.getChildren().size(); i++)
		uttString = uttString + " " + getUttString(c.child(i));
	    return uttString;
	}
    }
	
    public DerivationStream call(final Example ex, final Callable c) {
	Executor executor = new JavaExecutor();
	// c.child(0).printDerivationRecursively();
	if (this.formula == null)
	    this.formula = c.child(0).formula;
	String candidates = executor.execute(this.formula, ex.context).value.pureString();
	elements = candidates.split(","); // representation of set is as a string (comma-separated)
	if (elements.length > 1) {
	    LassieUtils.printToSocket("Lassie.AMBIGUITY_WARNING := SOME {set= "
				      + "[\"" + candidates.replace(",","\",\"") + "\"], "
				      + "span= \"" + getUttString((CallInfo) c) + "\"}");
	    elements = new String[0];
	}
	return new MultipleDerivationStream() {
	    private boolean chosen = false;
	    @Override
	    public Derivation createDerivation() {
		if (elements.length == 0 || elements[0].equals("") || chosen) return null;
		else {
		    Derivation res = new Derivation.Builder()
			.withCallable(c)
			.formula(formula)
			.createDerivation();
		    chosen = true;
		    return res;
		}
	    }
	};
    }   
}
