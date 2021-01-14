package edu.stanford.nlp.sempre.interactive.lassie;

import java.io.IOException;
import java.io.PrintWriter;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;

import edu.stanford.nlp.sempre.ContextValue;
import edu.stanford.nlp.sempre.Json;
import edu.stanford.nlp.sempre.NaiveKnowledgeGraph;
import edu.stanford.nlp.sempre.StringValue;
import edu.stanford.nlp.sempre.interactive.Item;
import edu.stanford.nlp.sempre.interactive.World;

import fig.basic.IOUtils;
import fig.basic.LogInfo;
import fig.basic.Option;

import edu.stanford.nlp.sempre.interactive.lassie.Component;

// the world of tactics
public class TacticWorld {

    public static String thm (String t) {
        return t;
    }

    // Wrap a tactic text as a "Tactic":
    public static String tactic (String t) {
        return "TACTIC " + t;
    }

    public static String command (String c) {
        return "COMMAND " + c;
    }

    // String constructions, basically tactic language
    public static String int2string(Integer n) {
        return n.toString();
    }
    public static String app(String fn, String arg) {
        if (fn.equals("") || arg.equals("")) return "";
        return fn + " " + arg;
    }

    public static String then(String tac1, String tac2) {
        if (tac1.equals("") || tac2.equals("")) return "";
        return tac1 + " \\ " + tac2;
    }
    public static String then1(String tac1, String tac2) {
        if (tac1.equals("") || tac2.equals("")) return "";
        return tac1 + " >- " + parens(tac2);
    }
    public static String cons(String hd, String tl) {
        if (hd.equals("") || tl.equals("")) return "";
        return hd + " , " + tl;
    }
    public static String list(String seq) {
        if (seq.equals("")) return "";
        return "[ " + seq + " ]";
    }
    public static String quote(String exp) {
        if (exp.equals("")) return "";
        return "TERMSTART " + exp + " TERMEND";
    }
    public static String parens(String exp) {
        if (exp.equals("")) return "";
        return "( " + exp + " )";
    }
    public static String op(String operator, String arg1, String arg2) {
        if (operator.equals("") || arg1.equals("") || arg2.equals("")) return "";
        return arg1 + " " + operator + " " + arg2;
    }

    public static String goalInt(String num) {
        return "INTGOAL" + " " + num;
    }

    public static String goalTerm(String tm) {
        return "TERMGOAL" + " " + tm;
    }

    public static Set<String> fromFeature(String f) {
        HOLOntology ontology = HOLOntology.getTheOntology();
        if (f.equals("top")) return ontology.entities.keySet();
        else if (f.equals("bot")) return new HashSet<String>();
        else if (ontology.features.containsKey(f)) return ontology.features.get(f);
        else throw new RuntimeException("Feature not recognized: " + f);
    }

    // Set operations
    public static Set<String> intersect(Set<String> s1, Set<String> s2) {
        return s1.stream().filter(i -> s2.contains(i)).collect(Collectors.toSet());
    }

    public static String set2string(Set<String> s) {
        return String.join(",", s);
    }

    // Semantic side helper of ChoiceFn
    // returns
    public static String choice(Set<String> s) {
        if (s.size() > 1) {

            // Abduce simplest answer if its features are a subset of every other candidate's features
            // (i.e. abduce if there is no disambiguation possible)
            HOLOntology ontology = HOLOntology.getTheOntology();
            String smallest = "TOP_TACTIC";
            int smallestSize = Integer.MAX_VALUE;
            for (String e : s)
                if (ontology.entities.get(e).size() < smallestSize) {
                    smallest = e;
                    smallestSize = ontology.entities.get(e).size();
                }
            boolean abduceable = true;
            for (String e : s)
                if (!ontology.entities.get(e).containsAll(ontology.entities
                                                          .get(smallest)
                                                          .stream() // (not required to share name)
                                                          .filter(x -> !x.startsWith("name"))
                                                          .collect(Collectors.toSet())))
                    abduceable = false;

            if (abduceable)
                return smallest;
        }
        // not abduceable, therefore ambiguous
        return String.join(",", s); // send the set of candidates to alert ambiguity
    }
}
