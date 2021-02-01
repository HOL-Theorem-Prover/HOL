package edu.stanford.nlp.sempre.interactive.lassie;

import com.google.common.base.Joiner;
import com.google.common.base.Strings;
import com.google.common.collect.Lists;

import com.fasterxml.jackson.core.JsonProcessingException;

import edu.stanford.nlp.sempre.*;
import fig.basic.*;
import java.util.*;
import java.io.*;


public class LassieUtils{

    public static void printToSocket(String string) {
        try (PrintWriter writer = new PrintWriter(new FileOutputStream (new File("interactive/sempre-out-socket.sml"), true))) {
            writer.println("val _ = " + string + "\n");
            writer.close();
        } catch (IOException ex) {
            System.err.println("Error writing to file interactive/sempre-out-socket.sml");
        }
    }

    // Rudimentary translation of a json object into an SML record
    public static String json2sml(String string) {
        // dependent on knowing the fields in advance
        String[] fields = {"score", "prob", "formula", //"candidates", "anchored", "formula",
                           "size", "status"}; //"stats", "lines"};
        String orig = string;
        // unquote fields; subsitute `:` for `=`
        for (String field : fields) {
            string = string.replace("\"" + field + "\":", field + "= ");
        }

        //string = string
        //    .replace("\"type\":", "cmd= ") // avoid reserved keywords of SML
        //    .replace("\"NaN\"", "~1.0") // force types of fields
        //    .replaceAll("\"anchored\":true,","")
        //    .replaceAll("\"anchored\":false,","")
        //    .replaceAll("\"candidates\":\\[(.*?)\\]","\\[ $1 \\]")
        //    .replaceAll("\"stats\":\\{(.*?)\\},","")
        //    .replaceAll(",\"lines\":\\[(.*?)\\]","")
        //    .replaceAll("\"value\":\"Tactic (.*?)\"", "value = \"Tactic $1\",result = Tactic ($1)")
        //    .replaceAll("\"value\":\"Command (.*?)\"", "value = \"Command $1\",result = Command ($1)")
        //    .replaceAll("\"value\":\"(.*?)\"", "value = \"$1\",result = Tactic ($1)")
        //    .replaceAll("\\{\\[(.*?)\\]\\}","\\[$1\\]");

            //.replaceAll("\"value\":\"(.*?)\"","value= \"$1\",tactic= $1"); // cast the value as a tactic

        // escape backslashes in strings
        // (we could do more fancy escaping, but quotes are already converted earlier by
        //  sempre and other characters requiring escaping are not expected to appear here)
        String[] substrings = string.split("(?<!\\\\)(?:\\\\\\\\)*\"");
        assert (substrings.length % 2 == 1); // we assume the Json had matching quotes and does not begin nor end with them
        string = substrings[0];
        for (int i = 1; i < substrings.length; i++) {
            if (i % 2 == 1) // every second substring is data of type string
                substrings[i] = substrings[i].replace("\\\\","\\\\\\\\");
            string = string + "\"" + substrings[i];
        }

        return string + "\n\n(* " + orig + " *)";
    }
}
