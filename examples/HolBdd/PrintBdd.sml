
(*****************************************************************************)
(* PrintBdd.sml                                                              *)
(* ------------                                                              *)
(*                                                                           *)
(* Some BDD utilities for printing using dot                                 *)
(*  http://www.research.att.com/sw/tools/graphviz/                           *)
(*                                                                           *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*   Tue Oct  9 08:53:21 BST 2001 -- created file                            *)
(*   Thu Nov  1 21:04:27 GMT 2001 -- updated for judgement assumptions       *)
(*   Thu Mar 28 09:40:05 GMT 2002 -- added signature file                    *)
(*                                                                           *)
(*****************************************************************************)

structure PrintBdd :> PrintBdd = struct

(*
load "muddyLib";
load "PrimitiveBddRules";

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
*)

local

open bdd;
open Varmap;
open PrimitiveBddRules;

open Globals HolKernel Parse boolLib bdd;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

in

(*****************************************************************************)
(* Print a BDD to <file>.dot and convert it to <file>.ps; return the bdd     *)
(*****************************************************************************)

fun dotBdd file label bdd = 
 let val glab  = ("label=\""^label^"\"");
     val gsize = "size=\"7.5,8\""
 in
 (bdd.fnprintdot (file^".dot") bdd;
  Process.system("dot -G"^glab^" -G"^gsize^" -Tps "^file^".dot -o "^file^".ps");
  bdd)
 end;

(*****************************************************************************)
(* Print a term_bdd using a supplied label into <file>.dot;                  *)
(* make a sed script to replace node numbers with variable names;            *)
(* execute the sed script to create edited_<file>.dot;                       *)
(* run:                                                                      *)
(*  dot -Glabel="label" -Gsize="7.5,10" -Tps edited_<file>.dot -o <file>.ps  *)
(* delete dot, sed edits and and edited dot files                            *)
(* return the bdd and the variable name-to-number mapping                    *)
(*****************************************************************************)

     
(*****************************************************************************)
(* Create a sed script for editing a dot file so that BBD nodes              *)
(* are labelled with variable names rather than numbers                      *)
(*****************************************************************************)

local

fun varmap_to_sed_script file varmap_pairs =
 let val out = BasicIO.open_out file
 in
 (List.map 
  (fn (s,n) => 
    BasicIO.output
     (out,
      "s/\\\""^(makestring n)^"\\\"/\\\""^s^"\\\"/g\n"
     ))
  varmap_pairs;
 BasicIO.close_out out)
 end

in

fun dotLabelledTermBdd file label tb = 
 let val (_,ass,vm,tm,bdd) = dest_term_bdd tb;
     val pairs           = Binarymap.listItems vm;
     val glab            = ("label=\""^label^"\"");
     val gsize           = "size=\"7.5,8\""
     val _               = if not(HOLset.isEmpty ass)
                            then print "printing a term_bdd with assumptions"
                            else ()
 in
 (bdd.fnprintdot (file^".dot") bdd;
  varmap_to_sed_script(file^"_sed_edits")pairs;
  Process.system("sed -f "^file^"_sed_edits "^file^".dot > edited_"^file^".dot");
  Process.system("dot -G"^glab^" -G"^gsize^" -Tps edited_"^file^".dot -o "^file^".ps");
  Process.system("rm "^file^".dot");
  Process.system("rm "^file^"_sed_edits");
  Process.system("rm edited_"^file^".dot");
  ())
 end

end;

(*****************************************************************************)
(* Print dot-drawn BDD to scratchBdd.ps, with the term as label if           *)
(* !dotTermBddFlag is true and an empty label if it's false.                 *)
(*****************************************************************************)

val dotTermBddFlag = ref true;

(* Old version -- gets printing of "/\" and "\/" wrong
fun dotTermBdd tb = 
 (print "writing scratchBdd.ps\n";
  dotLabelledTermBdd 
   "scratchBdd" 
   (if !dotTermBddFlag then Parse.term_to_string(getTerm tb) else "") 
   tb);
*)

fun dotTermBdd tb = 
 let val _ = add_rule {term_name = "/\\",
                       fixity = Infixr  400,
                       pp_elements = [HardSpace 1, TOK "AND", BreakSpace(1,0)],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundSameName, (PP.INCONSISTENT, 0))}
     val _ = add_rule {term_name = "\\/",
                       fixity = Infixr  300,
                       pp_elements = [HardSpace 1, TOK "OR", BreakSpace(1,0)],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundSameName, (PP.INCONSISTENT, 0))}
     val _ = print "writing scratchBdd.ps\n";
     val _ = dotLabelledTermBdd 
              "scratchBdd" 
              (if !dotTermBddFlag then Parse.term_to_string(getTerm tb) else "") 
              tb
     val _ = remove_termtok {term_name = "/\\", tok = "AND"}
     val _ = prefer_form_with_tok {term_name = "/\\", tok = "/\\"}
     val _ = remove_termtok {term_name = "\\/", tok = "OR"}
     val _ = prefer_form_with_tok {term_name = "\\/", tok = "\\/"}
 in
 ()
 end;

end
end
