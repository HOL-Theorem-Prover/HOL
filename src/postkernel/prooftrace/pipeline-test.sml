open Lib Feedback

val seq =  [
   "bool", "marker", "num", "sat", "combin",
   "relation", "prim_rec", "quotient", "pair",
   "arithmetic", "numeral", "cv", "numpair",
   "ind_type", "one", "sum", "option", "While",
   "reduce", "divides", "normalForms", "pred_set"];

fun mk_inp s = s ^ "Theory.tr.gz";
fun mk_raw s = s ^ ".raw.pft.bin";
val () = List.app (fn s => PFTEmit.emit_theory{trace=mk_inp s, output=mk_raw s, binary=true, ruleset=PFTEmit.HOL4}) seq;
val () = print "Wrote raw.pft.bin files\n"
(* for debugging 
fun mk_out s = s ^ ".pft.jsonl";
val () = List.app (fn s => PFTEmit.emit_theory{trace=mk_inp s, output=mk_out s, binary=false, ruleset=PFTEmit.HOL4}) seq;
val () = print "Wrote pft.jsonl files\n"
*)

(*
fun mk_bin s = s ^ ".pft.bin";
(* TODO: should rename before merging *)
val () = List.app (fn s => PFTRename.rename {input=mk_raw s, output=mk_bin s}) seq;
val () = print "Wrote renamed pft.bin files\n"
*)

val () = PFTMerge.merge {
  inputs = List.map mk_raw seq,
  targets = [PFTMerge.ThyAll ("arithmetic",false),
             PFTMerge.ThyAll ("pred_set",false)],
  output = "merged.pft.bin",
  binary = true
};
val () = print "Wrote merged.pft.bin\n"

val db = PFTReplay.replay PFTReplay.empty_trDB "merged.pft.bin"
handle (e as (HOL_ERR m)) => (print("Uncaught HOL_ERR: "^(message_of m)); raise e)
val () = print ("Replay produced "^(Int.toString(PFTReplay.size db))^" theorems\n")

open Type Term

fun print_ty ty =
  if is_vartype ty then dest_vartype ty
  else case total dom_rng ty of SOME (d,r) =>
    String.concat[print_ty d, "-->", print_ty r]
  | _ => let
    val (opn, args) = dest_type ty
    val args = List.map print_ty args
  in if List.null args then opn
     else String.concat["(", String.concatWith "," args, ") ", opn]
  end

fun print_tm tm =
  if is_var tm then let
    val (x,ty) = dest_var tm
  in String.concat[x,":",print_ty ty] end
  else if is_const tm then let
    val (x,ty) = dest_const tm
  in x end
  else if is_abs tm then let
    val (x,b) = dest_abs tm
  in String.concat["(\\", print_tm x, ". ", print_tm b, ")"] end
  else let val (f,x) = dest_comb tm in
    String.concat["(", print_tm f, " ", print_tm x, ")"]
  end

val SOME th = PFTReplay.lookup db "arithmetic$ADD_COMM";
val [] = Thm.hyp th
val ([],_) = Tag.dest_tag (Thm.tag th)
val () = print ("Found ADD_COMM with no hyps or oracles\nConclusion:\n")
val () = print(print_tm(Thm.concl th)) 
val () = print("\n")

val SOME th = PFTReplay.lookup db "pred_set$INTER_COMM";
val [] = Thm.hyp th
val ([],_) = Tag.dest_tag (Thm.tag th)
val () = print ("Found INTER_COMM with no hyps or oracles\nConclusion:\n")
val () = print(print_tm(Thm.concl th)) 
val () = print("\n")
