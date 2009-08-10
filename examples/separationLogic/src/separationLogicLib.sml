structure separationLogicLib :> separationLogicLib =
struct

(*
quietdec := true;
loadPath :=
            (concat Globals.HOLDIR "/examples/separationLogic/src") ::
            (concat Globals.HOLDIR "/examples/separationLogic/src/smallfoot") ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "stringTheory", "Parser", "Lexer","Lexing", "Nonstdio",
   "stringLib", "listLib"];
show_assums := true;
*)

open HolKernel Parse boolLib bossLib;

open generalHelpersTheory finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory arithmeticTheory operatorTheory optionTheory latticeTheory separationLogicTheory;

(*
quietdec := false;
*)





fun GSYM_FUN_EQ_CONV t =
let
   val (vars, b_term) = strip_forall t;
   val (l_term,r_term) = dest_eq b_term;
   val (l_f, l_args) = strip_comb l_term;
   fun split_vars [] acc = ([], acc)
     | split_vars (t::ts) acc =
       if mem t vars then
	   split_vars ts (t::acc)
       else
	   (rev (t::ts), acc)
   val (rest_args, elim_args) = split_vars (rev l_args) [];
   val _ = if (elim_args = []) then raise UNCHANGED else ();
   val rest_vars = filter (fn v => not (mem v elim_args)) vars;

   val l_term' = list_mk_comb (l_f, rest_args);
   val r_term' = list_mk_abs (elim_args, r_term);
   val b_term' = mk_eq (l_term', r_term');
   val t' = list_mk_forall (rest_vars, b_term');

   val thm_term = mk_eq (t,t');
   val thm = prove (thm_term, SIMP_TAC std_ss [FUN_EQ_THM] THEN
			      EQ_TAC THEN SIMP_TAC std_ss [])
in
   thm
end




end
