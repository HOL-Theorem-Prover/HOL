(*=====================================================================  *)
(* FILE          : quantHeuristicsLib.sml                                *)
(* DESCRIPTION   : some code to find instantations for quantified        *)
(*                 variables                                             *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : December 2008                                         *)
(* ===================================================================== *)


structure quantHeuristicsArgsLib :> quantHeuristicsArgsLib =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule ConseqConv quantHeuristicsLib
     rich_listTheory quantHeuristicsTheory

(*
quietdec := false;
*)


(* quantHeuristicsLib contains the core functionality to eliminate
   quantifiers. However the heuristics contained in this lib are just
   concerned with equations and basic boolean expressions. This
   file contains heuristics for common construcs like lists, pairs,
   option-types, etc.
*)







(*******************************************************************
 * Pairs
 *******************************************************************)


(* val v = ``x:('a # 'b)``;
   val fv = [``y:'a``]:term list;
   val t = ``FST (x:('a # 'b)) = y``
   fun P v (t:term) = SOME (enumerate_pair v)
 *)

fun enumerate_pair v =
let
   val (vn,vt) = dest_var v
   val tL = pairSyntax.strip_prod vt;

   val ntL = enumerate 1 tL
   val vars = map (fn (n,ty) => mk_var (vn^(Int.toString n), ty)) ntL
in
   vars
end;


(* if left or right side is FST, SND of v, then do a case split on v and
   let the details be sorted during the next iteration *)
fun QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR_GEN P (sys:quant_heuristic) fv v t =
let
   (*check whether something should be done*)
   val _ = pairSyntax.dest_prod (type_of v) handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val vars = case (P v t) of NONE => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
                            | some => valOf some;

   (*do it*)
   val (_, vars) = term_variant fv vars T;
   val precond_thm0 = pairTools.PAIR_EX v (pairSyntax.list_mk_pair vars)

   val neg_precond_thm = CONV_RULE (NEG_NEG_INTRO_CONV THENC
                         RAND_CONV (NOT_EXISTS_LIST_CONV)) precond_thm0

   val precond = rand (concl neg_precond_thm);
   val thm0 = UNDISCH neg_precond_thm

   val thm1 = GEN v (DISCH precond (CCONTR t thm0))
   val thm2 = GEN v (DISCH precond (CCONTR (mk_neg t) thm0))

   val i = pairSyntax.list_mk_pair vars
   val g1 = guess_others_satisfied (i,vars, SOME (fn () => thm1));
   val g2 = guess_others_not_possible (i,vars, SOME (fn () => thm2));
in
   guess_list2collection ([], [g1,g2])
end



fun split_pair___FST_SND___pred v t =
let
   val t1 = pairSyntax.mk_fst v;
   val t2 = pairSyntax.mk_snd v;

   val do_split = not (null (find_terms (fn t' => (t' = t1) orelse (t' = t2)) t))
in
   if do_split then SOME (enumerate_pair v) else NONE
end;


(* val v = ``x:('a # 'b # 'c)``;
   val t = ``(\ (a,b,c). P a b c) ^v``
 *)
local
   fun is_var_pabs v t =
   let
      val (b,v') = dest_comb t;
   in
      (v = v') andalso (pairSyntax.is_pabs b)
   end handle HOL_ERR _ => false;
in

fun split_pair___PABS___pred v t =
let
   val p = hd (find_terms (is_var_pabs v) t);
   val vars = pairSyntax.strip_pair (fst (pairSyntax.dest_pabs (fst (dest_comb p))))
in
   SOME vars
end handle Empty => NONE
         | HOL_ERR _ => NONE;
end;



val QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR =
    QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR_GEN
     (fn v => fn t => case split_pair___PABS___pred v t of
                    NONE => split_pair___FST_SND___pred v t
                  | some => some)




(* val v = ``x:('a # 'b # 'c)``
   val fv = []:term list;
   val t = ``(\ (a1, a2, a3). P a1 a2 a3) (x:('a # 'b # 'c))``
 *)


val pair_qhca =
  {distinct_thms = [],
   cases_thms =    [],
   rewrite_thms =  [PAIR_EQ_EXPAND, pairTheory.FST, pairTheory.SND],
   convs =         [],
   heuristics =    [QUANT_INSTANTIATE_HEURISTIC___SPLIT_PAIR],
   final_rewrite_thms = [pairTheory.FST,  pairTheory.SND,
                         PAIR_EQ_SIMPLE_EXPAND]
  }:quant_heuristic_combine_argument


(*
val PAIR_QUANT_INSTANTIATE_CONV = SEXT_PURE_QUANT_INSTANTIATE_CONV
   [pairs_combine_argument]

val t = ``!p. (x = FST p) ==> Q p``
val thm = PAIR_QUANT_INSTANTIATE_CONV t;

val t = ``!p. ?t. ((f t = FST p) /\ Z x) ==> Q p``
val thm = PAIR_QUANT_INSTANTIATE_CONV t


val t = ``?p. ((SND p) = 7) /\ Q p``
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``?v. (v,X) = Z``
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``?v. (v,X) = (a,9)``
val thm = PAIR_QUANT_INSTANTIATE_CONV t

val t = ``!x. a /\ (\ (a1, t3, a2). P a1 a2 t3) x /\ b x``
val thm = PAIR_QUANT_INSTANTIATE_CONV t

*)


val stateful_qhca = quantHeuristicsLib.stateful_qhca;
val pure_stateful_qhca = quantHeuristicsLib.pure_stateful_qhca;
val TypeBase_qhca = quantHeuristicsLib.TypeBase_qhca;


(*******************************************************************
 * Option types
 *******************************************************************)

val option_qhca =
  {distinct_thms      = [optionTheory.NOT_NONE_SOME],
   cases_thms         = [optionTheory.option_nchotomy],
   rewrite_thms       = [optionTheory.SOME_11, optionTheory.IS_NONE_EQ_NONE,
                         optionTheory.IS_NONE_EQ_NONE,
                         IS_SOME_EQ_NOT_NONE],
   convs              = [],
   heuristics         = [],
   final_rewrite_thms = [optionTheory.option_CLAUSES]
  }:quant_heuristic_combine_argument



(*******************************************************************
 * Nums
 *******************************************************************)

val num_qhca =
  {distinct_thms = [prim_recTheory.SUC_ID, numTheory.NOT_SUC],
   cases_thms =    [arithmeticTheory.num_CASES],
   rewrite_thms =  [prim_recTheory.INV_SUC_EQ,
      arithmeticTheory.EQ_ADD_RCANCEL,arithmeticTheory.EQ_ADD_LCANCEL,
      arithmeticTheory.ADD_CLAUSES],
   convs =         [],
   heuristics =    [],
   final_rewrite_thms = []
  }:quant_heuristic_combine_argument



(*******************************************************************
 * Lists
 *******************************************************************)

val list_qhca =
  {distinct_thms = [rich_listTheory.NOT_CONS_NIL],
   cases_thms =    [listTheory.list_CASES],
   rewrite_thms =  [listTheory.CONS_11,
                    listTheory.NULL_EQ,
                    listTheory.APPEND_11,
                    listTheory.APPEND_eq_NIL],
   convs =         [],
   heuristics =    [],
   final_rewrite_thms = [listTheory.NULL_DEF,
                         rich_listTheory.NOT_CONS_NIL,
                         GSYM rich_listTheory.NOT_CONS_NIL]
  }:quant_heuristic_combine_argument


(*******************************************************************
 * Combinations
 *******************************************************************)

val std_qhca = combine_qhcas [
   num_qhca, option_qhca, pair_qhca, list_qhca]

end
