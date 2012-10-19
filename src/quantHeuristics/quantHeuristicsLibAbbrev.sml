(*=====================================================================  *)
(* FILE          : quantHeuristicsLibAbbrev.sml                          *)
(* DESCRIPTION   : Abbreviate subterms                                   *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : Oct 2012                                              *)
(* ===================================================================== *)


structure quantHeuristicsLibAbbrev =
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

open HolKernel Parse boolLib Drule
     quantHeuristicsLibBase

(*
val t = ``P y /\ !x. (Q (SND (g x)) /\ P (f (FST (g x))))``
*)

type selection_fun = term -> (term * string) option

fun INTRO_QUANT_ABBREVIATIONS_CONV_base elim_conv elim_abbrev_abort (select_funs:selection_fun list) t =
let
   val select_terms = let
      val all_subterms = (find_terms (K true) t);
      val rel_subterms = filter (fn t => not (is_var t) andalso not (is_const t)) all_subterms
      fun sf_subterms sf = mapfilter (valOf o sf) rel_subterms
      val sfs = map sf_subterms select_funs
   in flatten sfs end
   val fvL = all_vars t;
(*
   val (st, ss) = hd select_terms
*)

   fun try_select (st, ss) =
   let
      val _ = if (is_var st) then fail() else ();
      val new_v = variant fvL (mk_var (ss, type_of st))
      val s = [st |-> new_v]


      fun v_inst_filter v t i fvL = not (i = st)
      fun v_filter v t = v = new_v
      val v_qps = [inst_filter_qp [v_inst_filter], filter_qp [v_filter]]

(*
      val (_, t0) = dest_abs (rand (rand t))
val t0 = t
val t0 = qasm_t
*)
      fun try_subst t0 =
      let
         val t' = subst s t0
      in
         if (t0 = t') then (SUB_CONV try_subst t0) else
         let
           val abbrev_t = mk_forall (new_v, mk_imp(mk_eq (st, new_v), t'));
           val elim_thm = QCHANGED_CONV (elim_conv v_qps) abbrev_t handle HOL_ERR _ => REFL abbrev_t
           val _ = if (aconv t0 (rhs (concl elim_thm))) then fail() else ()
           val _ = if (elim_abbrev_abort andalso
                       (aconv abbrev_t (rhs (concl elim_thm)))) then fail() else ()

           val abbrev_thm = prove (mk_eq (t0, abbrev_t), Unwind.UNWIND_FORALL_TAC THEN REWRITE_TAC [])
         in
           TRANS abbrev_thm elim_thm
         end
      end
   in
     try_subst t
   end;
in
  tryfind try_select select_terms
end;



fun SIMPLE_QUANT_ABBREV_CONV select_funs = REPEATC (INTRO_QUANT_ABBREVIATIONS_CONV_base (K NO_CONV) false select_funs)

fun SIMPLE_QUANT_ABBREV_TAC (select_funs:selection_fun list) =
  ConseqConv.DISCH_ASM_CONV_TAC (SIMPLE_QUANT_ABBREV_CONV select_funs)

fun elim_conv qpL qps = QCHANGED_CONV (FAST_QUANT_INSTANTIATE_CONV (qps@qpL))

fun QUANT_ABBREV_CONV select_funs qpL = REPEATC (INTRO_QUANT_ABBREVIATIONS_CONV_base
 (elim_conv qpL) false select_funs)

fun QUANT_ABBREV_TAC (select_funs:selection_fun list) qpL =
  ConseqConv.DISCH_ASM_CONV_TAC (QUANT_ABBREV_CONV select_funs qpL)


(* Some select functions *)

fun select_fun_constant c (name:string) = (fn t =>
  let
    val (c', a) = dest_comb t;
    val _ = if same_const c c' then () else fail();
  in
    SOME (a, name)
  end handle HOL_ERR _ => NONE): selection_fun

val FST_select_fun = select_fun_constant ``FST`` "p"
val SND_select_fun = select_fun_constant ``SND`` "p"
val IS_SOME_select_fun = select_fun_constant ``IS_SOME`` "x"
val THE_select_fun = select_fun_constant ``THE`` "p"


(* Testing it

open quantHeuristicsLibAbbrev
open quantHeuristicsLib

val t = ``P (FST (g x)) /\ (P (FST (g x))) /\ P (FST (f x)) /\ !y. Q p /\ P (SND (g y))``

SIMPLE_QUANT_ABBREV_CONV [FST_select_fun]  t
SIMPLE_QUANT_ABBREV_CONV [SND_select_fun]  t

QUANT_ABBREV_CONV [FST_select_fun] [std_qp] t
QUANT_ABBREV_CONV [SND_select_fun] [std_qp] t
QUANT_ABBREV_CONV [FST_select_fun, SND_select_fun] [std_qp] t


set_goal ([], t)
e (QUANT_ABBREV_TAC [FST_select_fun, SND_select_fun] [std_qp])


val t2 = ``Q x ==> (IS_SOME (g x)) ==> (IS_SOME (f x)) ==> P (THE (g x), THE (f x))``

REPEAT STRIP_TAC
QUANT_ABBREV_TAC [THE_select_fun] [std_qp]
SIMPLE_QUANT_ABBREV_TAC [THE_select_fun]

*)

end
