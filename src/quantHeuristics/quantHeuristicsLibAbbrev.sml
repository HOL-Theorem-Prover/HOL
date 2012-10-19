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
     quantHeuristicsLibBase quantHeuristicsLibParameters

(*
val t = ``P y /\ !x. (Q (SND (g x)) /\ P (f (FST (g x))))``


fun FST_select_fun t =
  let
    val t' = pairSyntax.dest_fst t
  in
    SOME (t', "p")
  end handle HOL_ERR _ => NONE

fun THE_select_fun t =
  let
    val t' = optionSyntax.dest_the t
  in
    SOME (t', "x")
  end handle HOL_ERR _ => NONE

fun SND_select_fun t =
  let
    val t' = pairSyntax.dest_snd t
  in
    SOME (t', "p")
  end handle HOL_ERR _ => NONE


val select_funs = [FST_split_fun, SND_split_fun]

fun elim_conv qps = NO_CONV
val elim_abbrev_abort = false


fun elim_conv qps = QCHANGED_CONV (FAST_QUANT_INSTANTIATE_CONV (qps@[std_qp]))
val elim_abbrev_abort = true

*)

fun INTRO_QUANT_ABBREVIATIONS_CONV_base elim_conv elim_abbrev_abort select_funs t =
let
   val select_terms = let
      val all_subterms = (find_terms (K true) t);
      fun sf_subterms sf = mapfilter (valOf o sf)  all_subterms
      val sfs = map sf_subterms select_funs
   in flatten sfs end
   val fvL = free_vars t;
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


fun INTRO_QUANT_ABBREVIATIONS_CONV select_funs = REPEATC (INTRO_QUANT_ABBREVIATIONS_CONV_base (K NO_CONV) false select_funs)

fun QUANT_ABBREVIATIONS_CONV select_funs qpL = REPEATC (INTRO_QUANT_ABBREVIATIONS_CONV_base
(fn qps => QCHANGED_CONV (FAST_QUANT_INSTANTIATE_CONV (qps@qpL))) false select_funs)

(* Testing it

val t = ``P (FST (g x)) /\ (P (FST (g x))) /\ P (FST (f x)) /\ !y. Q p /\ P (SND (g y))``

INTRO_QUANT_ABBREVIATIONS_CONV [FST_select_fun]  t
INTRO_QUANT_ABBREVIATIONS_CONV [SND_select_fun]  t

QUANT_ABBREVIATIONS_CONV [FST_select_fun] [std_qp] t
QUANT_ABBREVIATIONS_CONV [SND_select_fun] [std_qp] t
QUANT_ABBREVIATIONS_CONV [FST_select_fun, SND_select_fun] [std_qp] t

val t2 = ``IS_SOME (g x) ==> P (THE (g x))``

INTRO_QUANT_ABBREVIATIONS_CONV [THE_select_fun]  t2
QUANT_ABBREVIATIONS_CONV [THE_select_fun] [std_qp] t2

*)

end
