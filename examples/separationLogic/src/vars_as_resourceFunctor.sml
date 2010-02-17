functor vars_as_resourceFunctor (var_res_param :
sig
    include Abbrev;

    val combinator_thmL              : thm list
    val combinator_terms             : term * term * term;
    val resource_proccall_free_thmL  : thm list
    val inital_prop_rewrite_thmL     : thm list
    val abstrL                       : separationLogicLib.fasl_program_abstraction list
    val comments_step_convL          : (conv->conv) list
    val quantifier_heuristicsL       : quantHeuristicsLib.quant_param list
    val var_res_prop_implies___GENERATE :
       (thm list -> term * term * term * term -> thm list) list

    val hoare_triple_case_splitL     : (term -> term) list
    val frame_split_case_splitL      : (term -> term) list

    val INFERENCES_LIST___simulate_command          : (string * (bool -> (bool * simpLib.ssfrag) -> thm list -> ConseqConv.directed_conseq_conv)) list
    val INFERENCES_LIST___simulate_minor_command    : (string * (bool -> (bool * simpLib.ssfrag) -> thm list -> ConseqConv.directed_conseq_conv)) list
    val INFERENCES_LIST___expensive_simplifications : (string * (bool -> (bool * simpLib.ssfrag) -> thm list -> ConseqConv.directed_conseq_conv)) list
    val INFERENCES_LIST___entailment_steps          : (string * (bool -> (bool * simpLib.ssfrag) -> thm list -> ConseqConv.directed_conseq_conv)) list

    val VAR_RES_IS_PURE_PROPOSITION___provers : (term -> term -> thm) list

    structure var_res_base : sig
       include Abbrev;

       val var_res_prove              : Abbrev.term -> Abbrev.thm
       val var_res_prove___no_expn    : Abbrev.term -> Abbrev.thm
       val var_res_assumptions_prove  : Abbrev.thm -> Abbrev.thm
       val var_res_precondition_prove : Abbrev.thm -> Abbrev.thm
       val var_res_precondition_assumption_prove :
                                        Abbrev.term option -> Abbrev.thm -> Abbrev.thm
       val raise_var_res_prove_expn   : exn -> 'a

       val COND_REWR_CONV             : Abbrev.thm -> Abbrev.conv
       val COND_REWRITE_CONV          : bool -> Abbrev.thm list -> Abbrev.conv
       val GUARDED_COND_REWRITE_CONV  : bool -> (Abbrev.term -> bool) -> Abbrev.thm list -> Abbrev.conv

       val VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV : conv -> conv
       val VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV : conv -> conv
       val VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV : (term -> bool) -> conv

       val var_res_prop___VAR_EQ_PROPAGATE : conv
       val VAR_RES_COND_INFERENCE___CONST_INTRO___CONV : term -> string option -> term -> (bool * term * thm)
       val VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV : (term * string option) list -> term -> thm
       val VAR_RES_FRAME_SPLIT_INFERENCE___CONST_INTRO___CONV : term -> string option -> term -> thm
       val VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV : (term * string option) list -> term -> thm

       val var_res_prop_equal_unequal___NORMALISE_CONV : conv
       val VAR_RES_PROP_REWRITE_CONV : (bool * simpLib.ssfrag) -> thm list -> term -> thm
       val get_const_name_for_exp    : string -> term -> string

       val VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV : int list -> conv
       val var_res_prop___COND_RESORT_CONV : int list -> conv

       val cond_rewrite___varlist_update : thm list -> conv
       val GENERATE___var_res_exp_varlist_update___REWRITES : term -> term -> term -> (term * thm list)
       val var_res_prop___var_res_prop_varlist_update___EVAL : term -> conv;
       val VAR_RES_COND_INFERENCE___PRECOND_var_res_prop_varlist_update___EVAL : term -> conv

       val BAG_NORMALISE_CONV : conv;
       val VAR_RES_FRAME_SPLIT___imp_CONV               : conv -> conv
       val VAR_RES_FRAME_SPLIT___split_CONV             : conv -> conv
       val VAR_RES_FRAME_SPLIT___context_CONV           : conv -> conv
       val VAR_RES_FRAME_SPLIT___context_split_imp_CONV : conv -> conv
       val VAR_RES_FRAME_SPLIT___PROP_CONV              : conv -> conv

       type var_res_inference = bool -> (bool * simpLib.ssfrag) -> thm list -> ConseqConv.directed_conseq_conv
       val no_context_conseq_conv                    : ConseqConv.directed_conseq_conv -> var_res_inference;
       val no_context_strengthen_conseq_conv         : conv -> var_res_inference;
       val context_strengthen_conseq_conv            : (thm list -> conv) -> var_res_inference;
       val simpset_strengthen_conseq_conv            : ((bool * simpLib.ssfrag) -> thm list -> conv) -> var_res_inference;
       val simpset_no_context_strengthen_conseq_conv : ((bool * simpLib.ssfrag) -> conv) -> var_res_inference;
    end
end) :
sig
   type user_rewrite_param = (Abbrev.thm list * Abbrev.conv list * simpLib.ssfrag list);
   type gen_step_param = {use_asms       : bool,
                          do_case_splits : bool,
                          do_expands     : bool,
                          generate_vcs   : bool,
                          fast           : bool,
                          stop_evals     : (Abbrev.term -> bool) list,
                          do_prop_simps  : bool};

   datatype gen_step_tac_opt =
       case_splits_flag of bool
     | expands_flag of bool
     | fast_flag of bool
     | prop_simp_flag of bool
     | use_asms_flag of bool
     | generate_vcs_flag of bool
     | add_rewrites of Abbrev.thm list
     | add_convs of Abbrev.conv list
     | add_ssfrags of simpLib.ssfrag list
     | stop_evals of (Abbrev.term -> bool) list
     | combined_gen_step_tac_opt of gen_step_tac_opt list

   val no_case_splits        : gen_step_tac_opt;
   val do_case_splits        : gen_step_tac_opt;
   val no_expands            : gen_step_tac_opt;
   val do_expands            : gen_step_tac_opt;
   val no_case_split_expands : gen_step_tac_opt;
   val generate_vcs          : gen_step_tac_opt;
   val dont_generate_vcs     : gen_step_tac_opt;
   val no_asms               : gen_step_tac_opt;
   val use_asms              : gen_step_tac_opt;
   val no_prop_simps         : gen_step_tac_opt;
   val conservative          : gen_step_tac_opt; (* not fast *)
   val careful               : gen_step_tac_opt; (* no asms. no case splits, no expands *)
   val stop_at_cond          : gen_step_tac_opt;
   val stop_at_while         : gen_step_tac_opt;
   val stop_at_abstraction   : gen_step_tac_opt;
   val stop_at_frame_calc    : gen_step_tac_opt;
   val stop_at_hoare_triple  : gen_step_tac_opt;
   val stop_at_block_spec    : gen_step_tac_opt;

   val gen_step_param___update_use_asms   : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_cs         : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_vcs        : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_expands    : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_fast       : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_prop_simps : gen_step_param -> bool -> gen_step_param
   val gen_step_param___update_stop_evals : gen_step_param -> (Abbrev.term -> bool) list -> gen_step_param

   val VAR_RES_GEN_STEP_CONSEQ_CONV : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.thm list -> Abbrev.conv
   val VAR_RES_GEN_STEP_TAC         : gen_step_param -> user_rewrite_param -> int option -> int -> Abbrev.tactic
   val xVAR_RES_GEN_STEP_CONSEQ_CONV: gen_step_tac_opt list -> int option -> int -> Abbrev.conv
   val xVAR_RES_GEN_STEP_TAC        : gen_step_tac_opt list -> int option -> int -> Abbrev.tactic

   val VAR_RES_PURE_VC_TAC          : Abbrev.tactic;
   val VAR_RES_ELIM_COMMENTS_TAC    : Abbrev.tactic
   val VAR_RES_VC_TAC               : Abbrev.tactic;
   val VAR_RES_SPECIFICATION___CONSEQ_CONV : ConseqConv.conseq_conv
   val VAR_RES_SPECIFICATION_TAC : Abbrev.tactic
end  =
struct

(*
quietdec := true;
loadPath :=
            (Globals.HOLDIR ^ "/examples/separationLogic/src") ::
            (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot") ::
            !loadPath;

show_assums := true;
*)

open HolKernel Parse boolLib bossLib;
open generalHelpersTheory finite_mapTheory pred_setTheory
     listTheory rich_listTheory pairTheory bagTheory
open separationLogicTheory
open separationLogicSyntax
open vars_as_resourceSyntax
open vars_as_resourceTheory
open vars_as_resourceSyntax
open quantHeuristicsLib
open quantHeuristicsArgsLib
open ConseqConv
open bagLib
open separationLogicLib
open Profile


(*
quietdec := false;
*)

(******************************************************************************)
(* Get everything from base                                                   *)
(******************************************************************************)

open var_res_param.var_res_base;


(******************************************************************************)
(* Parameters                                                                 *)
(******************************************************************************)

val verbose_level = ref 0
val verbose_level_try = ref 0
fun do_profile_ref () = ref (Profile.profile_with_exn)



(******************************************************************************)
(* COND_PROP___STRONG_EXIST                                                   *)
(******************************************************************************)

fun COND_PROP___STRONG_EXISTS_NORMALISE_CONV___internally is_rec tt =
let
   val (v1, _) = dest_COND_PROP___STRONG_EXISTS tt handle HOL_ERR _ => raise UNCHANGED;
   val thm0 = RAND_CONV pairTools.PABS_ELIM_CONV tt handle UNCHANGED => REFL tt;
   val body = (snd o pairSyntax.dest_pabs o rand o rhs o concl) thm0
in
   if not (is_COND_PROP___STRONG_EXISTS body) then
      if is_rec then (v1,thm0) else raise UNCHANGED
   else let
      val (v2, thm1) = COND_PROP___STRONG_EXISTS_NORMALISE_CONV___internally true body;
      val thm2 = CONV_RULE ((RHS_CONV o RAND_CONV o ABS_CONV) (K thm1)) thm0;
      val thm3 = CONV_RULE (RHS_CONV (HO_REWR_CONV COND_PROP___STRONG_EXISTS___UNION)) thm2;
   in
      (pairSyntax.mk_pair (v1,v2), thm3)
   end
end;

fun COND_PROP___STRONG_EXISTS_NORMALISE_CONV tt =
let
   val (vc, thm0) = COND_PROP___STRONG_EXISTS_NORMALISE_CONV___internally false tt
   val thm1 = CONV_RULE (RHS_CONV (RAND_CONV (pairTools.PABS_INTRO_CONV vc))) thm0
in
   thm1
end handle HOL_ERR _ => raise UNCHANGED;


fun COND_PROP___STRONG_EXISTS_INTRO___CONV ttt =
let
   val (vp, _) = dest_COND_PROP___STRONG_EXISTS ttt
   val thm = (RAND_CONV (pairTools.PABS_ELIM_CONV)) ttt handle UNCHANGED => REFL ttt
in
   ((SOME vp), thm)
end handle HOL_ERR _ =>
let
   val v = genvar (Type `:unit`)
   val thm_term = mk_icomb (COND_PROP___STRONG_EXISTS_term, mk_abs(v, ttt))
in
   (NONE,
    GSYM ((REWR_CONV COND_PROP___STRONG_EXISTS___ELIM) thm_term))
end;

fun COND_PROP___STRONG_EXISTS_ELIM___CONV NONE ttt =
   REWR_CONV COND_PROP___STRONG_EXISTS___ELIM ttt
| COND_PROP___STRONG_EXISTS_ELIM___CONV (SOME vp) ttt =
   (RAND_CONV (pairTools.PABS_INTRO_CONV vp)) ttt



(****************************************************************)
(* check that no proccalls and resources are used               *)
(****************************************************************)

exception resource_and_proccall_free_PROVE___failed_expn of term * term option;

(*
val exp = (intro_cond_hoare_triple thm; UNCHANGED) handle x => x
val exp =
     (e HOLFOOT_SPECIFICATION_TAC; UNCHANGED) handle x => x;

val resource_and_proc_call_free_PROVE___failed_expn(_, tt, _) = exp
*)

val resource_and_proccall_free_CONV =
   EXT_CONSEQ_REWRITE_CONV
        [K (DEPTH_CONV BETA_CONV)] [EVERY_DEF]
        ([], append (var_res_param.resource_proccall_free_thmL)
         [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ASL_REWRITES,
          fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_REWRITES],
         []) CONSEQ_CONV_STRENGTHEN_direction;


fun resource_and_proccall_free_PROVE tt =
   let
      val thm = resource_and_proccall_free_CONV tt
   in
      (MP thm TRUTH handle HOL_ERR _ =>
      raise resource_and_proccall_free_PROVE___failed_expn (tt, SOME
         ((fst o dest_imp o concl) thm)))
   end handle HOL_ERR _ =>
      raise resource_and_proccall_free_PROVE___failed_expn (tt, NONE);



val proc_call_free_CONV = REWRITE_CONV [
   REWRITE_RULE [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF]
                 fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_bla];


(***************************************************************
 * Eliminate program abstractions and use hoare triples
 ****************************************************************)

fun FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_quant_bla_CONV tt =
let
   val (xenv,penv,prog,abst) = dest_FASL_PROGRAM_IS_ABSTRACTION tt
   val (qP, qQ) = dest_var_res_prog_quant_best_local_action abst

   val thm0 = ISPECL [xenv,penv,qP,prog,qQ] FASL_PROGRAM_IS_ABSTRACTION___var_res_quant_best_local_action
   val thm1 = var_res_precondition_prove thm0

   val (var_const, _) = pairSyntax.dest_pabs qP;

   val thm2 = CONV_RULE (RHS_CONV (PairRules.GEN_PALPHA_CONV var_const)) thm1
   val thm3 = CONV_RULE (RHS_CONV (DEPTH_CONV PairRules.PBETA_CONV)) thm2 handle UNCHANGED => thm2
in
   thm3
end handle HOL_ERR _ => raise UNCHANGED;


val LIST_UNROLL_GIVEN_ELEMENT_NAMES_term = Term `LIST_UNROLL_GIVEN_ELEMENT_NAMES:'a list -> label list -> bool`;
val LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL_NULL = CONJUNCT1 LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL
val LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL_CONS = CONJUNCT2 LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL

local
fun LIST_UNROLL_GIVEN_ELEMENT_NAMES_CONV_int tt =
let
   val (fun_term, argL) = strip_comb tt;
   val _ = if (same_const fun_term LIST_UNROLL_GIVEN_ELEMENT_NAMES_term) andalso
              (length argL = 2) then () else raise UNCHANGED;
   val (x, xL) = (el 1 argL, el 2 argL);
in
   if (not (listSyntax.is_cons xL)) then
      ISPEC x LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL_NULL
   else
   let
       val (h,L) = listSyntax.dest_cons xL
       val thm = ISPECL [x,h,L] LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL_CONS;
       val new_name = fst (dest_var (fst (listSyntax.dest_cons xL)));
       val thm2 = CONV_RULE (RHS_CONV (RENAME_VARS_CONV [new_name])) thm


       val thm3 = CONV_RULE ((RHS_CONV o STRIP_QUANT_CONV o RAND_CONV) (
                   (LIST_UNROLL_GIVEN_ELEMENT_NAMES_CONV_int))) thm2

       val thm4 = CONV_RULE (RHS_CONV (STRIP_QUANT_CONV (
                   REPEATC (STRIP_QUANT_CONV (
                   RIGHT_AND_EXISTS_CONV))))) thm3
   in
       thm4
   end
end;
in
fun LIST_UNROLL_GIVEN_ELEMENT_NAMES_CONV tt =
   CONV_RULE (RHS_CONV (DEPTH_CONV Unwind.UNWIND_EXISTS_CONV))
     (LIST_UNROLL_GIVEN_ELEMENT_NAMES_CONV_int tt)
end;

(*
   val tref = ref [T]
   val _ = tref := []
   val tt = (el (length (!tref)) (!tref))
   val tt = find_term is_var_res_prop_internal ((rhs o concl) thm1)
   val tt = find_term
      (fn t => is_FASL_PROGRAM_IS_ABSTRACTION (snd (strip_forall t)))
       (concl current_theorem)

current_theorem
*)
local
   fun add_vars thm0 vs =
     let
        val xthm0 = CONV_RULE (RHS_CONV (
                      pairTools.ELIM_TUPLED_QUANT_CONV)) thm0
                    handle UNCHANGED => thm0
                         | HOL_ERR _ => thm0;
        val xthm1 = foldr (fn (v, thm) => PairRules.PFORALL_EQ v thm) xthm0 vs
     in
        xthm1
     end;

   val elim_names_wrapper_CONV =
     let
         val conv1 = REWRITE_CONV [pairTheory.FST, pairTheory.SND,
                    var_res_prop_input_ap_def, VAR_RES_HOARE_TRIPLE___comment___ELIM_preserve_names]


         val elim_UNROLL_CONV =
            let
               val xconv1 = STRIP_QUANT_CONV
                             ((RATOR_CONV o RAND_CONV) LIST_UNROLL_GIVEN_ELEMENT_NAMES_CONV) THENC
                              (REPEATC (STRIP_QUANT_CONV LEFT_IMP_EXISTS_CONV))

               val xconv2 = RESORT_FORALL_CONV (fn l => (tl l) @ [hd l])
               val xconv3 = LAST_FORALL_CONV (HO_PART_MATCH lhs
                               UNWIND_FORALL_THM2)
            in
               xconv1 THENC xconv2 THENC xconv3
            end;

         val cs = reduceLib.num_compset()
         val _ = listSimps.list_rws cs

         val conv2 = DEPTH_CONV PairRules.PBETA_CONV
         val conv3 =  computeLib.CBV_CONV cs
     in
         conv1 THENC elim_UNROLL_CONV THENC elim_UNROLL_CONV THENC conv2 THENC conv3
     end;

   fun intro_cond_hoare_triple thm =
     let
        val triple_term = (snd o strip_forall o rhs) (concl thm)
        val xthm1 = PART_MATCH (lhs o rand) VAR_RES_COND_HOARE_TRIPLE_INTRO triple_term;
        val precond = (fst o dest_imp) (concl xthm1)
        val (precond1, precond2) = dest_conj precond;
        val precond1_thm = resource_and_proccall_free_PROVE precond1
        val precond2_thm = var_res_prove precond2
        val precond_thm = CONJ precond1_thm precond2_thm
        val xthm2 = MP xthm1 precond_thm

        val xthm3 = (CONV_RULE
                     ((RHS_CONV o STRIP_QUANT_CONV)
                      (K xthm2))) thm
     in
        xthm3
     end;

in

fun FASL_PROGRAM_IS_ABSTRACTION___forall_comment_var_res_prog_quant_bla_CONV tt =
let
   val (vs,body) = strip_forall tt;
   val _ = if (null vs) then raise UNCHANGED else ();

   (*to VAR_RES_HOARE_TRIPLE*)
   val thm0 = FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_quant_bla_CONV body;

   (*add vars again*)
   val thm1 = add_vars thm0 vs;

   (*elim procedure-call-preserve-names wrapper*)
   val thm2 = CONV_RULE (RHS_CONV elim_names_wrapper_CONV) thm1;

   (*introduce hoare triples *)
   val thm3 = intro_cond_hoare_triple thm2
in
   thm3
end handle HOL_ERR _ => raise UNCHANGED;

end


(******************************************************************************)
(* transform var_res_prop_input ...                                           *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


(*
val tref = ref T;
val ttt = !tref
*)

val all_distinct_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [listTheory.ALL_DISTINCT,
                             listTheory.MEM] all_distinct_cs;
val ALL_DISTINCT_EXPAND_CONV =
   computeLib.CBV_CONV all_distinct_cs



(*
   val var_res_prop_internal___ELIM_CONV___failed_expn ttt = expn
   val ttt = rhs (concl thm1)
*)
local
   val asl_star___PROPS1 = var_res_precondition_prove (
       ISPEC (#1 var_res_param.combinator_terms) asl_star___PROPERTIES___EVAL)
   val asl_star___PROPS2 = var_res_precondition_prove (
       ISPEC (#3 var_res_param.combinator_terms) asl_star___PROPERTIES___EVAL)

   val cond_conv0 = REWRITE_CONV (append var_res_param.inital_prop_rewrite_thmL
      [asl_star___PROPS1, asl_star___PROPS2]);


   val cond_conv1a = (COND_REWRITE_CONV true [var_res_prop_internal___VARS_TO_BAGS])
   val cond_conv1b = (COND_REWR_CONV var_res_prop_internal___VARS_TO_BAGS___END)
   val cond_conv1  = cond_conv1a THENC cond_conv1b


   val cond_conv2a = (COND_REWRITE_CONV true [var_res_prop_internal___PROP_TO_BAG])
   val cond_conv2b = (COND_REWR_CONV var_res_prop_internal___PROP_TO_BAG___END)
   val cond_conv2  = cond_conv2a THENC cond_conv2b
in

exception var_res_prop_internal___ELIM_CONV___failed_expn of term;
fun var_res_prop_internal___ELIM_CONV ttt =
if not (is_var_res_prop_internal ttt) then raise UNCHANGED else
(let
    val thm0 = ALL_DISTINCT_EXPAND_CONV ttt handle UNCHANGED => REFL ttt;

    (*elim exists*)
    val thm1 = RHS_CONV_RULE (
                 Ho_Rewrite.REWRITE_CONV [var_res_prop_internal___EXISTS]) thm0;

    (*find subterm to continue with*)
    val ttt' = find_term is_var_res_prop_internal ((rhs o concl) thm1)

    (*bring props in normal form*)
    val thm1a = cond_conv0 ttt' handle UNCHANGED => REFL ttt';

    (*move vars to bag*)
    val thm2 = RHS_CONV_RULE cond_conv1 thm1a;

    (*move props to bag*)
    val thm3 = RHS_CONV_RULE cond_conv2 thm2;

    (*final step*)
    val thm4 = RHS_CONV_RULE
        (REWR_CONV (GSYM var_res_prop_def)) thm3;

    (*prove assumptions*)
    val thm5 = var_res_assumptions_prove thm4;


    (*combine again*)
    val thm6 = RHS_CONV_RULE (ONCE_REWRITE_CONV [thm5]) thm1

in
    thm6
end handle Interrupt => raise Interrupt
         | _ => raise (var_res_prop_internal___ELIM_CONV___failed_expn ttt));

end


exception var_res_prop_input_distinct___ELIM_CONV___failed_expn of term;
fun var_res_prop_input_distinct___ELIM_CONV a_opt tt =
if not (is_var_res_prop_input_distinct tt) then raise UNCHANGED else
(let
   val thm0 = PART_MATCH (lhs o snd o dest_imp) var_res_prop_input_distinct___REWRITE tt
   val thm1 = var_res_precondition_assumption_prove a_opt thm0
   val thm2 = RHS_CONV_RULE (DEPTH_CONV (var_res_prop_internal___ELIM_CONV)) thm1
in
   thm2
end handle Interrupt => raise Interrupt
         | var_res_prop_internal___ELIM_CONV___failed_expn ttt =>
           raise var_res_prop_internal___ELIM_CONV___failed_expn ttt
         | _ => raise (var_res_prop_input_distinct___ELIM_CONV___failed_expn tt));



(***************************************************************
 * PROGRAM ABSTRACTION
 ****************************************************************)

(*
fun sys xenv penv t = SOME (prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv t)

val t = ``FASL_PROGRAM_IS_ABSTRACTION xenv penv (var_res_prog_local_var (\v. body v 2))``;
val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));

*)
fun FASL_PROGRAM_ABSTRACTION___local_var pf abstL sys xenv penv p =
   let
      val (v, body) = dest_var_res_prog_local_var p

      (*search abstraction*)
      val body_thm_opt = sys xenv penv body;
      val body_thm = if (isSome body_thm_opt) then valOf body_thm_opt else raise UNCHANGED;
      val thm = GEN_ASSUM v body_thm

      val thm0 = ISPECL [xenv, penv] FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var___CONG
      val thm1 = HO_MATCH_MP thm0 thm;
   in
      SOME thm1
   end;


(*
fun sys xenv penv t = SOME (prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv t)

val t = ``FASL_PROGRAM_IS_ABSTRACTION xenv penv (var_res_prog_call_by_value_arg (\v. body v 2) c)``;
val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));

*)
fun FASL_PROGRAM_ABSTRACTION___call_by_value_arg pf abstL sys xenv penv p =
   let
      val (c, v, body) = dest_var_res_prog_call_by_value_arg p

      (*search abstraction*)
      val body_thm_opt = sys xenv penv body;
      val body_thm = if (isSome body_thm_opt) then valOf body_thm_opt else raise UNCHANGED;
      val thm = GEN_ASSUM v body_thm

      val thm0 = ISPECL [xenv,penv,c] FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg___CONG
      val thm1 = HO_MATCH_MP thm0 thm;
   in
      SOME thm1
   end;




(*
fun sys xenv penv t = SOME (prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv t)

val t = ``FASL_PROGRAM_IS_ABSTRACTION
     (HOLFOOT_SEPARATION_COMBINATOR,
      LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP DISJOINT_FMAP_UNION [])) penv
        ((fasl_prog_procedure_call "merge" ([EL 0 arg_refL],constL)):holfoot_program)``
val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));
*)

fun FASL_PROGRAM_ABSTRACTION___eval_expressions pf abstL sys xenv penv p =
   let
      val (abs_body, expL) = dest_var_res_prog_eval_expressions p
      val (v, body) = dest_abs abs_body;

      (*search abstraction*)
      val body_thm_opt = sys xenv penv body;
      val body_thm = if (isSome body_thm_opt) then valOf body_thm_opt else raise UNCHANGED;
      val thm = GEN_ASSUM v body_thm

      val thm0 = ISPECL [xenv,penv,expL] FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions;
      val thm1 = HO_MATCH_MP thm0 thm;
   in
      SOME thm1
   end;



(*
val t = ``FASL_PROGRAM_IS_ABSTRACTION
     (HOLFOOT_SEPARATION_COMBINATOR,
      LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP DISJOINT_FMAP_UNION [])) penv
        ((var_res_prog_procedure_call "merge" ([EL 0 arg_refL],constL)):holfoot_program)``

val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));
val abstL = BODY_CONJUNCTS (ASSUME proc_abst_t)
val sys = FASL_PROGRAM_ABSTRACTION___match abstL ();

val t_opt = ref []
val (abstL, sys, xenv,penv,p) = el 3 (!t_opt)
*)

fun FASL_PROGRAM_ABSTRACTION___var_res_prog_procedure_call pf abstL sys xenv penv p =
   let
      val (name, args) = dest_var_res_prog_procedure_call p handle HOL_ERR _ => raise UNCHANGED;
      val thm0 = ISPECL [xenv,penv,name,args] FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_procedure_call

      (*search abstraction*)
      val precond = (fst o dest_imp o snd o dest_forall) (concl thm0)
      val (v,p1) = (I ## rator) (dest_forall precond);

      val p1_thm = GEN v
                   (tryfind (fn thm => (PART_MATCH rator thm p1)) abstL)
                   handle HOL_ERR _ => raise UNCHANGED;

      val thm1 = HO_MATCH_MP thm0 p1_thm;

      (*intro abstraction comment*)
      val c = term_to_string (pf p)
      val thm2 = CONV_RULE (RAND_CONV (fasl_comment_abstraction_INTRO_CONV c)) thm1

   in
      SOME thm2
   end



(*
val t = ``FASL_PROGRAM_IS_ABSTRACTION
     (HOLFOOT_SEPARATION_COMBINATOR,
      LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP DISJOINT_FMAP_UNION [])) penv
        ((var_res_prog_procedure_call "merge" ([EL 0 arg_refL],constL)):holfoot_program)``

val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));
val abstL = BODY_CONJUNCTS (ASSUME proc_abst_t)
val sys = FASL_PROGRAM_ABSTRACTION___match abstL ();

val t_opt = ref NONE
val SOME (abstL, xenv,penv,p) = !t_opt
val combinatorRWL = [IS_VAR_RES_COMBINATOR___holfoot_separation_combinator,
                     GET_VAR_RES_COMBINATOR___holfoot_separation_combinator,
                    ]

exception my_pointer_exp;
*)

fun FASL_PROGRAM_ABSTRACTION___var_res_prog_parallel_procedure_call pf abstL sys xenv penv p =
   let
      val (name1, args1, name2, args2) = dest_var_res_prog_parallel_procedure_call p handle HOL_ERR _ => raise UNCHANGED;

      val thm0 = ISPECL [xenv,penv,args1,args2,name1,name2]
          FASL_PROGRAM_IS_ABSTRACTION___var_res_prog_parallel_procedure_call

      (*elim combinator precond*)
      val thm1 = var_res_precondition_prove thm0


      (*find abstractions*)
      val precond = (fst o dest_imp o snd o strip_forall) (concl thm1)
      val (v1,p1) = (I ## rator) ((dest_forall o fst o dest_conj) precond);
      val (v2,p2) = (I ## rator) ((dest_forall o snd o dest_conj) precond);

      val p1_thm = GEN v1
                   (tryfind (fn thm => (PART_MATCH rator thm p1)) abstL)
                   handle HOL_ERR _ => raise UNCHANGED;

      val p2_thm = GEN v2
                   (tryfind (fn thm => (PART_MATCH rator thm p2)) abstL)
                   handle HOL_ERR _ => raise UNCHANGED;


      val precond_thm = CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
                                   (CONJ p1_thm p2_thm)

      val thm2 = HO_MATCH_MP thm1 precond_thm;

      val thm3 = REWRITE_RULE [pairTheory.FST, pairTheory.SND] thm2

      (*intro abstraction comment*)
      val c = "("^(term_to_string (pf p))^")";
      val thm4 = CONV_RULE (RAND_CONV (fasl_comment_abstraction_INTRO_CONV c)) thm3
   in
      SOME thm4
   end



(*
val t = ``FASL_PROGRAM_IS_ABSTRACTION
     (HOLFOOT_SEPARATION_COMBINATOR,
      LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP DISJOINT_FMAP_UNION [])) penv
        ((var_res_prog_procedure_call "merge" ([EL 0 arg_refL],constL)):holfoot_program)``

val xenv = el 1 (snd (strip_comb t));
val penv = el 2 (snd (strip_comb t));
val p    = el 3 (snd (strip_comb t));
val abstL = BODY_CONJUNCTS (ASSUME proc_abst_t)
val sys = FASL_PROGRAM_ABSTRACTION___match abstL ();

val t_opt = ref NONE

val _ = t_opt := SOME (abstL, sys, xenv,penv,p);
val SOME (abstL, sys, xenv,penv,p) = !t_opt
val combinatorRWL = [IS_VAR_RES_COMBINATOR___holfoot_separation_combinator,
                     GET_VAR_RES_COMBINATOR___holfoot_separation_combinator]
*)

val critical_section_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [listTheory.MAP, pairTheory.FST,
                             listTheory.ALL_DISTINCT,
                             listTheory.MEM] critical_section_cs;
val _ = computeLib.add_conv (Term `($=):'a -> 'a -> bool`, 2, stringLib.string_EQ_CONV) critical_section_cs;

fun FASL_PROGRAM_ABSTRACTION___var_res_cond_critical_section pf abstL sys xenv penv p =
   let
      val (res, cond, body) = dest_fasl_prog_cond_critical_section p handle HOL_ERR _ => raise UNCHANGED;

      (*destruct the xenv*)
      val (_, lock_env) = pairLib.dest_pair xenv;
      val lock_decls = rand (snd (dest_comb lock_env))

      val (wpL,P) =
           (pairSyntax.dest_pair o snd o pairSyntax.dest_pair) (
           first (fn tt =>
              (fst (pairSyntax.dest_pair tt) = res))
              (fst (listSyntax.dest_list lock_decls)))

      val thm0 = ISPECL [
                    #2 var_res_param.combinator_terms,
                    #1 var_res_param.combinator_terms,
                    lock_decls, penv, res, cond, body, wpL, P]
                 FASL_PROGRAM_IS_ABSTRACTION___fasl_prog_cond_critical_section___lock_decls_env___INTERNAL


      (*elim preconds*)
      val thm1a = var_res_precondition_prove thm0
      val precond = (fst o dest_imp) (concl thm1a)
      val precond_thm = EQT_ELIM (computeLib.CBV_CONV critical_section_cs precond)
      val thm1 = MP thm1a precond_thm

      (*normalise var_res_prop_input*)
      val i_t = (rand o rand o rator o rand o rand o concl) thm1;
      val wpL_t = (fst o dest_pair o rand o rator) i_t;
      val wpL_thm = REWRITE_CONV [LIST_TO_SET_THM] wpL_t;

      val i_thm = ((REWR_CONV var_res_prop_input_def) THENC
                    ((RATOR_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                        (K wpL_thm)) THENC
                    (var_res_prop_input_distinct___ELIM_CONV NONE)) i_t

      (*use it to simplify aquire*)
      val a_t = (rand o rator o rand o rand o concl) thm1;
      val a_thm0 = RAND_CONV (K i_thm) a_t
      val a_thm1 = PART_MATCH (lhs o snd o dest_imp)
                      var_res_prog_aquire_lock___INTRO (rhs (concl a_thm0))
      val a_thm2 = CONV_RULE ((RAND_CONV o LHS_CONV) (K (GSYM a_thm0))) a_thm1

      val set_eq_precond = (fst o dest_imp o concl) a_thm2
      val set_eq_precond_thm = EQT_ELIM (REWRITE_CONV [LIST_TO_SET_THM, SET_OF_BAG_INSERT,
            BAG_OF_EMPTY, SET_EQ_SUBSET, SUBSET_REFL,
            INSERT_SUBSET, IN_INSERT, NOT_IN_EMPTY, EMPTY_SUBSET] set_eq_precond) handle e =>
                 (print "!!!could not prove set_eq_precond!"; raise e)
      val a_thm3 = MP a_thm2 set_eq_precond_thm
      val res_s = stringLib.fromHOLstring res
      val a_c = "aquire-resource "^(term_to_string (pf cond))^" "^res_s
      val a_thm = CONV_RULE (RHS_CONV (fasl_comment_abstraction_INTRO_CONV a_c)) a_thm3
      val thm2 = CONV_RULE ((RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                     (K a_thm)) thm1

      (*use it to simplify release*)
      val r_t = (rand o rator o rand o rand o rand o rand o concl) thm1;
      val r_thm0 = RAND_CONV (K i_thm) r_t
      val r_thm1 = PART_MATCH (lhs o snd o dest_imp)
                      var_res_prog_release_lock___INTRO (rhs (concl r_thm0))
      val r_thm2 = CONV_RULE ((RAND_CONV o LHS_CONV) (K (GSYM r_thm0))) r_thm1
      val r_thm3 = MP r_thm2 set_eq_precond_thm
      val r_c = "release-resource "^res_s
      val r_thm = CONV_RULE (RHS_CONV (fasl_comment_abstraction_INTRO_CONV r_c)) r_thm3

      val thm3 = CONV_RULE ((RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o
                     RATOR_CONV o RAND_CONV) (K r_thm)) thm2


      (*call sys recursively*)
     val (_, _, p1, p2) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm3);

     val sys_thm_opt =  sys xenv penv p2;
     val thm4 = if not (isSome sys_thm_opt) then thm3 else
          let
             val xthm0 = valOf sys_thm_opt
             val (_, _, _, p3) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl xthm0);
             val xthm1 = ISPECL [xenv, penv, p1, p2, p3] FASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE;
          in  MP (MP xthm1 thm3) xthm0 end

   in
      (SOME thm4)
   end




(******************************************************************************)
(* ELIMINATE EXISTENTIAL QUANTIFICATION FROM PRE-AND POST-CONDITIONS          *)
(******************************************************************************)

fun VAR_RES_COND_INFERENCE___EXISTS_PRE___CONSEQ_CONV ttt =
let
   val (_,pre,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE ttt
   val (vc, _) = dest_COND_PROP___STRONG_EXISTS pre

   val thm0 = (PART_MATCH (snd o dest_imp)
       VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_PRE) ttt


   val apply_beta = (QUANT_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
                    PairRules.PBETA_CONV
   val elim_quant = pairTools.SPLIT_QUANT_CONV vc;


   val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV) (
      (apply_beta THENC elim_quant))) thm0
in
   thm1
end handle HOL_ERR _ => raise UNCHANGED;

fun VAR_RES_COND_INFERENCE___EXISTS_POST___CONSEQ_CONV ttt =
let
   val (_,_,_,post) = dest_VAR_RES_COND_HOARE_TRIPLE ttt
   val (vc, _) = dest_COND_PROP___STRONG_EXISTS post

   val thm0 = (PART_MATCH (snd o dest_imp)
       VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_POST) ttt

   val apply_beta = (QUANT_CONV o RAND_CONV)
                    PairRules.PBETA_CONV
   val elim_quant = pairTools.SPLIT_QUANT_CONV vc;

   val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV) (
      (apply_beta THENC elim_quant))) thm0

   val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV) (
      (apply_beta THENC elim_quant))) thm0

in
   thm1
end handle HOL_ERR _ => raise UNCHANGED;



(***************************************************************
 * HANDLE SPECIFICATIONS
 *
 * Eliminate function calls
 ****************************************************************)

(*
val (_,t) = top_goal()
*)


local
   val abstrL = append (var_res_param.abstrL) (append basic_fasl_program_abstractions [
        FASL_PROGRAM_ABSTRACTION___local_var,
        FASL_PROGRAM_ABSTRACTION___call_by_value_arg,
        FASL_PROGRAM_ABSTRACTION___eval_expressions,
        FASL_PROGRAM_ABSTRACTION___var_res_prog_procedure_call,
        FASL_PROGRAM_ABSTRACTION___var_res_prog_parallel_procedure_call,
        FASL_PROGRAM_ABSTRACTION___var_res_cond_critical_section]);


   (*intro hoare triples*)

   fun STRIP_CONJ_CONV c t =
      if is_conj t then
          BINOP_CONV (STRIP_CONJ_CONV c) t
      else c t

   val intro_hoare_triples =
       ANTE_CONV_RULE (
         (QUANT_CONV (STRIP_CONJ_CONV
            FASL_PROGRAM_IS_ABSTRACTION___forall_comment_var_res_prog_quant_bla_CONV)) THENC
         (TRY_CONV FORALL_SIMP_CONV)
       )

   (*bring pre and post conditions in normal form*)
   val intro_var_res_prop =
       ANTE_CONV_RULE
         (ONCE_DEPTH_CONV (QCHANGED_CONV (var_res_prop_input_distinct___ELIM_CONV NONE)))


   fun elim_exists_pre thm =
      let
         val thm1 = ANTE_CONV_RULE (
           ONCE_DEPTH_CONV (QCHANGED_CONV COND_PROP___STRONG_EXISTS_NORMALISE_CONV)) thm handle UNCHANGED => thm
      in
          (STRENGTHEN_CONSEQ_CONV_RULE (
            (DEPTH_CONSEQ_CONV (K VAR_RES_COND_INFERENCE___EXISTS_PRE___CONSEQ_CONV))) thm1)
          handle UNCHANGED => thm1
      end
in

fun VAR_RES_SPECIFICATION___CONSEQ_CONV t = let
   (*execute*)
   val current_theorem = FASL_SPECIFICATION___CONSEQ_CONV (proc_call_free_CONV, abstrL) t;
   val current_theorem2 = intro_hoare_triples current_theorem
   val current_theorem3 = intro_var_res_prop current_theorem2
   val current_theorem4 = elim_exists_pre current_theorem3
in
   current_theorem4
end

end


fun get_exception f x =
(f x;raise UNCHANGED) handle e => e


val VAR_RES_SPECIFICATION_TAC =
  CONSEQ_CONV_TAC (K VAR_RES_SPECIFICATION___CONSEQ_CONV)



(******************************************************************************)
(* HANDLE local vars and arguments                                            *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
local
   val conv1 = HO_PART_MATCH (snd o dest_imp_only)
                  VAR_RES_COND_INFERENCE___prog_local_var
   val conv2 = HO_PART_MATCH (snd o dest_imp_only)
                  VAR_RES_COND_INFERENCE___prog_call_by_value_arg
   val conv = ORELSE_CONSEQ_CONV conv1 conv2

   fun strip_local_vars_args_CONV c p =
     if (is_var_res_prog_call_by_value_arg p) then
        ((RATOR_CONV o RAND_CONV o ABS_CONV)
         (strip_local_vars_args_CONV c)) p else
     if (is_var_res_prog_local_var p) then
        ((RAND_CONV o ABS_CONV)
         (strip_local_vars_args_CONV c)) p else
        c p

in
   fun VAR_RES_COND_INFERENCE___local_vars_args___CONSEQ_CONV tt =
   let
      val (_, _, prog, post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
      val (c, prog', prog_thm_fun) = save_dest_fasl_comment_location prog;
      val _ = if (is_var_res_prog_call_by_value_arg prog' orelse
                  is_var_res_prog_local_var prog') then () else raise UNCHANGED

      val (vp, post_thm) = COND_PROP___STRONG_EXISTS_INTRO___CONV post;
      val prog_thm0 = prog_thm_fun ()
      val prog_thm = CONV_RULE (RHS_CONV (strip_local_vars_args_CONV
           (fasl_comment_location_BLOCK_INTRO_CONV (fasl_comment_modify_INC c)))) prog_thm0

      val thm0 = ((RAND_CONV (K post_thm)) THENC
                 ((RATOR_CONV o RAND_CONV) (K prog_thm))) tt;

      val thm1 = REDEPTH_CONSEQ_CONV (K conv) CONSEQ_CONV_STRENGTHEN_direction
                   (rhs (concl thm0));

      val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1

      val thm3 = ANTE_CONV_RULE ((STRIP_QUANT_CONV o RAND_CONV) (
                    COND_PROP___STRONG_EXISTS_ELIM___CONV vp)) thm2
   in
      thm3
   end
end;


(******************************************************************************)
(* HANDLE comments for blocks                                                 *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___block_comment___CONV tt =
let
   val (_,_,prog,_) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (c, prog') = dest_fasl_comment_location prog;
   val _ = if is_fasl_prog_block prog' then () else raise UNCHANGED

   val conv1 = K (ISPECL [c, prog'] fasl_comment_location_def)
   val conv2 = fasl_comment_location_BLOCK_INTRO_CONV (fasl_comment_modify_COPY_INIT c)
   val conv = conv1 THENC conv2
in
   RATOR_CONV (RAND_CONV conv) tt
end



(******************************************************************************)
(* Flatten blocks                                                             *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
val tt = (snd o dest_conj o fst o dest_imp o concl) ttt
val tref = ref NONE
*)
fun VAR_RES_COND_INFERENCE___block_flatten___CONSEQ_CONV tt =
let
    val (f,P,prog1,Q) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
    val pL_t = dest_fasl_prog_block prog1
    val (pL, _) = listSyntax.strip_cons pL_t
    val _ = if exists is_fasl_prog_block pL then () else raise UNCHANGED

    val (xenv, penv) = let (* a crude, but robust and simple way *)
         val thm0 = ISPECL [f, prog1] VAR_RES_PROGRAM_IS_ABSTRACTION_def
         val t0 = (rator o rator o rhs o snd o strip_forall o concl) thm0
         val penv = rand t0
         val xenv = rand (rator t0)
      in
         (xenv, penv)
      end;
    val abst_opt =
          FASL_PROGRAM_ABSTRACTION___block_flatten___no_rec xenv penv prog1
    val _ = if isSome abst_opt then () else raise UNCHANGED;

    val abst_thm = CONV_RULE (REWR_CONV (GSYM VAR_RES_PROGRAM_IS_ABSTRACTION_def))
                      (valOf abst_opt);

    val prog2 = (rand o concl) abst_thm
    val thm0 = ISPECL [f, P, prog1, prog2, Q] VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_EVAL
    val thm1 = MP thm0 abst_thm
in
   thm1
end;


(******************************************************************************)
(* HANDLE conditional execution                                               *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___cond___CONSEQ_CONV tt =
let
   val (p1,c_opt,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
   val (cond_t, _, _) = dest_fasl_prog_cond p1

   (*apply inference*)
   val c = if isSome c_opt then valOf c_opt else empty_label_list
   val thm0 = if not (isSome c_opt) then REFL tt else
              VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                   (K (ISPECL [c, p1] fasl_comment_location_def)) tt
   val thm1a =
      (HO_PART_MATCH (snd o dest_imp_only) VAR_RES_COND_INFERENCE___prog_cond)
      (rhs (concl thm0));
   val thm1 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1a

   (*comments*)
   val neg_cond_t = mk_icomb (fasl_pred_neg_term, cond_t);
   val cond_s = term_to_string cond_t
   val neg_cond_s = term_to_string neg_cond_t

   val ct = fasl_comment_modify_APPEND_INC ("case "^cond_s) c
   val cf = fasl_comment_modify_APPEND_INC ("case "^neg_cond_s) c

   val ttt = (fst o dest_conj o fst o dest_imp o concl) thm1

   fun list_first_conv conv ttt =
      if listSyntax.is_nil ttt then conv ttt else
      (RATOR_CONV (RAND_CONV conv)) ttt
   fun comment_conv c =
      (TRY_CONV (REWR_CONV VAR_RES_COND_INFERENCE___prog_block3)) THENC
      ((RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
       (list_append_norm_CONV THENC
        list_first_conv (fasl_comment_location_INTRO_CONV c)))

   val thm2 = CONV_RULE (
      (RATOR_CONV o RAND_CONV)
      (RAND_CONV (comment_conv cf) THENC
       (RATOR_CONV (RAND_CONV (comment_conv ct))))) thm1
in
   thm2
end;


(******************************************************************************)
(* HANDLE assume                                                              *)
(******************************************************************************)

val fasl_prog_assume___INFERENCES = [
VAR_RES_COND_INFERENCE___prog_assume_and,
VAR_RES_COND_INFERENCE___prog_assume_or,
VAR_RES_COND_INFERENCE___prog_assume_neg_and,
VAR_RES_COND_INFERENCE___prog_assume_neg_or,
VAR_RES_COND_INFERENCE___prog_assume_neg_neg,
VAR_RES_COND_INFERENCE___prog_assume_neg_pred_bin,
VAR_RES_COND_INFERENCE___prog_assume_pred_bin,
VAR_RES_COND_INFERENCE___prog_assume_true,
VAR_RES_COND_INFERENCE___prog_assume_false,
VAR_RES_COND_INFERENCE___prog_assume_neg_true,
VAR_RES_COND_INFERENCE___prog_assume_neg_false]


val fasl_prog_assume___INFERENCES_CONSEQ_CONVS =
map (fn thm =>
let
   val tt = (snd o dest_imp o snd o strip_forall o concl) thm
in
   if (is_VAR_RES_COND_HOARE_TRIPLE tt) then
      PART_MATCH (snd o dest_imp) thm
   else
      PART_MATCH (snd o dest_imp o snd o dest_imp) thm
end) fasl_prog_assume___INFERENCES

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___assume___internal tt =
let
    val (ap,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
    val _ = if (is_fasl_prog_assume ap) then () else raise UNCHANGED;

    val thm0 = tryfind (fn c => c tt) fasl_prog_assume___INFERENCES_CONSEQ_CONVS
    val thm1 = if (is_imp_only ((snd o dest_imp o concl) thm0)) then
                   var_res_precondition_prove thm0
               else thm0
    val thm2 = STRENGTHEN_CONSEQ_CONV_RULE
                  (K (VAR_RES_COND_INFERENCE___assume___internal))
                  thm1 handle UNCHANGED => thm1
                            | HOL_ERR _ => thm1
in
    thm2
end;


fun VAR_RES_COND_INFERENCE___assume___CONSEQ_CONV tt =
let
   val (ap,_,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
   val _ = if (is_fasl_prog_assume ap) then () else raise UNCHANGED;

   fun conv_pre t = thm0_fun ();
   val conv_post = VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV (
                      DEPTH_CONV BETA_CONV THENC
                      REWRITE_CONV [var_res_prop_binexpression_ELIM])
in
   (EVERY_CONSEQ_CONV [conv_pre,
    VAR_RES_COND_INFERENCE___assume___internal, conv_post]) tt
end;



(******************************************************************************)
(* Propagate equality                                                         *)
(******************************************************************************)

fun var_res_prop___var_eq_const_BAG___INTRO f b =
let
   (*find the equations for rewriting*)
   val (sfs,_) = dest_bag b
   fun get_vcL n nL vcL [] = (rev nL, rev vcL)
     | get_vcL n nL vcL (p::pL) =
       let
          val (_,l,r) = dest_var_res_prop_equal p;
          val v = dest_var_res_exp_var l;
          val c = dest_var_res_exp_const r;
          val _ = if (exists (fn (v', _) => aconv v v') vcL) then
                     Feedback.fail() else ();
       in
          get_vcL (n+1) (n::nL) ((v,c)::vcL) pL
       end handle HOL_ERR _ =>
          get_vcL (n+1) nL vcL pL;

   val (nL, vcL) = get_vcL 0 [] [] sfs
   val _ = if (null nL) then raise UNCHANGED else ();

   val vcL_t = let
                  val vcL_pL = map (pairSyntax.mk_pair) vcL;
               in
                  listSyntax.mk_list (vcL_pL, type_of (hd vcL_pL))
               end;

   (*bring original term in right form*)
   val b_resort_thm = bagLib.BAG_RESORT_CONV nL b;
   val b' = rhs (concl b_resort_thm);

   val b''_rest = (funpow (length nL) rand) b'
   val b''_start = list_mk_icomb(var_res_prop___var_eq_const_BAG_term, [f, vcL_t])
   val b'' = bagSyntax.mk_union (b''_start, b''_rest)

   val b''_eq_t = mk_eq (b', b'');
   val b''_eq_thm = EQT_ELIM (BAG_NORMALISE_CONV b''_eq_t)
   val b_thm = TRANS b_resort_thm b''_eq_thm
in
   (vcL_t, b_thm)
end;


fun var_res_prop___PROPAGATE_EQ___CONV pre =
let
   (*do some simple preprocessing bringing every equation in
     normal form*)
   val pre_thm = var_res_prop___VAR_EQ_PROPAGATE pre handle UNCHANGED =>
                 REFL pre
   val pre' = rhs (concl pre_thm);


   (*find the equations for rewriting*)
   val (f, wpb, rpb, sfb) = dest_var_res_prop pre';
   val (vcL_t, sfb_thm) = var_res_prop___var_eq_const_BAG___INTRO f sfb;
   val pre_thm' = CONV_RULE (RHS_CONV
        (RAND_CONV (K sfb_thm))) pre_thm


   (*instantiate the rewrite thm*)
   val pre'' = rhs (concl pre_thm')
   val imp_thm0 = PART_MATCH (rand o rator) var_res_prop___equal_const pre''
   val imp_thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV)
       (K (GSYM pre_thm'))) imp_thm0

   (*simplify it by removing the BAG_IMAGE and evaluating
     var_res_prop_varlist*)
   val imp_thm2 = CONV_RULE (RAND_CONV ((DEPTH_CONV BAG_IMAGE_CONV) THENC
        BAG_NORMALISE_CONV)) imp_thm1

   val imp_thm3a = var_res_prop___var_res_prop_varlist_update___EVAL vcL_t
        (rand (concl imp_thm2));
   val imp_thm3b = CONJUNCT1 (CONV_RULE (REWR_CONV COND_PROP___STRONG_EQUIV_def) imp_thm3a)
   val thm3 = MATCH_MP (MATCH_MP COND_PROP___STRONG_IMP___TRANS imp_thm2) imp_thm3b
in
   thm3
end;



(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun VAR_RES_COND_INFERENCE___PROPAGATE_EQ___CONSEQ_CONV tt =
let
   val (f, P1, prog, Q) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val thm0 = var_res_prop___PROPAGATE_EQ___CONV P1
   val P2 = rand (concl thm0)

   val thm1 = ISPECL [f, P1, P2, prog, Q] VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP
in
   MP thm1 thm0
end


fun VAR_RES_COND_INFERENCE___CONST_INTRO_PROPAGATE_EQ___CONSEQ_CONV inst_all_vars tt =
let
   val (f, P, prog, Q) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (_, wp, rp, _, sfs) = dest_var_res_prop___propL P;

   fun is_subterm st t =
      (find_term (aconv st) t; true) handle HOL_ERR _ => false
   fun var_is_needed v =
      let
         val sfs' = filter (is_subterm v) sfs;
      in
         if length sfs' > 1 then true else
         if length sfs' = 0 then inst_all_vars else
         let
            val (_, v', c) = dest_var_res_prop_equal (hd sfs');
            val _ = dest_var_res_exp_const c
            val v'' = dest_var_res_exp_var v'
         in
            not (aconv v v'')
         end handle HOL_ERR _ => true
      end

   val varsL = (fst (bagSyntax.dest_bag wp)) @ (fst (bagSyntax.dest_bag rp))
   val needed_vars = filter var_is_needed varsL
   val _ = if null needed_vars then raise UNCHANGED else ();


   val expression_ty =
      mk_var_res_expr_type (fst (dest_var_res_ext_state_type (
         dest_var_res_cond_proposition (type_of P))))

   (*instantiate needed constants*)
   val thm0 = VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV
      (map (fn v => (mk_var_res_exp_var v expression_ty, NONE)) needed_vars) tt;

   val (vL, tt') = (strip_forall o rhs o concl) thm0
   val thm1a = VAR_RES_COND_INFERENCE___PROPAGATE_EQ___CONSEQ_CONV tt';
   val thm1b = LIST_GEN_IMP vL thm1a
   val thm1 =  CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1b
in
   thm1
end;




(*
   val tL = find_terms is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
   val tt = el 1 tL
val thm = VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV tt
*)
fun VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV tt =
let
   val (_, pre, _, _) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (_, wpb, rpb, _) = dest_var_res_prop pre
   val var_list = append (fst (dest_bag wpb)) (fst (dest_bag rpb))

   val expression_ty =
      mk_var_res_expr_type (fst (dest_var_res_ext_state_type (
         dest_var_res_cond_proposition (type_of pre))))

   val exp_list = map (fn v => (mk_var_res_exp_var v expression_ty, NONE)) var_list
in
   (CHANGED_CONV (VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV exp_list) tt) handle HOL_ERR _ => raise UNCHANGED
end;


(* while preparing for the introduction of a "VAR_RES_FRAME_SPLIT" 
   predicate, existential quantifiers are moved to the outer level.
   This may cause trouble, because the choices for these variables have to
   hold under all other (later) case-splits. Therefore, obvious case splits
   are done first, like ones acoording to if-then-else. Moreover, 
   concrete values for variables are introduced as well before the existential
   quantifiers. *)

fun VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV tt =
let
   val (_, pre, _, _) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   fun not_ok t = is_cond t orelse is_var_res_prop_binexpression_cond t
   val is_ok = (find_term not_ok pre; false) handle HOL_ERR _ => true;
   val _ = if (is_ok) then () else Feedback.fail();
in
   VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV tt
end;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___ALL_CONST_INTRO___CONV tt =
let
   val (_, _, wprpb, _, context_sfb,_,_,_) = dest_VAR_RES_FRAME_SPLIT tt;
   val (wpb, rpb) = pairSyntax.dest_pair wprpb
   val var_list = append (fst (dest_bag wpb)) (fst (dest_bag rpb))

   val expression_ty =
      mk_var_res_expr_type (fst (dest_var_res_ext_state_type (
         dest_var_res_proposition (bagSyntax.base_type context_sfb))))

   val exp_list = map (fn v => (mk_var_res_exp_var v expression_ty, NONE)) var_list
in
   (CHANGED_CONV (VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV exp_list) tt) handle HOL_ERR _ => raise UNCHANGED
end;




(******************************************************************************)
(* Final step                                                                 *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___final___CONSEQ_CONV tt =
let
   val (_,_,prog,_) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val bL = dest_fasl_prog_block prog
   val (c, bL, bl_eq_fun) = save_dest_fasl_comment_location bL
   val _ = if (listSyntax.is_nil bL) then () else raise UNCHANGED;


   (*elim comment / intro constants *)
   val thm0 = (((RATOR_CONV o RAND_CONV o RAND_CONV) (K (bl_eq_fun ()))) THENC
               VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV) tt
   val (vs, tt') = strip_forall (rhs (concl thm0))

   (*elim existentials in post-condition*)
   val thm1 = VAR_RES_COND_INFERENCE___EXISTS_POST___CONSEQ_CONV tt'
      handle UNCHANGED => REFL_CONSEQ_CONV tt';

   (*solve*)
   val pre = (fst o dest_imp o concl) thm1
   val (vL, trip) = strip_exists pre;

   val new_comment = fasl_comment_modify_APPEND "final" c;
   val rfc = pairSyntax.mk_pair (F, optionSyntax.mk_some new_comment)

   val pre_thm0 = PART_MATCH (rand o rand)
       (SPEC rfc VAR_RES_COND_HOARE_TRIPLE___SOLVE) trip
   val pre_thm1 = var_res_precondition_prove pre_thm0

   val pre_thm2 = LIST_EXISTS_INTRO_IMP vL pre_thm1
   val thm3 = IMP_TRANS pre_thm2 thm1

   (*combine with thm0*)
   val thm4a = LIST_GEN_IMP vs thm3
   val thm4 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm4a
in
   thm4
end;



(******************************************************************************)
(* HANDLE while loops                                                         *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___while___invariant___CONSEQ_CONV tt =
let
    (* destruct everything *)
    val (p1_0,c_opt,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
    val (inv_t,p1) = dest_fasl_comment_loop_invariant p1_0;
    val (vc, inv_body_t) = pairSyntax.dest_pabs inv_t

    val (co, while_body') = dest_fasl_prog_while p1;
    val while_body = dest_fasl_prog_block while_body'
    val c = if isSome c_opt then valOf c_opt else empty_label_list;

    (*introduce constants*)
    val thm_const = CONV_RULE (RHS_CONV
         VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV) (thm0_fun())
    val (vs, tt') = strip_forall (rhs (concl thm_const))


    (*apply inference*)
    val inv_thm = pairTools.PABS_ELIM_CONV inv_t handle UNCHANGED => REFL inv_t;
    val (v, inv_body_t') = dest_abs (rhs (concl inv_thm))
    val (_, wprp, d, sfb) = dest_var_res_prop_input_ap_distinct inv_body_t'
    val (wp,rp) = pairSyntax.dest_pair wprp;

    val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (
                   (RATOR_CONV (RAND_CONV (K inv_thm)))) tt'

    val pL = (rand o rand o rand o rator o rhs o concl) thm0a
    val (_,_,f,P,Q,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt';

    val thm0b = ISPECL [f, P, wp,rp, d, mk_abs (v, sfb),
           co, while_body, pL, Q] VAR_RES_COND_INFERENCE___prog_while

    val thm0 = CONV_RULE ((RAND_CONV o RAND_CONV) ((DEPTH_CONV BETA_CONV) THENC
                                        (K (GSYM thm0a)))) thm0b

    (*elim precond*)
    val precond = (fst o dest_imp o concl) thm0
    val precond_thm1 = PART_MATCH (fst o dest_imp) var_res_prop___IMPLIES_VAR_DISTINCT
            ((fst o dest_imp) precond)
    val precond_thm2_term = mk_imp ((snd o dest_imp o concl) precond_thm1,
                                    (snd o dest_imp) precond)
    val precond_thm2 = var_res_prove precond_thm2_term;
    val precond_thm = IMP_TRANS precond_thm1 precond_thm2;

    val thm1 = MP thm0 precond_thm;

    (*simplify invariant*)
    val inv_prop = (rand o snd o dest_forall o rand o rator o fst o dest_imp o concl) thm1;
    val inv_prop_thm = ((DEPTH_CONV BETA_CONV) THENC
                        var_res_prop_input_distinct___ELIM_CONV NONE THENC
                        COND_PROP___STRONG_EXISTS_NORMALISE_CONV) inv_prop;

    val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV (REWR_CONV inv_prop_thm))) thm1

    (*reintroduce orginal variable names*)
    val thm3 = CONV_RULE ((RATOR_CONV o RAND_CONV)
                  (((RAND_CONV) (pairTools.SPLIT_QUANT_CONV vc THENC
                                 TRY_CONV LIST_EXISTS_SIMP_CONV)) THENC
                   ((RATOR_CONV o RAND_CONV) (pairTools.SPLIT_QUANT_CONV vc THENC
                                             TRY_CONV LIST_FORALL_SIMP_CONV)))) thm2

    (*introduce comment while-abstraction*)
    val new_c1 = fasl_comment_modify_APPEND ("abstracted while loop") c
    val thm4 = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                  ((fasl_comment_location2_INTRO_CONV new_c1) THENC
                   (fasl_comment_abstraction_INTRO_CONV "while-loop"))) thm3


    (*introduce comment while-body*)
    val new_c2 = fasl_comment_modify_APPEND ("while loop") c
    val thm5 = CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o
                   (fn conv => fn t => if listSyntax.is_nil t then conv t else
                       (RATOR_CONV o RAND_CONV) conv t))
                  (fasl_comment_location_INTRO_CONV new_c2)) thm4

   (*combine with thm_const*)
   val thm6a = LIST_GEN_IMP vs thm5
   val thm6 = CONV_RULE (RAND_CONV (K (GSYM thm_const))) thm6a
in
   thm6
end;



(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___while___loop_spec___CONSEQ_CONV tt =
let
    (* destruct everything *)
    val (p1_0,c_opt,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
    val (PQ',p1) = dest_fasl_comment_loop_spec p1_0;
    val (P',Q') = pairSyntax.dest_pair PQ';

    val (pL',_) = listSyntax.dest_list (dest_fasl_prog_block p1);
    val (p1,pL) = (hd pL', tl pL');

    val (co, while_body') = dest_fasl_prog_while p1;
    val while_body = dest_fasl_prog_block while_body'
    val c = if isSome c_opt then valOf c_opt else empty_label_list;

    (*introduce constants*)
    val thm_const = CONV_RULE (RHS_CONV
         VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV) (thm0_fun())
    val (vs, tt') = strip_forall (rhs (concl thm_const))


    (*apply inference*)
    val (vc, _) = pairSyntax.dest_pabs P';
    val P_thm = pairTools.PABS_ELIM_CONV P' handle UNCHANGED => REFL P';
    val Q_thm = pairTools.PABS_ELIM_CONV Q' handle UNCHANGED => REFL Q';

    val pair_PQ_CONV = (RAND_CONV (K Q_thm)) THENC
                       (RATOR_CONV (RAND_CONV (K P_thm)))

    val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                   (RATOR_CONV (RAND_CONV pair_PQ_CONV)) tt'

    val thm0b = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
                   VAR_RES_COND_INFERENCE___loop_spec
                   (rhs (concl thm0a))

    val thm0 = CONV_RULE ((RAND_CONV o RAND_CONV) ((DEPTH_CONV BETA_CONV) THENC
                                        (K (GSYM thm0a)))) thm0b

    (*elim precond*)
    val precond = (fst o dest_imp o concl) thm0
    val precond_thm1 = PART_MATCH (fst o dest_imp) var_res_prop___IMPLIES_VAR_DISTINCT
            ((fst o dest_imp) precond)
    val precond_thm2_term = mk_imp ((snd o dest_imp o concl) precond_thm1,
                                    (snd o dest_imp) precond)
    val precond_thm2 = var_res_prove precond_thm2_term;
    val precond_thm = IMP_TRANS precond_thm1 precond_thm2;

    val thm1 = MP thm0 precond_thm;

    (*simplify invariant*)
    val post_prop = (rand o snd o dest_forall o rand o rator o fst o dest_imp o concl) thm1;
    val post_prop_thm = ((DEPTH_CONV BETA_CONV) THENC
                        var_res_prop_input_distinct___ELIM_CONV NONE THENC
                        COND_PROP___STRONG_EXISTS_NORMALISE_CONV) post_prop;

    val pre_prop = (rand o rator o rator o snd o dest_forall o rand o rator o fst o dest_imp o concl) thm1;
    val pre_prop_thm = ((DEPTH_CONV BETA_CONV) THENC
                        var_res_prop_input_distinct___ELIM_CONV NONE THENC
                        COND_PROP___STRONG_EXISTS_NORMALISE_CONV) pre_prop;

    val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV (
               (REWR_CONV pre_prop_thm) ORELSEC (REWR_CONV post_prop_thm)))) thm1

    (*reintroduce orginal variable names*)
    val my_intro_conv = (pairTools.SPLIT_QUANT_CONV vc THENC
                         TRY_CONV LIST_EXISTS_SIMP_CONV)
    val my_abs_intro_conv = pairTools.PABS_INTRO_CONV vc

    val thm3 = CONV_RULE ((RATOR_CONV o RAND_CONV)
                  ((RATOR_CONV (RAND_CONV my_intro_conv)) THENC
                   (RAND_CONV (RAND_CONV (my_intro_conv)) THENC
                   (RAND_CONV (RATOR_CONV (RAND_CONV (
                      my_intro_conv THENC
                      ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV o RAND_CONV o
                        RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                        (RAND_CONV my_abs_intro_conv THENC
                         RATOR_CONV (RAND_CONV my_abs_intro_conv)))))))))) thm2

    (*introduce comment while-abstraction*)
    val new_c1 = fasl_comment_modify_APPEND ("abstracted while-loop block") c
    val thm4a = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o
                   STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                  ((fasl_comment_location2_INTRO_CONV new_c1) THENC
                   (fasl_comment_abstraction_INTRO_CONV "while-loop block"))) thm3

    (*introduce comment while-skip*)
    val new_c2 = fasl_comment_modify_APPEND ("while-loop block unroll skip") c
    val thm4b = CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o
                   (fn conv => fn t => if listSyntax.is_nil t then conv t else
                       (RATOR_CONV o RAND_CONV) conv t))
                  (fasl_comment_location_INTRO_CONV new_c2)) thm4a


    (*introduce comment while-*)
    val new_c3 = fasl_comment_modify_APPEND ("while-loop block unroll iterate") c

    fun block_list_CONV conv t =
       if listSyntax.is_nil t then conv t else
          (RATOR_CONV o RAND_CONV) conv t
    fun block_first_CONV conv t =
         if is_fasl_prog_block t then RAND_CONV (block_list_CONV conv) t else
            conv t

    val thm4c = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o
                   block_first_CONV)
                     (fasl_comment_location_INTRO_CONV new_c3)) thm4b

    val thm4d = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                  (fasl_comment_abstraction_INTRO_CONV "re-enter while-loop")) thm4c

    (*introduce flatten blocks-*)
   val block_flatten_conv =
      (REWR_CONV VAR_RES_COND_INFERENCE___prog_block3) THENC
      ((RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
       (list_append_norm_CONV))

    val thm4 = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV)
                   block_flatten_conv) thm4d handle HOL_ERR _ => thm4d

   (*combine with thm_const*)
   val thm5a = LIST_GEN_IMP vs thm4
   val thm5 = CONV_RULE (RAND_CONV (K (GSYM thm_const))) thm5a
in
   thm5
end;




(******************************************************************************)
(* HANDLE block specs                                                         *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___block_spec___CONSEQ_CONV tt =
let
    (* destruct everything *)
    val (p1_0,c_opt,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
    val (PQ',p1) = dest_fasl_comment_block_spec p1_0;
    val (P',Q') = pairSyntax.dest_pair PQ';
    val c = if isSome c_opt then valOf c_opt else empty_label_list;

    (*introduce constants*)
    val thm_const = CONV_RULE (RHS_CONV
         VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV) (thm0_fun())
    val (vs, tt') = strip_forall (rhs (concl thm_const))


    (*apply inference*)
    val (vc, _) = pairSyntax.dest_pabs P';
    val P_thm = pairTools.PABS_ELIM_CONV P' handle UNCHANGED => REFL P';
    val Q_thm = pairTools.PABS_ELIM_CONV Q' handle UNCHANGED => REFL Q';

    val pair_PQ_CONV = (RAND_CONV (K Q_thm)) THENC
                       (RATOR_CONV (RAND_CONV (K P_thm)))

    val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                   (RATOR_CONV (RAND_CONV pair_PQ_CONV)) tt'

    val thm0b = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
                   VAR_RES_COND_INFERENCE___block_spec
                   (rhs (concl thm0a))

    val thm0 = CONV_RULE ((RAND_CONV o RAND_CONV) ((DEPTH_CONV BETA_CONV) THENC
                                        (K (GSYM thm0a)))) thm0b

    (*elim precond*)
    val precond = (fst o dest_imp o concl) thm0
    val precond_thm1 = PART_MATCH (fst o dest_imp) var_res_prop___IMPLIES_VAR_DISTINCT
            ((fst o dest_imp) precond)
    val precond_thm2_term = mk_imp ((snd o dest_imp o concl) precond_thm1,
                                    (snd o dest_imp) precond)
    val precond_thm2 = var_res_prove precond_thm2_term;
    val precond_thm = IMP_TRANS precond_thm1 precond_thm2;
    val thm1 = MP thm0 precond_thm;

    (*simplify invariant*)
    val post_prop = (rand o snd o dest_forall o rand o rator o fst o dest_imp o concl) thm1;
    val post_prop_thm = ((DEPTH_CONV BETA_CONV) THENC
                        var_res_prop_input_distinct___ELIM_CONV NONE THENC
                        COND_PROP___STRONG_EXISTS_NORMALISE_CONV) post_prop;

    val pre_prop = (rand o rator o rator o snd o dest_forall o rand o rator o fst o dest_imp o concl) thm1;
    val pre_prop_thm = ((DEPTH_CONV BETA_CONV) THENC
                        var_res_prop_input_distinct___ELIM_CONV NONE THENC
                        COND_PROP___STRONG_EXISTS_NORMALISE_CONV) pre_prop;

    val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV (
               (REWR_CONV pre_prop_thm) ORELSEC (REWR_CONV post_prop_thm)))) thm1

    (*reintroduce orginal variable names*)
    val my_intro_conv = (pairTools.SPLIT_QUANT_CONV vc THENC
                         TRY_CONV LIST_EXISTS_SIMP_CONV)

    val thm3 = CONV_RULE ((RATOR_CONV o RAND_CONV)
                  ((RATOR_CONV (RAND_CONV my_intro_conv)) THENC
                   (RAND_CONV (my_intro_conv)))) thm2

    (*introduce comment while-abstraction*)
    val new_c1 = fasl_comment_modify_APPEND ("abstracted block-spec") c
    val thm4a = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV o
                   STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                  ((fasl_comment_location2_INTRO_CONV new_c1) THENC
                   (fasl_comment_abstraction_INTRO_CONV "block-spec"))) thm3

    (*introduce comment while-skip*)
    val new_c2 = fasl_comment_modify_APPEND ("block-spec body") c
    val thm4 = CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o STRIP_QUANT_CONV o
                   RATOR_CONV o RAND_CONV o RAND_CONV o
                   (fn conv => fn t => if listSyntax.is_nil t then conv t else
                       (RATOR_CONV o RAND_CONV) conv t))
                  (fasl_comment_location_INTRO_CONV new_c2)) thm4a

   (*combine with thm_const*)
   val thm5a = LIST_GEN_IMP vs thm4
   val thm5 = CONV_RULE (RAND_CONV (K (GSYM thm_const))) thm5a
in
   thm5
end;






(******************************************************************************)
(* HANDLE assignments                                                         *)
(******************************************************************************)

(*
val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun VAR_RES_COND_INFERENCE___assign___CONSEQ_CONV tt =
let
   val (p1, _, _, _, _, thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
   val (v, e) = dest_var_res_prog_assign p1

   (* intro var *)
   val thm0a = thm0_fun();
   val (intro, c, thm0b) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV
       (mk_var_res_exp_var v (type_of e)) NONE (rhs (concl thm0a))
   val thm0 = TRANS thm0a thm0b
   val t' = let val ttt = rhs (concl thm0) in
               if intro then (snd (dest_forall ttt)) else ttt end


   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
                 VAR_RES_COND_INFERENCE___var_res_prog_assign t'
   val thm1b = var_res_precondition_prove thm1a;
   val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV o
      VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o RAND_CONV)
      ((DEPTH_CONV BAG_IMAGE_CONV) THENC
        BAG_NORMALISE_CONV)) thm1b


   (* simplifying new precond *)
   val pre = (rand o rator o rator o fst o dest_imp o concl) thm1

   val vc = pairSyntax.mk_pair (v, c);
   val vcL_t = listSyntax.mk_list ([vc], type_of vc);
   val pre_imp_thm = var_res_prop___var_res_prop_varlist_update___EVAL
             vcL_t pre


   val rw_thm = MATCH_MP VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_EQUIV
       pre_imp_thm
   val thm2 = ANTE_CONV_RULE (REWR_CONV rw_thm) thm1

   (* add new variable if necessary *)
   val thm3 = if intro then GEN_IMP c thm2 else thm2

   (* recombine *)
   val thm4 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm3

   (*eliminate new const, if not used*)
   val thm5 = ANTE_CONV_RULE (REWR_CONV FORALL_SIMP) thm4 handle
                  UNCHANGED => thm4
                | HOL_ERR _ => thm4
in
   thm5
end;


(******************************************************************************)
(* HANDLE abstractions                                                        *)
(******************************************************************************)

(*WARNING! Please remove! Just for debugging!!!*)
fun fasl_comments_EQ_PROVE p1 p2 = REFL p1;

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___abstracted_code___CONV tt =
let
   (*destruct*)
   val (p1,c_opt,_,_,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;

   val (c2, body) = dest_fasl_comment_abstraction p1 handle HOL_ERR _ =>
                    raise UNCHANGED;

   (*update comments*)
   val c1_thm = ISPECL [c2,body] fasl_comment_abstraction_def
   val c2_conv = if not (isSome c_opt) then ALL_CONV else
      let
        val new_c = fasl_comment_modify_APPEND ("abstracted "^
           (fst (dest_var c2))) (valOf c_opt)
      in
        fasl_comment_location2_INTRO_CONV new_c
      end
   val c_conv = (K c1_thm) THENC c2_conv
   (*put into the context*)
   val thm0 = ((K (thm0_fun ()))  THENC
       (VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
        c_conv)) tt
in
   thm0
end;


(******************************************************************************)
(* HANDLE procedure_calls                                                     *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
local
val my_ss1 = simpLib.conv_ss {conv = K (K fasl_procedure_call_preserve_names_wrapper_ELIM_CONV),
                 key = NONE, name = "procedure_call_preserve_names_wrapper_ELIM",
                 trace = 2}

val my_ss2 = simpLib.conv_ss {conv = K (K pairLib.GEN_BETA_CONV),
                 key = NONE, name = "GEN_BETA_CONV",
                 trace = 2}

val my_conv = SIMP_CONV (list_ss++my_ss1++my_ss2) []

in
fun VAR_RES_COND_INFERENCE___eval_expressions___CONV tt =
let
   (*destruct*)
   val (p1,pL,f,_,post) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (c,p1',p1_thm_fun) = save_dest_fasl_comment_location2 p1;
   val (p1'',expL_t) = dest_var_res_prog_eval_expressions p1'
   val (expL,_) = listSyntax.dest_list expL_t

   (*introduce expressions if necessary*)
   val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (K (p1_thm_fun ())) tt
   val thm0 = CONV_RULE (RHS_CONV (VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV
      (map (fn x => (x, NONE)) expL))) thm0a

   (*destruct again*)
   val (vL, tt') = strip_forall (rhs (concl thm0));
   val (_,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt';
   val (_, wpb, rpb, sfb, sfs) = dest_var_res_prop___propL pre

   (*find constants*)
   fun var_res_exp___is_equals_const e n t =
   let
      val (_,l,r) = dest_var_res_prop_equal t
   in
      if (aconv l e) andalso (is_var_res_exp_const r) then
         SOME (dest_var_res_exp_const r)
      else if (aconv r e) andalso (is_var_res_exp_const l) then
         SOME (dest_var_res_exp_const l)
      else NONE
   end handle HOL_ERR _ => NONE;

   fun get_const_for_exp e =
       let
          val found_opt = first_opt (var_res_exp___is_equals_const e) sfs;
          val _ = if isSome found_opt then () else raise UNCHANGED;
          val c = valOf found_opt
       in
          c
       end;
   val cL = map get_const_for_exp expL

   (*build thm*)
   val thm1a = ISPECL [f,wpb,rpb,sfb,expL_t] VAR_RES_COND_INFERENCE___eval_expressions
   val cL_type = (listSyntax.dest_list_type o type_of o fst o dest_forall o concl) thm1a;
   val cL_t = listSyntax.mk_list (cL, cL_type)

   val thm1b = ISPECL [cL_t,p1'',pL,post] thm1a

   val thm1c = var_res_precondition_prove thm1b
   val thm1d = LIST_GEN_EQ vL thm1c

   val thm2 = TRANS thm0 thm1d

   (*simplify*)
   val thm3 = CONV_RULE ((RHS_CONV o STRIP_QUANT_CONV o RATOR_CONV o
                         RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
         my_conv) thm2

   (*reintroduce comment*)
   val (p1''',_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND
       (snd (strip_forall (rhs (concl thm3))));

   val p1'''_thm = GSYM (ISPECL [c, p1'''] fasl_comment_location2_def)
   val thm4 = CONV_RULE (STRIP_QUANT_CONV (RHS_CONV
         (VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (K p1'''_thm)))) thm3
in
   thm4
end
end;


(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___quant_best_local_action___CONSEQ_CONV tt =
let
   (*destruct*)
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (c,p1',p1_thm_fun) = save_dest_fasl_comment_location2 p1
   val (has_cond, (pre, _)) =
        (false, dest_var_res_prog_quant_best_local_action p1') handle HOL_ERR _ =>
        (true, dest_var_res_prog_cond_quant_best_local_action p1')
   val vc = fst (pairSyntax.dest_pabs pre)

   (*elim comment*)
   val thm0a = p1_thm_fun ();
   val thm0  = (VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (K thm0a)
                THENC VAR_RES_COND_INFERENCE___PREPARE_FOR_FRAME___CONV) tt
   val (vs, tt') = strip_forall (rhs (concl thm0))


   (*apply inference*)
   val base_thm = if has_cond then
          VAR_RES_COND_INFERENCE___var_res_prog_cond_quant_best_local_action else
          VAR_RES_COND_INFERENCE___var_res_prog_quant_best_local_action
   val thm1 = (HO_PART_MATCH (snd o dest_imp) base_thm)  tt'

   (*use PBETA_CONV*)
   val thm2 = ANTE_CONV_RULE
                 (VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                  (TRY_CONV (RAND_CONV PairRules.PBETA_CONV) THENC
                   TRY_CONV (RATOR_CONV (RAND_CONV PairRules.PBETA_CONV))))
                 thm1

   (*introduce comments*)
   val (p1'',_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND
           ((snd o dest_exists o fst o dest_imp o concl) thm2);
   val p1''_thm = ISPECL [c, p1''] fasl_comment_location2_def;

   val thm3 = CONV_RULE (
          (RATOR_CONV o RAND_CONV o QUANT_CONV o
           VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV)
          (K (GSYM p1''_thm))) thm2


   (*use correct vars*)
   val thm4 = ANTE_CONV_RULE (pairTools.SPLIT_QUANT_CONV vc) thm3

   (*combine with thm0*)
   val thm5a = LIST_GEN_IMP vs thm4
   val thm5 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm5a

in
   thm5
end


(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___best_local_action___CONV tt =
let
   (*destruct*)
   val (p1,progL,f,P,Q) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (c,p1',p1_thm_fun) = save_dest_fasl_comment_location2 p1
   val need_star = is_asl_star (rand p1')

   (*apply_rewrite*)
   val thm1a = HO_PART_MATCH (lhs o snd o dest_imp)
          (if need_star then
             var_res_prog_cond_best_local_action_INTRO_star
           else
             var_res_prog_cond_best_local_action_INTRO) p1';
   val a = (fst o dest_imp o concl) thm1a;
   val thm1b = UNDISCH thm1a;
   val thm1 = RAND_CONV (K thm1b) (mk_fasl_comment_location2 (c, p1'))

   (*normalise pre- / post-cond and reintroduce pabs*)
   val norm_conv = var_res_prop_input_distinct___ELIM_CONV (SOME a) THENC
                   TRY_CONV COND_PROP___STRONG_EXISTS_NORMALISE_CONV
   val thm2 = DISCH a (CONV_RULE (RHS_CONV (DEPTH_CONV norm_conv)) thm1)

   (*put it in context*)
   val p1' = (rhs o snd o dest_imp o concl) thm2;
   val (_, wpb, rpb, sfb) = dest_var_res_prop P

   val thm3a = ISPECL [f, p1, p1', wpb, rpb, sfb, progL, Q]
      VAR_RES_COND_INFERENCE___first_command_REWRITE
   val precond = (fst o dest_imp o fst o dest_imp o concl) thm3a
   val precond_thm0 = var_res_prove (mk_imp (precond, a));
   val precond_thm = IMP_TRANS precond_thm0 thm2

   val thm3 = MP thm3a precond_thm
in
   thm3
end

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___cond_best_local_action___CONV tt =
let
   (*destruct*)
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (c,p1',p1_thm_fun) = save_dest_fasl_comment_location2 p1
   val (pre,post) = dest_var_res_prog_cond_best_local_action p1';



   (*bring exists in p1 in normal form*)
   val (vc_pre,  pre_thm)  = COND_PROP___STRONG_EXISTS_INTRO___CONV pre;
   val (vc_post, post_thm) = COND_PROP___STRONG_EXISTS_INTRO___CONV post;

   val thm0 = ((VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                ((K (p1_thm_fun ())) THENC
                 RAND_CONV (K post_thm) THENC
                 RATOR_CONV (RAND_CONV (K pre_thm))))) tt

   (*apply inference*)
   val new_comment = fasl_comment_modify_APPEND "final" c;
   val rfc = pairSyntax.mk_pair (T, optionSyntax.mk_some new_comment)

   val thm1a = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
         (ISPEC rfc VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE)
         (rhs (concl thm0))
   val thm1b = var_res_precondition_prove thm1a;
   val thm1 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1b


   (*get original existential vars back*)
   val new_tt = (fst o dest_imp o concl) thm1
   fun quant_restore_CONV NONE = (REWR_CONV boolTheory.FORALL_SIMP) ORELSEC (REWR_CONV boolTheory.EXISTS_SIMP)
     | quant_restore_CONV (SOME vc) = pairTools.SPLIT_QUANT_CONV vc

   val new_tt_thm = (quant_restore_CONV vc_pre THENC
                     ((STRIP_QUANT_CONV o RAND_CONV o ABS_CONV)
                     (quant_restore_CONV vc_post))) new_tt
   val thm2 = ANTE_CONV_RULE (K new_tt_thm) thm1
in
   thm2
end

local

   fun COND_PROP___STRONG_IMP___strong_exists_asl_cond_star___ELIM exists_cond_term =
   let
       val (v, cond_term) = dest_COND_PROP___STRONG_EXISTS exists_cond_term;

       val thm0 = PART_MATCH (rand o rator o snd o dest_imp)
           COND_PROP___STRONG_IMP___asl_cond_star___var_res_prop
           cond_term
       val bag_conv = bagLib.SIMPLE_BAG_NORMALISE_CONV
       val thm1 = CONV_RULE ((RAND_CONV o RAND_CONV)
             (RAND_CONV bag_conv THENC
             ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) bag_conv))) thm0

       val precond = (fst o dest_imp o concl) thm1

       val thm2 = GEN v (UNDISCH thm1)
       val thm3 = HO_MATCH_MP COND_PROP___STRONG_EXISTS___COND_PROP___STRONG_IMP thm2
   in
       (thm3, precond)
   end;

in

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___cond_best_local_action___asl_cond_star___CONSEQ_CONV tt =
let
   (*destruct*)
   val (p1,pL,f,P,Q) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, wpb, rpb, sfb) = dest_var_res_prop P;

   val (c,p1',p1_thm_fun) = save_dest_fasl_comment_location2 p1;
   val (pre,post) = dest_var_res_prog_cond_best_local_action p1';
   val _ = if (is_asl_cond_star pre) andalso (is_asl_cond_star post) then () else raise UNCHANGED;

   (*bring COND_PROP___STRONG_EXISTS in normal form*)
   val (vc_pre1,  pre1_thm)  = COND_PROP___STRONG_EXISTS_INTRO___CONV ((rand o rator) pre);
   val (vc_pre2,  pre2_thm) = COND_PROP___STRONG_EXISTS_INTRO___CONV (rand pre);

   val (vc_post1,  post1_thm)  = COND_PROP___STRONG_EXISTS_INTRO___CONV ((rand o rator) post);
   val (vc_post2,  post2_thm)  = COND_PROP___STRONG_EXISTS_INTRO___CONV (rand post);


   val pre_thm0 = (((RAND_CONV (K pre2_thm)) THENC
                  ((RATOR_CONV (RAND_CONV (K pre1_thm))))) pre)
   val pre_thm = CONV_RULE (RHS_CONV (
                    (HO_PART_MATCH lhs asl_cond_star___COND_PROP___STRONG_EXISTS___BOTH))) pre_thm0

   val post_thm0 = (((RAND_CONV (K post2_thm)) THENC
                  ((RATOR_CONV (RAND_CONV (K post1_thm))))) post)
   val post_thm = CONV_RULE (RHS_CONV (
                    (HO_PART_MATCH lhs asl_cond_star___COND_PROP___STRONG_EXISTS___BOTH))) post_thm0

   val thm0a = p1_thm_fun ();
   val thm0 = (VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV
                ((K thm0a) THENC
                 RAND_CONV (K post_thm) THENC
                 RATOR_CONV (RAND_CONV (K pre_thm)))) tt

   (*remove asl_cond_star*)
   val (cond_pre, cond_post) =
           (dest_var_res_prog_cond_best_local_action o #1 o
            dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND o rhs o concl) thm0

   val (cond_pre_thm, pre_pre) =   COND_PROP___STRONG_IMP___strong_exists_asl_cond_star___ELIM cond_pre
   val (cond_post_thm, pre_post) = COND_PROP___STRONG_IMP___strong_exists_asl_cond_star___ELIM cond_post


   val thm1a = (MATCH_MP (ISPEC f var_res_prog_cond_best_local_action___STRONG_IMP___pre_post)
                 (CONJ cond_pre_thm cond_post_thm));
   val (pre,thm1b) = if (aconv pre_pre pre_post) then (pre_pre,thm1a) else
          let
             val pre = mk_conj (pre_pre, pre_post);
             val pre_thm = ASSUME pre
             val xthm1 = MP (DISCH pre_pre  thm1a) (CONJUNCT1 pre_thm)
             val xthm2 = MP (DISCH pre_post xthm1) (CONJUNCT2 pre_thm)
          in
             (pre, xthm2)
          end;


   val pre_imp_t = mk_imp (bagSyntax.mk_all_distinct (bagSyntax.mk_union (wpb,rpb)), pre);
   val pre_imp_thm = var_res_prove pre_imp_t;
   val thm1c = DISCH (fst (dest_imp pre_imp_t)) (MP (DISCH pre thm1b) (UNDISCH pre_imp_thm))
   val thm1d = ISPECL [sfb, pL, Q]
        (MATCH_MP VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block thm1c)
   val thm1 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1d

   (*apply inference*)
   val new_comment = fasl_comment_modify_APPEND " - final" c;
   val rfc = pairSyntax.mk_pair (T, optionSyntax.mk_some new_comment)

   val thm2a = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
         (ISPEC rfc VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE)
         ((fst o dest_imp o concl) thm1)
   val thm2b = var_res_precondition_prove thm2a;
  val bag_conv = bagLib.SIMPLE_BAG_NORMALISE_CONV
   val thm2c = CONV_RULE ((RATOR_CONV o RAND_CONV o QUANT_CONV o RAND_CONV o
             ABS_CONV o QUANT_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV o
             RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
             bag_conv) thm2b

   val thm2 = IMP_TRANS thm2c thm1


   (*get original existential vars back*)
   val new_tt = (fst o dest_imp o concl) thm2
   fun quant_restore_CONV NONE = (REWR_CONV boolTheory.FORALL_SIMP) ORELSEC (REWR_CONV boolTheory.EXISTS_SIMP)
     | quant_restore_CONV (SOME vc) =
          pairTools.SPLIT_QUANT_CONV vc


   fun mk_vc NONE    NONE    = NONE
     | mk_vc vc1_opt vc2_opt =
       let
          val vc1 = if isSome vc1_opt then (valOf vc1_opt) else (genvar (Type `:unit`));
          val vc2 = if isSome vc2_opt then (valOf vc2_opt) else (genvar (Type `:unit`));
          val (vc2',_) = term_variant (free_vars vc1) (free_vars vc2) vc2
       in
          SOME (pairSyntax.mk_pair(vc1, vc2'))
       end

   val vc_pre = mk_vc vc_pre1 vc_pre2
   val vc_post = mk_vc vc_post1 vc_post2
   val new_tt_thm = (quant_restore_CONV vc_pre THENC
                    ((STRIP_QUANT_CONV o RAND_CONV o ABS_CONV)
                     (quant_restore_CONV vc_post))) new_tt
   val thm3 = ANTE_CONV_RULE (K new_tt_thm) thm2

in
   thm3
end

end


(******************************************************************************)
(* Locks                                                                      *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___release_lock___CONV tt =
let
   (*destruct*)
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (p1', c, thm0a) = let
         val (c, p1') = dest_fasl_comment_location2 p1
         val _ = if is_var_res_prog_release_lock p1' then () else raise UNCHANGED
         val c_thm = ISPECL [c, p1'] fasl_comment_location2_def;
         val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (K c_thm) tt
      in
         (p1', c, thm0a)
      end handle UNCHANGED =>
        if is_var_res_prog_release_lock p1 then (p1, empty_label_list, REFL tt) else raise UNCHANGED
   val thm0 = CONV_RULE (RHS_CONV VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV) thm0a
   val (vs, tt') = strip_forall (rhs (concl thm0))


   (*apply inference*)
   val rfc = pairSyntax.mk_pair (T, optionSyntax.mk_some c)
   val thm1a = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
         (SPEC rfc VAR_RES_COND_INFERENCE___var_res_prog_release_lock) tt'
   val thm1 = var_res_precondition_prove thm1a;

   (*combine with thm0*)
   val thm2a = LIST_GEN_IMP vs thm1
   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm2a
in
   thm2
end


(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___aquire_lock___CONV tt =
let
   (*destruct*)
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (p1', thm0a) = let
         val (c, p1') = dest_fasl_comment_location2 p1
         val _ = if is_var_res_prog_aquire_lock p1' then () else raise UNCHANGED
         val c_thm = ISPECL [c, p1'] fasl_comment_location2_def;
         val thm0a = VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV (K c_thm) tt
      in
         (p1', thm0a)
      end handle UNCHANGED =>
        if is_var_res_prog_aquire_lock p1 then (p1, REFL tt) else raise UNCHANGED
   val thm0 = CONV_RULE (RHS_CONV VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV) thm0a
   val (vs, tt') = strip_forall (rhs (concl thm0))

   (*apply inference*)
   val thm1a = HO_PART_MATCH (snd o dest_imp o snd o dest_imp)
         VAR_RES_COND_INFERENCE___var_res_prog_aquire_lock
         (rhs (concl thm0))
   val thm1 = var_res_precondition_prove thm1a;


   (*simplify*)
   val bag_conv = bagLib.SIMPLE_BAG_NORMALISE_CONV
   val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV)
                 ((RAND_CONV bag_conv) THENC
                  ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) bag_conv))) thm1

   (*combine with thm0*)
   val thm3a = LIST_GEN_IMP vs thm2
   val thm3 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm3a
in
   thm3
end

(******************************************************************************)
(* Simplify preconds                                                          *)
(******************************************************************************)
(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun VAR_RES_COND_INFERENCE___PRECOND_bool_pred___CONV ss context tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_var_res_bool_proposition tt
   val thm1 = CONV_RULE (RHS_CONV (
        REWR_CONV VAR_RES_COND_INFERENCE___var_res_bool_proposition)) thm0
   val thm2 = CONV_RULE ((RHS_CONV o RATOR_CONV o RAND_CONV)
        (VAR_RES_PROP_REWRITE_CONV ss context)) thm1
in
   thm2
end;

fun VAR_RES_COND_INFERENCE___PRECOND_trivial_cond___CONV tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_asl_trivial_cond tt
   val thm1 = CONV_RULE (RHS_CONV (
        REWR_CONV VAR_RES_COND_INFERENCE___asl_trivial_cond)) thm0
in
   thm1
end;


fun VAR_RES_COND_INFERENCE___PRECOND_stack_true___CONV tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_var_res_prop_stack_true tt
   val thm1 = CONV_RULE (RHS_CONV (
        REWR_CONV VAR_RES_COND_INFERENCE___var_res_prop_stack_true)) thm0
in
   thm1
end;


fun VAR_RES_COND_INFERENCE___PRECOND_false___CONV tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_asl_false tt
   val thm1 = EQT_INTRO (PART_MATCH I VAR_RES_COND_INFERENCE___false_precond (rhs (concl thm0)))
   val thm2 = TRANS thm0 thm1
in
   thm2
end;


fun VAR_RES_COND_INFERENCE___PRECOND_REWRITE___CONV ss context t =
      VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV
         (VAR_RES_PROP_REWRITE_CONV ss context) t;



fun VAR_RES_COND_INFERENCE___PRECOND_asl_exists___CONV tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_asl_exists tt

   val thm1 = HO_PART_MATCH (lhs o snd o dest_imp) VAR_RES_COND_INFERENCE___asl_exists_pre
           (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1 handle e => raise_var_res_prove_expn e
   val thm3 = TRANS thm0 thm2
in
   thm3
end;


fun VAR_RES_COND_INFERENCE___PRECOND_asl_star___CONV tt =
let
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV
                 is_asl_star tt

   val thm1 = PART_MATCH (lhs o snd o dest_imp) VAR_RES_COND_INFERENCE___asl_star_pre
           (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1;
   val thm3 = TRANS thm0 thm2
in
   thm3
end;



(******************************************************************************)
(* ENTAILMENTS                                                                *)
(******************************************************************************)

fun VAR_RES_FRAME_SPLIT_INFERENCE___PROP_REWRITE___CONV ss context t =
   VAR_RES_FRAME_SPLIT___PROP_CONV
         (VAR_RES_PROP_REWRITE_CONV ss context) t;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___VAR_EQ_CONST_TO_CONTEXT___CONV tt =
let
   val (f, _, _, _, _, split_sfb, _, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   (* sort all equations out *)
   val (vcL_t, split_thm) = var_res_prop___var_eq_const_BAG___INTRO f split_sfb;
   val thm0 = VAR_RES_FRAME_SPLIT___split_CONV (K split_thm) tt

   (* apply the inference *)
   val thm1a = PART_MATCH (snd o dest_imp) VAR_RES_FRAME_SPLIT___equal_const (rhs (concl thm0))
   val thm1 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1a

   (* simplify *)
   val thm2 = ANTE_CONV_RULE (VAR_RES_FRAME_SPLIT___context_split_imp_CONV
           ((DEPTH_CONV BAG_IMAGE_CONV) THENC BAG_NORMALISE_CONV)) thm1


   (*update vars*)
   val (_, _, wr, _, context_sfb, split_sfb, imp_sfb, _) =
        dest_VAR_RES_FRAME_SPLIT ((fst o dest_imp) (concl thm2));
   val (wpb,rpb) = dest_pair wr
   val (precond, rewrL) = GENERATE___var_res_exp_varlist_update___REWRITES wpb rpb vcL_t;

   fun save_conv t = (cond_rewrite___varlist_update rewrL t) handle UNCHANGED => REFL t
   val context_thm = save_conv context_sfb
   val split_thm = save_conv split_sfb
   val imp_thm = save_conv imp_sfb
   val conj_thm0 = DISCH precond (LIST_CONJ [context_thm, split_thm, imp_thm])
   val conj_thm = var_res_assumptions_prove conj_thm0

   val thm3a =
      MATCH_MP (
         ISPEC f VAR_RES_FRAME_SPLIT___WEAK_COND_REWRITE) conj_thm
   val thm3 = ANTE_CONV_RULE (PART_MATCH lhs thm3a) thm2
in
   thm3
end;



(* searches common terms in two lists of terms and returns the positions*)


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___FRAME___CONV tt =
let
   val (_, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   (* find a proposition that occurs in both *)
   val (n1l, n2l) =  get_resort_lists___pred_pair aconv split_sfb imp_sfb
   val _ = if null n1l then raise UNCHANGED else ();
   (*resort*)

   (*apply inference*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV n1l) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV n2l) THENC
               REPEATC (PART_MATCH lhs VAR_RES_FRAME_SPLIT___FRAME)) tt
in
   thm0
end;



(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___stack_true___CONV tt =
let
   val (_, _, _, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun resort_list sfb = get_resort_list___pred is_var_res_prop_stack_true sfb
   val context_nl = resort_list context_sfb
   val split_nl = resort_list split_sfb
   val imp_nl = resort_list imp_sfb

   val _ = if (null context_nl) andalso (null split_nl) andalso (null imp_nl) then
              raise UNCHANGED else ()
   (*resort*)

   (*apply inference*)
   val conv_context = if null context_nl then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___context_CONV (BAG_RESORT_CONV context_nl) THENC
        REPEATC (PART_MATCH lhs VAR_RES_FRAME_SPLIT___stack_true___context))
   val conv_split = if null split_nl then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV split_nl) THENC
        REPEATC (PART_MATCH lhs VAR_RES_FRAME_SPLIT___stack_true___split))
   val conv_imp = if null imp_nl then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV imp_nl) THENC
        REPEATC (PART_MATCH lhs VAR_RES_FRAME_SPLIT___stack_true___imp))

   val thm0 = (conv_context THENC conv_split THENC conv_imp) tt
in
   thm0
end;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___bool_pred___CONV ss context tt =
let
   val (_, _, _, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun resort_list sfb = get_resort_list___pred is_var_res_bool_proposition sfb
   val context_nl = resort_list context_sfb
   val split_nl = resort_list split_sfb
   val imp_nl = resort_list imp_sfb

   val _ = if (null context_nl) andalso (null split_nl) andalso (null imp_nl) then
              raise UNCHANGED else ()

   (*apply inference*)
   val precond_simp_conv = (RATOR_CONV (RAND_CONV (VAR_RES_PROP_REWRITE_CONV ss context)))
   fun conv_context1 t = ((PART_MATCH lhs VAR_RES_FRAME_SPLIT___bool_proposition___context) THENC
                           precond_simp_conv THENC
                          (TRY_CONV (RAND_CONV conv_context1))) t
   val conv_context = if null context_nl then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___context_CONV (BAG_RESORT_CONV context_nl) THENC
        conv_context1)
   fun conv_split1 t = ((PART_MATCH lhs VAR_RES_FRAME_SPLIT___bool_proposition___split) THENC
                         precond_simp_conv THENC
                        (TRY_CONV (RAND_CONV conv_split1))) t

   val conv_split = if null split_nl then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV split_nl) THENC
        conv_split1)

   val conv_imp = if (length imp_nl) < 2 then ALL_CONV else
       (VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV imp_nl) THENC
        REPEATC (PART_MATCH lhs VAR_RES_FRAME_SPLIT___bool_proposition___imp))

   val thm0 = (conv_imp THENC conv_split THENC ONCE_DEPTH_CONV conv_context) tt
in
   thm0
end;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___asl_star___CONV tt =
let
   val (_, _, _, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun get_resort_thm [] = raise UNCHANGED
     | get_resort_thm ((sfb, c, thm)::L) =
       let
          val nl = get_resort_list___pred is_asl_star sfb;
       in
          if null nl then get_resort_thm L else
          (c (BAG_RESORT_CONV nl) tt, thm)
       end;

   val (resort_thm, thm) = get_resort_thm
         [(context_sfb, VAR_RES_FRAME_SPLIT___context_CONV, VAR_RES_FRAME_SPLIT___asl_star___context),
          (imp_sfb, VAR_RES_FRAME_SPLIT___imp_CONV, VAR_RES_FRAME_SPLIT___asl_star___imp),
          (split_sfb, VAR_RES_FRAME_SPLIT___split_CONV, VAR_RES_FRAME_SPLIT___asl_star___split)]



   val thm1 = PART_MATCH (lhs o snd o dest_imp) thm (rhs (concl resort_thm));
   val thm2 = var_res_precondition_prove thm1
   val thm3 = TRANS resort_thm thm2
in
   thm3
end;



(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___asl_trivial_cond___CONV tt =
let
   val (_, _, _, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun get_resort_thm [] = raise UNCHANGED
     | get_resort_thm ((sfb, c, thm, has_precond)::L) =
       let
          val nl = get_resort_list___pred is_asl_trivial_cond sfb;
       in
          if null nl then get_resort_thm L else
          (c (BAG_RESORT_CONV nl) tt, thm, has_precond)
       end;

   val (resort_thm, thm, has_precond) = get_resort_thm
         [(context_sfb, VAR_RES_FRAME_SPLIT___context_CONV, VAR_RES_FRAME_SPLIT___trivial_cond___context, false),
          (imp_sfb, VAR_RES_FRAME_SPLIT___imp_CONV, VAR_RES_FRAME_SPLIT___trivial_cond___imp, true),
          (split_sfb, VAR_RES_FRAME_SPLIT___split_CONV, VAR_RES_FRAME_SPLIT___trivial_cond___split, false)]



   val thm1 = PART_MATCH (lhs o snd o dest_imp) thm (rhs (concl resort_thm));
   val thm2 = if has_precond then var_res_precondition_prove thm1 else thm1
   val thm3 = TRANS resort_thm thm2
in
   thm3
end;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___asl_false___CONV tt =
let
   val (_, _, _, _, context_sfb, split_sfb, _, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun get_resort_thm [] = raise UNCHANGED
     | get_resort_thm ((sfb, c, thm)::L) =
       let
          val nl = get_resort_list___pred is_asl_false sfb;
       in
          if null nl then get_resort_thm L else
          (c (BAG_RESORT_CONV nl) tt, thm)
       end;

   val (resort_thm, thm) = get_resort_thm
         [(context_sfb, VAR_RES_FRAME_SPLIT___context_CONV, VAR_RES_FRAME_SPLIT___asl_false___context),
          (split_sfb, VAR_RES_FRAME_SPLIT___split_CONV, VAR_RES_FRAME_SPLIT___asl_false___split)]

   val thm1 = PART_MATCH I thm (rhs (concl resort_thm));
   val thm2 = TRANS resort_thm (EQT_INTRO thm1)
in
   thm2
end;


fun VAR_RES_FRAME_SPLIT_INFERENCE___asl_exists___CONV tt =
let
   val (_, _, _, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   fun get_resort_thm [] = raise UNCHANGED
     | get_resort_thm ((sfb, c, thm)::L) =
       let
          val nl = get_resort_list___pred is_asl_exists sfb;
       in
          if null nl then get_resort_thm L else
          (c (BAG_RESORT_CONV nl) tt, thm)
       end;

   val (resort_thm, thm) = get_resort_thm
         [(context_sfb, VAR_RES_FRAME_SPLIT___context_CONV, VAR_RES_FRAME_SPLIT___asl_exists___context),
          (imp_sfb, VAR_RES_FRAME_SPLIT___imp_CONV, VAR_RES_FRAME_SPLIT___asl_exists___imp),
          (split_sfb, VAR_RES_FRAME_SPLIT___split_CONV, VAR_RES_FRAME_SPLIT___asl_exists___split)]

   val thm1 = HO_PART_MATCH (snd o dest_imp o snd o dest_imp) thm (rhs (concl resort_thm));
   val thm2 = var_res_precondition_prove thm1
   val thm3 = CONV_RULE (RAND_CONV (K (GSYM resort_thm))) thm2
in
   thm3
end;

(******************************************************************************)
(* Case splits                                                                *)
(******************************************************************************)


val case_split_thm = prove (Term `!c B.
(B = ((c ==> B) /\ (~c ==> B)))`, Cases_on `c` THEN REWRITE_TAC[])

fun case_split_heuristic___is_cond ttt =
let
   val cond_term = find_term (fn t => is_cond t) ttt
   val (c, _, _) = dest_cond cond_term;
   val (c',_) = strip_neg c;
in
   c'
end;

fun VAR_RES_COND_INFERENCE___case_split___CONV tt =
let
   val (_,pre,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE tt
   val heuristicL = (fn _ => case_split_heuristic___is_cond pre)::
      var_res_param.hoare_triple_case_splitL
   val c = tryfind (fn h => h tt) heuristicL;
in
   ISPECL [c, tt] case_split_thm
end;

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___case_split___CONV tt =
let
   val _ = if is_VAR_RES_FRAME_SPLIT tt then () else raise UNCHANGED;
   val heuristicL = (case_split_heuristic___is_cond)::
      var_res_param.frame_split_case_splitL
   val c = tryfind (fn h => h (rator tt)) heuristicL;
in
   ISPECL [c, tt] case_split_thm
end;


(******************************************************************************)
(* Strong stack proposition                                                   *)
(******************************************************************************)
local
   val ssp_conv =  REWRITE_CONV [VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]
in

fun VAR_RES_IS_PURE_PROPOSITION___prove___BASIC f p =
let
   val ttt = mk_VAR_RES_IS_PURE_PROPOSITION f p
in
   EQT_ELIM (ssp_conv ttt)
end;

end


fun VAR_RES_IS_PURE_PROPOSITION___prove f p =
   tryfind (fn pr => pr f p)
     ([VAR_RES_IS_PURE_PROPOSITION___prove___BASIC]@
     (var_res_param.VAR_RES_IS_PURE_PROPOSITION___provers))

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___strong_stack_proposition_to_context___CONV tt =
let
   val (f, _, _, _, context_sfb, split_sfb, _, _) =  dest_VAR_RES_FRAME_SPLIT tt;
   val (split_sfs,_) = dest_bag split_sfb

   val found_opt = first_opt (fn n => fn ttt =>
       SOME (n, VAR_RES_IS_PURE_PROPOSITION___prove f ttt)) split_sfs
   val _ = if isSome found_opt then () else raise UNCHANGED
   val (pos,ssp_thm) = valOf found_opt

   (*resort*)
   val thm0 = VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [pos]) tt

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
       VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT
       ((rhs o concl) thm0)
   val thm2 = MP thm1 ssp_thm
   val thm3 = TRANS thm0 thm2
in
   thm3
end;



(******************************************************************************)
(* solving entailments                                                        *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)

local

val BAG_EVERY_INSERT_IMP = prove (Term
   `!P b e. BAG_EVERY P b ==> (P (e:'a) ==> BAG_EVERY P (BAG_INSERT e b))`,
   SIMP_TAC std_ss [BAG_EVERY_THM]);


fun VAR_RES_FRAME_SPLIT___strong_stack_proposition_to_split (entail_thm, imprecise_thm) =
let
   val tt = rhs (concl entail_thm)
   val (f, _, _, _, context_sfb, _, _, _) =  dest_VAR_RES_FRAME_SPLIT tt;
   val (context_sfs,_) = dest_bag context_sfb
   val imprecise_t = (rand o rator o concl) imprecise_thm

   val found_opt = first_opt (fn n => fn ttt =>
       let
          val ssp_thm = VAR_RES_IS_PURE_PROPOSITION___prove f ttt;
          val imp_thm = var_res_prove___no_expn (mk_comb (imprecise_t, ttt))
       in
          SOME (n, ssp_thm, imp_thm, ttt)
       end) context_sfs
   val _ = if isSome found_opt then () else Feedback.fail();
   val (pos,ssp_thm,imp_thm,sf) = valOf found_opt

   (*resort*)
   val thm0 = VAR_RES_FRAME_SPLIT___context_CONV (BAG_RESORT_CONV [pos]) tt

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
       (GSYM VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT)
       ((rhs o concl) thm0)
   val thm2 = MP thm1 ssp_thm
   val thm3 = TRANS thm0 thm2

   (*construct new thms*)
   val entail_thm' = TRANS entail_thm thm3

   val BAG_EVERY_INSERT_IMP' = ISPECL [imprecise_t,
      rand (concl imprecise_thm), sf] BAG_EVERY_INSERT_IMP
   val imprecise_thm' = MP (MP BAG_EVERY_INSERT_IMP' imprecise_thm) imp_thm
in
   VAR_RES_FRAME_SPLIT___strong_stack_proposition_to_split (entail_thm', imprecise_thm')
end handle HOL_ERR _ => (entail_thm, imprecise_thm)


val IMP_CLAUSES_XT = prove (Term `!t. (t ==> T) = T`, REWRITE_TAC[]);
fun imp_true_simp t =
let
   val (t1, t2) = dest_imp_only t
in
   if (same_const t2 T) then
      SPEC t1 IMP_CLAUSES_XT
   else Feedback.fail()
end

in




(*
   val do_bool = true;
   val preserve_fallback = true
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)

fun VAR_RES_FRAME_SPLIT_INFERENCE___SOLVE___CONSEQ_CONV do_bool preserve_fallback tt =
let
   val (f,sr, wpbrpb, wpb', _, _, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   (*check whether it can be solved*)
   val (solve_thm0,has_bool) = if bagSyntax.is_empty imp_sfb then
                      (if preserve_fallback then VAR_RES_FRAME_SPLIT___SOLVE else
                            VAR_RES_FRAME_SPLIT___SOLVE_WEAK, false)
                   else let
                        val (bp, rb) = bagSyntax.dest_insert imp_sfb handle HOL_ERR _ => raise UNCHANGED;
                        val _ = if bagSyntax.is_empty rb then () else raise UNCHANGED
                        val (_, b) = dest_var_res_bool_proposition bp handle HOL_ERR _ => raise UNCHANGED
                     in
                        (SPEC b (if preserve_fallback then VAR_RES_FRAME_SPLIT___SOLVE___bool_prop else VAR_RES_FRAME_SPLIT___SOLVE_WEAK___bool_prop), true)
                     end
   val _ = if has_bool andalso (not do_bool) then raise UNCHANGED else ();

   val (wpb,rpb) = dest_pair wpbrpb;
   val solve_thm1 = ISPECL [sr, f,wpb,rpb,wpb'] solve_thm0
   val solve_thm = CONV_RULE
      ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV o
        RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
       SIMPLE_BAG_NORMALISE_CONV) solve_thm1
   val imprecise_t = (rand o rator o fst o dest_imp o snd o strip_forall o concl) solve_thm

   (*move strong_stack_propositions to context*)
   val thm0 = (REPEATC VAR_RES_FRAME_SPLIT_INFERENCE___strong_stack_proposition_to_context___CONV) tt
              handle UNCHANGED => REFL tt

   (*check whether variable conditions are met*)
   val (_, sr, _, _, _, split_sfb, _, _) =  dest_VAR_RES_FRAME_SPLIT (rhs (concl thm0));
   val sr_b = aconv (fst (pairSyntax.dest_pair sr)) T handle HOL_ERR _ => false
   val _ = if sr_b orelse bagSyntax.is_empty split_sfb then () else raise UNCHANGED

   val split_thm = var_res_prove___no_expn (mk_every (imprecise_t, split_sfb))
                   handle HOL_ERR _ => raise UNCHANGED

   (*move strong_stack_propositions to *)
   val (thm1, precond_thm) = (if sr_b then
       VAR_RES_FRAME_SPLIT___strong_stack_proposition_to_split else I)
       (thm0, split_thm)


   (*combine it*)
   val thm2a = PART_MATCH (snd o dest_imp o snd o dest_imp) solve_thm (rhs (concl thm1))
   val thm2b = MP thm2a precond_thm
   val thm2c = CONV_RULE ((RAND_CONV) (K (GSYM thm1))) thm2b

   val c_opt = SOME (optionSyntax.dest_some (snd (pairSyntax.dest_pair sr))) handle HOL_ERR _ => NONE
   val comment_intro_CONV = if not has_bool orelse not (isSome c_opt) then ALL_CONV else
       (RATOR_CONV o RAND_CONV) (fasl_comment_location_INTRO_CONV (fasl_comment_modify_APPEND "condition" (valOf c_opt)))

   val restP_conv = if not sr_b then (REWRITE_CONV [BAG_EVERY_THM]) else
       (DEPTH_CONV BETA_CONV THENC
        DEPTH_CONV SIMPLE_BAG_NORMALISE_CONV)
   val thm2d = CONV_RULE ((RATOR_CONV o RAND_CONV o
             (if preserve_fallback then RAND_CONV else I))
                     (comment_intro_CONV THENC restP_conv)) thm2c
   val thm2e = if preserve_fallback then CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)
             (SIMPLE_BAG_NORMALISE_CONV)) thm2d else thm2d

   val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) imp_true_simp) thm2e handle HOL_ERR _ => thm2e;
in
   thm2
end;

end;


(******************************************************************************)
(* Enrichment of instructions with implied properties                         *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun var_res_prop_implies_COMBINE [] = Feedback.fail()
  | var_res_prop_implies_COMBINE [thm] =
    (CONV_RULE (RAND_CONV (bagLib.SIMPLE_BAG_NORMALISE_CONV)) thm handle HOL_ERR _ => thm)
  | var_res_prop_implies_COMBINE (thm1::thm2::thmL) =
    var_res_prop_implies_COMBINE (
       (MATCH_MP var_res_prop_implies___UNION (CONJ thm1 thm2))::thmL)

fun VAR_RES_COND_INFERENCE___enrich_precond___CONV context tt =
let
   val (_,pre,prog,post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (f, wpb,rpb, sfb) = dest_var_res_prop pre

   val implies_list = flatten (
      map (fn ff => ff context (f, wpb, rpb, sfb))
         var_res_param.var_res_prop_implies___GENERATE)

   val implies_thm = var_res_prop_implies_COMBINE implies_list;
   val sfb' = rand (concl implies_thm)
   val thm0 = ISPECL [f, wpb,rpb, sfb, sfb', prog, post]
      VAR_RES_COND_INFERENCE___prop_implies
   val thm1 = MP thm0 implies_thm
   val thm2 = CONV_RULE (RHS_CONV (VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV
        (RAND_CONV bagLib.SIMPLE_BAG_NORMALISE_CONV))) thm1
in
   thm2
end;


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___enrich_split___CONV context tt =
let
   val (f, _, wr, _, context_sfb, split_sfb, imp_sfb, _) =
        dest_VAR_RES_FRAME_SPLIT tt
   val (wpb,rpb) = dest_pair wr
   val sfb = bagSyntax.mk_union (context_sfb, split_sfb)

   val implies_list = flatten (
      map (fn ff => ff context (f, wpb, rpb, sfb))
         var_res_param.var_res_prop_implies___GENERATE)

   val implies_thm = var_res_prop_implies_COMBINE implies_list;
   val sfb = rand (concl implies_thm)
   val thm0 = PART_MATCH (lhs o snd o dest_imp)
      (ISPEC sfb VAR_RES_FRAME_SPLIT___var_res_prop_implies___split) tt

   val thm1 = MP thm0 implies_thm

   val thm2 = CONV_RULE (RHS_CONV (RATOR_CONV (RATOR_CONV (
        (RAND_CONV bagLib.SIMPLE_BAG_NORMALISE_CONV))))) thm1
in
   thm2
end;


(******************************************************************************)
(* STRUCTURE_NORMALISE                                                        *)
(******************************************************************************)

fun NO_MARKER___AND_IMP_INTRO t =
if ConseqConv.is_asm_marker ((fst o dest_imp) t) then Feedback.fail () else
(PART_MATCH lhs AND_IMP_INTRO) t

fun NO_MARKER___RIGHT_IMP_FORALL_CONV t =
if ConseqConv.is_asm_marker ((rand o snd o strip_forall) t) then Feedback.fail () else
RIGHT_IMP_FORALL_CONV t

val VAR_RES_STRUCTURE_NORMALISE_CONV =
  LIST_FORALL_SIMP_CONV ORELSEC
  LIST_FORALL_AND_CONV ORELSEC
  NO_MARKER___AND_IMP_INTRO ORELSEC
  NO_MARKER___RIGHT_IMP_FORALL_CONV ORELSEC
  (PART_MATCH lhs IMP_CONJ_THM) ORELSEC
  LIST_EXISTS_SIMP_CONV


(******************************************************************************)
(* Quantifier instantiations                                                  *)
(******************************************************************************)

fun QUANT_INSTANTIATE_HEURISTIC___VAR_RES_FRAME_SPLIT___bool (sys:quant_heuristic) fv v tt =
let
   val (_,_,_,_,_,_,sfb_imp,_) = dest_VAR_RES_FRAME_SPLIT tt
			  handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val (sfs,_) = bagSyntax.dest_bag sfb_imp;
   val sfs' = filter is_var_res_bool_proposition sfs;
   val sfs'' = map rand sfs';

   val gC = COMBINE_HEURISTIC_FUNS (map (fn t => (fn () => (sys fv v t))) sfs'');
   val relevant_guesses = #others_not_possible gC;


   fun mk_only_possible g =
     let
        val (i,fvL,_) = guess_extract g
     in
        guess_only_possible (i,fvL,NONE)
     end;
   val guesses = map mk_only_possible relevant_guesses
in
  {rewrites            = #rewrites gC,
   general             = [],
   true                = [],
   false               = [],
   only_not_possible   = [],
   only_possible       = guesses,
   others_satisfied    = [],
   others_not_possible = []}:guess_collection
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp


val VAR_RES_QUANT_INSTANTIATE_CONSEQ_CONV___main  =
   EXTENSIBLE_QUANT_INSTANTIATE_STEP_CONSEQ_CONV NONE (K true) false
     ({distinct_thms = [],
      cases_thms =    [],
      rewrite_thms =  [fasl_comments_ELIM],
      convs =         [],
      heuristics =    [QUANT_INSTANTIATE_HEURISTIC___VAR_RES_FRAME_SPLIT___bool],
      final_rewrite_thms = []
      }::(var_res_param.quantifier_heuristicsL));

fun VAR_RES_QUANT_INSTANTIATE_CONSEQ_CONV ss context tt =
let
   val thm0 = VAR_RES_QUANT_INSTANTIATE_CONSEQ_CONV___main CONSEQ_CONV_STRENGTHEN_direction tt
   val c = (if (is_imp (concl thm0)) then (RATOR_CONV o RAND_CONV) else
              RAND_CONV)
(*   val thm1 = CONV_RULE (c (VAR_RES_PROP_REWRITE_CONV ss context)) thm0*)
in
   thm0
end;

(*
fun FORALL_NORMALISE_CONV tt =
let
   val (v, body) = dest_forall tt;
in
   if (is_conj body) then
      HO_PART_MATCH lhs FORALL_AND_THM tt
   else if (is_imp_only body) then
      let
         val (b1,b2) = dest_imp_only body
      in
         if not (free_in v b1) then
            HO_PART_MATCH lhs RIGHT_FORALL_IMP_THM tt
         else if not (free_in v b2) then
            HO_PART_MATCH lhs LEFT_FORALL_OR_THM tt
         else Feedback.fail()
      end
   else if (is_disj body) then
      let
         val (b1,b2) = dest_disj body
      in
         if not (free_in v b2) then
            HO_PART_MATCH lhs LEFT_FORALL_OR_THM tt
         else if not (free_in v b1) then
            HO_PART_MATCH lhs RIGHT_FORALL_OR_THM tt
         else Feedback.fail()
      end
   else Feedback.fail()
end

   SIMP_CONV std_ss [] tt
end;
*)


(*
fun VAR_RES_COND_INFERENCE___comment_quant_best_local_action___CONV var_res_param =
  fasl_comment_location_CONSEQ_CONV
     (VAR_RES_COND_INFERENCE___quant_best_local_action___CONV var_res_param)


*)



(*

ONCE_DEPTH_CONSEQ_CONV_TAC (K (VAR_RES_COND_INFERENCE___assume var_res_param))



al exp = (intro_hoare_triples current_theorem; UNCHANGED) handle x => x
val resource_and_proc_call_free_PROVE___failed_expn(_, _, SOME tt) = exp

open Profile


fun profile_program_abst s a abstL sys xenv penv =
   Profile.profile s (fn p => (a abstL sys xenv penv p)
                                handle HOL_ERR _ => NONE
                                handle UNCHANGED => NONE)



reset_all ();
val _ = time (FASL_SPECIFICATION___CONSEQ_CONV (proc_call_free_CONV, abstrL)) t;
print_profile_results (results());

abstrL



remove_holfoot_pp ()
add_holfoot_pp ()
thm


``!x. n + x + 3 = 8``




*)


(* ========================================================================== *)
(* The inferences list consists of consequence conversions that are used to   *)
(* make some kind of progress towards verifying an specification. They are    *)
(* annotated with a string describing them and a level at which to excute.    *)
(* This level is important for interactive steps later. If an inference of a  *)
(* given or lower level has been sucessfully applied, this STEP_TAC stops.    *)
(* ========================================================================== *)
(*
*)
type var_res_inference_group =
 string * (term -> bool) * bool * bool * (string * var_res_inference) list;




val VAR_RES_INFERENCES_LIST___simulate_command = ("simulate command",
   is_VAR_RES_COND_HOARE_TRIPLE, false, true, [
   ("cond",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___cond___CONSEQ_CONV),
   ("assignment",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___assign___CONSEQ_CONV),
   ("local_vars_arg",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___local_vars_args___CONSEQ_CONV),
   ("while_invariant",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___while___invariant___CONSEQ_CONV),
   ("while_loop_spec",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___while___loop_spec___CONSEQ_CONV),
   ("abstractions",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___abstracted_code___CONV),
   ("hoare_triple_solve",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___final___CONSEQ_CONV),
   ("block_spec",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___block_spec___CONSEQ_CONV)]@
   var_res_param.INFERENCES_LIST___simulate_command):var_res_inference_group;



val VAR_RES_INFERENCES_LIST___simulate_minor_command = ("simulate minor command",
   is_VAR_RES_COND_HOARE_TRIPLE, false, true, [
   ("assume",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___assume___CONSEQ_CONV),
   ("eval_expressions",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___eval_expressions___CONV),
   ("quant_best_local_action",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___quant_best_local_action___CONSEQ_CONV),
   ("best_local_action",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___best_local_action___CONV),
   ("cond_best_local_action",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___cond_best_local_action___CONV),
   ("aquire_lock",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___aquire_lock___CONV),
   ("release_lock",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___release_lock___CONV),
   ("cond_best_local_action___cond_star",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___cond_best_local_action___asl_cond_star___CONSEQ_CONV)]@
   var_res_param.INFERENCES_LIST___simulate_minor_command):
     var_res_inference_group;


val VAR_RES_INFERENCES_LIST___mayor_step = ("mayor step",
   K true, false, true, [
  ("specification",
       no_context_strengthen_conseq_conv
       VAR_RES_SPECIFICATION___CONSEQ_CONV)]):var_res_inference_group;

val VAR_RES_INFERENCES_LIST___entailment_steps = ("entailment",
   is_VAR_RES_FRAME_SPLIT, false, true, [
   ("entailment_equality",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___VAR_EQ_CONST_TO_CONTEXT___CONV),
   ("frame",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___FRAME___CONV),
   ("simp___bool_pred",
       simpset_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___bool_pred___CONV)]@
   var_res_param.INFERENCES_LIST___entailment_steps):var_res_inference_group;

val VAR_RES_INFERENCES_LIST___entailment_solve = ("entailment",
   (K true), false, true,
   [("entailment_solve",
       fn fast => (K (K (K
       (VAR_RES_FRAME_SPLIT_INFERENCE___SOLVE___CONSEQ_CONV false (not fast))))))]):var_res_inference_group;


val VAR_RES_INFERENCES_LIST___cheap_simplifications = ("cheap simps",
   (K true), false, true, [
   ("precond_simp___false",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_false___CONV),
   ("entail_simp___false",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___asl_false___CONV),
   ("precond_simp___stack_true",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_stack_true___CONV),
   ("precond_simp___bool_pred",
       simpset_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_bool_pred___CONV),
   ("precond_simp___trivial_cond",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_trivial_cond___CONV),
   ("entailment_simp___stack_true",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___stack_true___CONV),
   ("precond_simp___asl_exists",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_asl_exists___CONV),
   ("precond_simp___strong_exists",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___EXISTS_PRE___CONSEQ_CONV),
   ("precond_simp___asl_star",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_asl_star___CONV),
   ("entail_simp___asl_star",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___asl_star___CONV),
   ("entail_simp___asl_trivial_cond",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___asl_trivial_cond___CONV),
   ("entail_simp___asl_exists",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___asl_exists___CONV),
   ("comment_block",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___block_comment___CONV)]):var_res_inference_group

(*
("quantifier instantiation",
       K VAR_RES_QUANT_INSTANTIATE_CONSEQ_CONV)*)

val VAR_RES_INFERENCES_LIST___expensive_simplifications___general = ("expensive simps",
   (K true), false, true, [
   ("eliminate_comment",
       no_context_strengthen_conseq_conv
       fasl_comment_location___TF_ELIM___CONV),
   ("quantifier instantiation",
       simpset_strengthen_conseq_conv VAR_RES_QUANT_INSTANTIATE_CONSEQ_CONV)]@
   var_res_param.INFERENCES_LIST___expensive_simplifications):var_res_inference_group

val VAR_RES_INFERENCES_LIST___expensive_simplifications___hoare_triple = ("expensive simps",
   is_VAR_RES_COND_HOARE_TRIPLE, false, true, [
   ("precond_simp___rewrites",
       simpset_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___PRECOND_REWRITE___CONV),
   ("precond_simp___propagate_eq",
       no_context_strengthen_conseq_conv
       (VAR_RES_COND_INFERENCE___CONST_INTRO_PROPAGATE_EQ___CONSEQ_CONV false)),
   ("flatten_block",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___block_flatten___CONSEQ_CONV)]):var_res_inference_group;


val VAR_RES_INFERENCES_LIST___expands = ("expands",
   (K true), false, false, [
   ("precond_enrich",
       context_strengthen_conseq_conv
       (VAR_RES_COND_INFERENCE___enrich_precond___CONV)),
   ("precond_simp___intro_constants",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___ALL_CONST_INTRO___CONV)]):var_res_inference_group;


val VAR_RES_INFERENCES_LIST___expands_entailment = ("expands_entailment",
   (K true), false, true, [
   ("entailment_enrich",
       context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___enrich_split___CONV),
   ("entailment___intro_constants",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___ALL_CONST_INTRO___CONV)]):var_res_inference_group;

val VAR_RES_INFERENCES_LIST___case_splits = ("case_splits",
   (K true), false, false, [
   ("entailment_case_split",
       no_context_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___case_split___CONV),
   ("hoare_triple case split",
       no_context_strengthen_conseq_conv
       VAR_RES_COND_INFERENCE___case_split___CONV)]):var_res_inference_group;


val VAR_RES_INFERENCES_LIST___expensive_simplifications___frame_split = ("expensive simps",
   is_VAR_RES_FRAME_SPLIT, false, true, [
   ("entailment_prop_rewrites",
       simpset_strengthen_conseq_conv
       VAR_RES_FRAME_SPLIT_INFERENCE___PROP_REWRITE___CONV)]):var_res_inference_group


val VAR_RES_INFERENCES_LIST = [
   (5, VAR_RES_INFERENCES_LIST___cheap_simplifications),
   (3, VAR_RES_INFERENCES_LIST___simulate_minor_command),
   (2, VAR_RES_INFERENCES_LIST___entailment_steps),
   (2, VAR_RES_INFERENCES_LIST___entailment_solve),
   (1, VAR_RES_INFERENCES_LIST___simulate_command),
   (1, VAR_RES_INFERENCES_LIST___mayor_step),
   (5, VAR_RES_INFERENCES_LIST___expensive_simplifications___hoare_triple),
   (5, VAR_RES_INFERENCES_LIST___expensive_simplifications___frame_split),
   (5, VAR_RES_INFERENCES_LIST___expensive_simplifications___general)];



type gen_step_param =
  {use_asms       : bool,
   do_case_splits : bool,
   do_expands     : bool,
   generate_vcs   : bool,
   fast           : bool,
   do_prop_simps  : bool,
   stop_evals     : (term -> bool) list};


fun gen_step_param___update_stop_evals
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) l =
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   do_prop_simps  = ps,
   stop_evals     = l}:gen_step_param);


fun gen_step_param___update_use_asms
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = b,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param);

fun gen_step_param___update_cs
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = asms,
   do_case_splits = b,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param);

fun gen_step_param___update_vcs
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = b,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param);

fun gen_step_param___update_expands
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = b,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param);

fun gen_step_param___update_fast
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = b,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param);

fun gen_step_param___update_prop_simps
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = ps}:gen_step_param) b =
 ({use_asms       = asms,
   do_case_splits = cs,
   do_expands     = ex,
   generate_vcs   = vcs,
   fast           = f,
   stop_evals     = sel,
   do_prop_simps  = b}:gen_step_param);


local

fun step_conv_map_fun l s1 (s2, c) = c;
(*
fun step_conv_map_fun l s1 (s2, c:var_res_inference) =
  let
     val s = s1 ^ " - "^s2;
     fun conv fast ss context dir t =
        (((!(do_profile_ref ())) s (fn () =>
         (c fast ss context dir t))) ())
     fun conv2 fast ss context dir = if !verbose_level = 0 then conv fast ss context dir else
         (fn t => let
            val _ = if (l < !verbose_level_try) then
                       print ("trying "^ s ^ "\n") else ()
            val thm = conv fast ss context dir t;
            val _ = if (l < !verbose_level) then
                       print ("applying "^ s ^ "\n") else ()
           in thm end)
  in conv2 end
*)

fun convL fast stops ss n list =
  let
     fun pre (l, (s1, guard, before_flag, continue_simp, cL)) =
       let
          val cL' = map (step_conv_map_fun l s1) cL
          fun conv context dir t =
             if (not (guard t) orelse (stops t)) then raise UNCHANGED else
             tryfind (fn c => c fast ss context dir t) cL'
          val w = (if l <= n then SOME 1 else if continue_simp then NONE else SOME 0);
       in
          (before_flag, w, conv)
       end;
  in
    map pre list
  end;

in

(*
val cache_opt = SOME (mk_DEPTH_CONSEQ_CONV_CACHE,
           fn (t, (n, thm_opt)) =>
           not ((isSome thm_opt) orelse
                (is_forall t) orelse (is_exists t) orelse
                (is_imp_only t) orelse (is_disj t) orelse
                (is_conj t) orelse (is_neg t)))

val cache_opt = SOME (mk_DEPTH_CONSEQ_CONV_CACHE, K true)
val cache_opt = CONSEQ_CONV_default_cache_opt
*)

val cache_opt = NONE

type user_rewrite_param = (Abbrev.thm list * Abbrev.conv list * simpLib.ssfrag list);

fun mk_ssfrag (thmL, convL, ssfragL) =
   let
       val ss1 = simpLib.rewrites thmL;
       val ss2 = simpLib.SSFRAG {name=NONE, convs =
            (map (fn c => {conv = K (K c), key = NONE, name = "user-conversion", trace = 2}) convL),
            filter = NONE, ac=[], dprocs=[], congs=[], rewrs = []};
   in
       simpLib.merge_ss (ss1::ss2::ssfragL)
   end

val CONSEQ_CONV_CONGRUENCE___var_res_list =
    (CONSEQ_CONV_get_context_congruences CONSEQ_CONV_IMP_CONTEXT) @ [
       CONSEQ_CONV_CONGRUENCE___location_comment]


fun vc_conv vc step_opt =
   if not vc then (K (0, NONE)) else
   EXT_DEPTH_NUM_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___var_res_list NONE step_opt true
     [(true, SOME 1, K (K (VAR_RES_FRAME_SPLIT_INFERENCE___SOLVE___CONSEQ_CONV true false)))] []
   CONSEQ_CONV_STRENGTHEN_direction;

(*
   val ((fast, vc, cs), ssp, step_opt, n, context) =
       ((false, false, true), ([],[],[]), NONE, 2, [])
*)

fun VAR_RES_GEN_STEP_CONSEQ_CONV (p:gen_step_param) ssp step_opt n context  =
   let
      val list0 = VAR_RES_INFERENCES_LIST;
      val list1 = if (#do_expands p) then list0@[(2, VAR_RES_INFERENCES_LIST___expands_entailment),(2, VAR_RES_INFERENCES_LIST___expands)] else list0;
      val list2 = if (#do_case_splits p) then list1@[(2, VAR_RES_INFERENCES_LIST___case_splits)] else list1;
      val list = list2
      val stops = if null (#stop_evals p) then K false else
                      (fn t => (exists (fn pp => (pp t) handle Interrupt => raise Interrupt
                                                            | _ => false)
                                 (#stop_evals p)))
      val cL = convL (#fast p) stops (#do_prop_simps p, mk_ssfrag ssp) n list;

      fun mc step_opt =
         EXT_DEPTH_NUM_CONSEQ_CONV CONSEQ_CONV_CONGRUENCE___var_res_list NONE step_opt true
            cL context CONSEQ_CONV_STRENGTHEN_direction
      val vcc = vc_conv (#generate_vcs p);

      fun fc step_opt t =
        let
           val (n1, thm1_opt) = mc step_opt t;
           val step_opt' = step_opt_sub step_opt n1;
           val t' = if (isSome thm1_opt) then ((fst o dest_imp o concl o valOf) thm1_opt) else t


           val (n2, thm2_opt) =
               (0, SOME (snd (EQ_IMP_RULE (((REDEPTH_CONV VAR_RES_STRUCTURE_NORMALISE_CONV) THENC
                                            REWRITE_CONV []) t'))))
               handle UNCHANGED => (0, NONE)
                    | HOL_ERR _ => (0, NONE)
           val (n2, thm2_opt) = if (isSome thm2_opt) then (n2, thm2_opt) else
                (if step_opt_allows_steps step_opt' 0 (SOME 1) then
                 vcc step_opt' t' else (0, NONE))
           val thm =
              if (isSome thm1_opt) then
                 (if (isSome thm2_opt) then
                    IMP_TRANS (valOf thm2_opt) (valOf thm1_opt)
                  else valOf thm1_opt)
              else
                 (if (isSome thm2_opt) then
                    valOf thm2_opt
                  else raise UNCHANGED)
        in
           if not (isSome thm2_opt) then thm else
           let
              val step_opt'' = step_opt_sub step_opt' n2;
              val t'' = (fst o dest_imp o concl) thm
              val thm3_opt = SOME (fc step_opt'' t'') handle UNCHANGED => NONE
           in
              if (isSome thm3_opt) then
                IMP_TRANS (valOf thm3_opt) thm
              else thm
           end
        end;
   in
      fc step_opt
   end;

end;


fun VAR_RES_GEN_STEP_TAC (p:gen_step_param) ss step_opt n =
   if (#use_asms p) then
      (DISCH_ASM_CONSEQ_CONV_TAC (K (VAR_RES_GEN_STEP_CONSEQ_CONV p ss step_opt n [])))
   else
      (CONSEQ_CONV_TAC (K (VAR_RES_GEN_STEP_CONSEQ_CONV p ss step_opt n [])));


datatype gen_step_tac_opt =
    case_splits_flag of bool
  | expands_flag of bool
  | fast_flag of bool
  | prop_simp_flag of bool
  | use_asms_flag of bool
  | generate_vcs_flag of bool
  | add_rewrites of thm list
  | add_convs of conv list
  | add_ssfrags of simpLib.ssfrag list
  | stop_evals of (term -> bool) list
  | combined_gen_step_tac_opt of gen_step_tac_opt list

val no_case_splits        = case_splits_flag false;
val no_expands            = expands_flag false;
val no_case_split_expands = combined_gen_step_tac_opt [no_case_splits, no_expands]
val do_case_splits        = case_splits_flag true;
val do_expands            = expands_flag true;
val generate_vcs          = generate_vcs_flag true;
val dont_generate_vcs     = generate_vcs_flag false;
val no_asms               = use_asms_flag false;
val use_asms              = use_asms_flag true;
val no_prop_simps         = prop_simp_flag false;
val conservative          = fast_flag false;
val careful               = combined_gen_step_tac_opt [no_case_splits, no_expands, no_asms];

val stop_at_while = stop_evals [fn t =>
    let
       val (p1_0,_,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location t;
    in
       is_fasl_comment_loop_invariant p1_0 orelse
       is_fasl_comment_loop_spec p1_0 orelse
       is_fasl_prog_while p1_0
    end]

val stop_at_cond = stop_evals [fn t =>
    let
       val (p1_0,_,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location t;
    in
       is_fasl_prog_cond p1_0
    end]

val stop_at_abstraction = stop_evals [fn t =>
    let
       val (p1_0,_,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location t;
    in
       is_fasl_comment_abstraction p1_0
    end]

val stop_at_block_spec = stop_evals [fn t =>
    let
       val (p1_0,_,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location t;
    in
       is_fasl_comment_block_spec p1_0
    end]


val stop_at_frame_calc = stop_evals [is_VAR_RES_FRAME_SPLIT]
val stop_at_hoare_triple = stop_evals [is_VAR_RES_COND_HOARE_TRIPLE]



fun gen_step_tac_opt_eval (p:gen_step_param, ssp) [] = (p, ssp)
  | gen_step_tac_opt_eval (p, (rw, cv, ss))
       ((add_rewrites thmL)::gstoL) =
    gen_step_tac_opt_eval (p, (rw@thmL, cv, ss)) gstoL
  | gen_step_tac_opt_eval (p, (rw, cv, ss))
       ((add_convs convL)::gstoL) =
    gen_step_tac_opt_eval (p, (rw, cv@convL, ss)) gstoL
  | gen_step_tac_opt_eval (p, (rw, cv, ss))
       ((add_ssfrags ssfL)::gstoL) =
    gen_step_tac_opt_eval (p, (rw, cv, ss@ssfL)) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((case_splits_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_cs p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((expands_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_expands p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((fast_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_fast p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((prop_simp_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_prop_simps p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((use_asms_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_use_asms p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((generate_vcs_flag b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_vcs p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((stop_evals b)::gstoL) =
    gen_step_tac_opt_eval (gen_step_param___update_stop_evals p b, ssp) gstoL
  | gen_step_tac_opt_eval (p, ssp)
       ((combined_gen_step_tac_opt optL)::gstoL) =
    gen_step_tac_opt_eval (p, ssp) (optL@gstoL)


val default_params = (
   {do_case_splits = true,
    do_expands = true,
    fast = true,
    use_asms = true,
    do_prop_simps = true,
    stop_evals = [],
    generate_vcs = false}, ([],[],[]))



fun xVAR_RES_GEN_STEP_TAC optL =
   let
      val (p,ssp) = gen_step_tac_opt_eval default_params optL;
   in
      VAR_RES_GEN_STEP_TAC p ssp
   end;

fun xVAR_RES_GEN_STEP_CONSEQ_CONV optL n m =
   let
      val (p,ssp) = gen_step_tac_opt_eval default_params optL
   in
      VAR_RES_GEN_STEP_CONSEQ_CONV p ssp n m []
   end;



val _ = Rewrite.add_implicit_rewrites [fasl_comments_TF_ELIM];

val VAR_RES_PURE_VC_TAC =
 CONSEQ_CONV_TAC (K (fn t =>
     let
        val (_, thm_opt) = vc_conv true NONE t
     in
        if isSome thm_opt then valOf thm_opt else raise UNCHANGED
     end))

val VAR_RES_ELIM_COMMENTS_TAC = REWRITE_TAC [fasl_comments_ELIM]
val VAR_RES_VC_TAC = (TRY VAR_RES_PURE_VC_TAC) THEN VAR_RES_ELIM_COMMENTS_TAC


end


