functor vars_as_resourceBaseFunctor (var_res_param : 
sig     
    val combinator_thmL              : Abbrev.thm list
    val prover_extra                 : Abbrev.thm list * Abbrev.thm list
    val varlist_rwts                 : Abbrev.thm list
    val exp_to_string                : Abbrev.term -> string
end) :
sig
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

       val var_res_prop___var_res_prop_varlist_update___EVAL : term -> conv;
       val VAR_RES_COND_INFERENCE___PRECOND_var_res_prop_varlist_update___EVAL : term -> conv
       val GENERATE___var_res_exp_varlist_update___REWRITES : term -> term -> term -> (term * thm list)
       val cond_rewrite___varlist_update : thm list -> conv
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
end =
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
open ConseqConv

(*
quietdec := false;
*)


(******************************************************************************)
(* Forced conditional rewriting                                               *)
(******************************************************************************)


local
   fun CONJ_SPLIT tt =
   let
      val (t1,t2) = dest_conj tt;
      val thm1 = CONJ_SPLIT t1;
      val thm2 = CONJ_SPLIT t2;
   in
      CONJ thm1 thm2
   end handle HOL_ERR _ => ASSUME tt;
in
   fun UNDISCH_SPLIT thm =
   let
      val precond = (fst o dest_imp o concl) thm
   in
      MP thm (CONJ_SPLIT precond)
   end;
end;


fun COND_REWR_CONV___with_match thm =
  if (is_imp (concl thm)) then
     if (is_eq (snd (dest_imp (concl thm)))) then
        (UNDISCH_SPLIT o (PART_MATCH (lhs o snd o dest_imp) thm),
         (lhs o snd o dest_imp o concl) thm)
     else
        (EQT_INTRO o UNDISCH_SPLIT o (PART_MATCH (snd o dest_imp) thm),
        (snd o dest_imp o concl) thm)
  else
     if (is_eq (concl thm)) then
        (PART_MATCH lhs thm,
         (lhs o concl) thm)
     else
        (EQT_INTRO o PART_MATCH I thm,
         concl thm);


fun COND_REWR_CONV thm =
    fst (COND_REWR_CONV___with_match thm);

fun COND_REWRITE_CONV___PREPOCESS thmL =
    (map COND_REWR_CONV___with_match (flatten (map BODY_CONJUNCTS thmL)));

fun GABS_CONV conv tm =
    case dest_term tm of
        LAMB(Bvar,Body) => ((ABS_CONV conv tm) handle HOL_ERR _ =>
        let
           fun conv2 tm =
              SPEC Bvar (GEN_ASSUM Bvar (conv tm));	    
        in
          ABS_CONV conv2 tm
        end)
    | _ => raise ERR "GABS_CONV" "Term not an abstraction"


fun GSUB_CONV conv t =    
    (TRY_CONV (COMB_CONV conv ORELSEC GABS_CONV conv) t)

fun GREDEPTH_CONV conv tm =
    (GSUB_CONV (GREDEPTH_CONV conv) THENC
     TRY_CONV (conv THENC GREDEPTH_CONV conv)) tm

fun EXT_COND_REWRITE_CONV top ctL thmL =
   let
     val conv_termL = ctL @ (COND_REWRITE_CONV___PREPOCESS thmL);
     val net = foldr (fn ((conv,t),net) => Net.insert (t,conv) net) Net.empty conv_termL;
   in
     (if top then REPEATC else GREDEPTH_CONV) (fn t =>
        let
          val convL = Net.match t net;
        in
          FIRST_CONV convL t
        end)
   end;

fun COND_REWRITE_CONV top thmL =
   EXT_COND_REWRITE_CONV top [] thmL;


fun GUARDED_COND_REWRITE_CONV top p thmL =
   let
      val conv = COND_REWRITE_CONV top thmL
   in
      fn t => if p t then conv t else NO_CONV t
   end



(******************************************************************************)
(* The proofer used for everything!                                           *)
(******************************************************************************)

val prover_cache_opt = mk_PERSISTENT_DEPTH_CONSEQ_CONV_CACHE_OPT (K true)
fun prover_cache_clear () = clear_CONSEQ_CONV_CACHE_OPT prover_cache_opt

val var_res_prove_RWL = [
      pairTheory.FST, pairTheory.SND, LENGTH,
      MAP, listTheory.ALL_DISTINCT,
      bagTheory.BAG_IN_BAG_INSERT,
      bagTheory.NOT_IN_EMPTY_BAG,
      bagTheory.BAG_ALL_DISTINCT_THM,
      MEM, optionTheory.THE_DEF,
      UNION_SUBSET, IN_UNIV,
      EMPTY_SUBSET, INSERT_SUBSET,
      DE_MORGAN_THM,
      FEVERY_FEMPTY,
      ZIP,
      IN_UNION, bagTheory.BAG_EVERY_THM, IN_DIFF,
      IN_INSERT, EVERY_DEF,
      FDOM_FUPDATE, FDOM_FEMPTY,
      NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
      bagTheory.BAG_UNION_EMPTY,
      bagTheory.BAG_UNION_INSERT,
      bagTheory.BAG_DISJOINT_EMPTY,
      bagTheory.BAG_DISJOINT_BAG_INSERT,
      bagTheory.IN_SET_OF_BAG,
      bagTheory.SET_OF_BAG_UNION,
      bagTheory.SET_OF_BAG_INSERT,
      bagTheory.BAG_OF_EMPTY,
      bagTheory.BAG_IN_BAG_UNION,
      bagTheory.NOT_IN_EMPTY_BAG,
      bagTheory.SET_OF_BAG_MERGE,
      bagTheory.BAG_IN_BAG_INSERT,
      bagTheory.FINITE_BAG_THM,
      bagTheory.BAG_INSERT_NOT_EMPTY,
      ELIM_UNCURRY,
      LIST_TO_SET_THM,
      SUBSET_REFL, IN_LIST_TO_SET,
      VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF];

   val var_res_prove_CONV =
   let
      val rewrites = flatten [
          var_res_param.combinator_thmL,
          (fst (var_res_param.prover_extra)),
          var_res_prove_RWL]
      val var_res_prove_cs = listLib.list_compset ();
      val _ = computeLib.add_thms rewrites var_res_prove_cs 
      val _ = computeLib.add_conv (stringSyntax.ord_tm, 1, stringLib.ORD_CHR_CONV) var_res_prove_cs
      val _ = computeLib.add_thms [stringTheory.CHR_ORD,stringTheory.CHAR_EQ_THM,stringTheory.ORD_11] var_res_prove_cs

      val strengthen = append [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___VAR_RES_REWRITES,
                               FEVERY_STRENGTHEN_THM]
                       (snd (var_res_param.prover_extra)) 
   in
      FULL_EXT_CONSEQ_REWRITE_CONV 
            (CONSEQ_CONV_get_context_congruences CONSEQ_CONV_IMP_CONTEXT)
            prover_cache_opt NONE true true []
            [(true, SOME 1, K (CHANGED_CONV (computeLib.CBV_CONV var_res_prove_cs))),
             (false, SOME 1, fn context => REWRITE_CONV (rewrites@context))]
        ([], strengthen, []) CONSEQ_CONV_STRENGTHEN_direction
   end

exception var_res_prove___failed_expn of (term * term option);
fun var_res_prove tttt =
   let
      val thm = var_res_prove_CONV tttt handle UNCHANGED => Feedback.fail ()
      val precond = (fst o dest_imp o concl) thm
      val _ = if (aconv precond T) then () else
              raise var_res_prove___failed_expn (tttt, SOME precond)
   in
      MP thm TRUTH
   end handle HOL_ERR _ =>
      raise var_res_prove___failed_expn (tttt, NONE)


fun raise_var_res_prove_expn (var_res_prove___failed_expn (tttt, p)) =
   (print "Proof failed on term:\n``";
   print_term tttt;
   if (isSome p) then (
      print "``\n\nCould not simplify subgoal:\n``";
      print_term (valOf p))
   else ();
   print "``\n";
   Feedback.fail())
| raise_var_res_prove_expn e = Raise e;

fun var_res_prove___no_expn tttt =
   var_res_prove tttt handle var_res_prove___failed_expn _ => Feedback.fail()

(*
  val var_res_prove___failed_expn (args, tttt, SOME precond) =
     (var_res_assumptions_prove args thm; UNCHANGED) handle x => x;
*)

fun var_res_assumptions_prove thm =
   foldl (fn (h, thm) =>
        (MP (DISCH h thm) (var_res_prove h))) thm (hyp thm)

fun var_res_precondition_prove thm =
let
   val precond = (fst o dest_imp o concl) thm;
   val precond_thm = var_res_prove precond
in

   MP thm precond_thm
end;


fun var_res_precondition_assumption_prove NONE thm = var_res_precondition_prove thm
  | var_res_precondition_assumption_prove (SOME a) thm =
let
   val precond = mk_imp (a, (fst o dest_imp o concl) thm);
   val precond_thm = UNDISCH (var_res_prove precond);
in

   MP thm precond_thm
end;



(******************************************************************************)
(* General helpers for the following inferences                               *)
(******************************************************************************)


fun bag_el_conv conv n b =
let
   val (insert_term, rest_term) = dest_comb b;
in
   if (n = 0) then
      AP_THM (RAND_CONV conv insert_term) rest_term
   else
      AP_TERM insert_term (bag_el_conv conv (n-1) rest_term)
end

fun var_res_prop___bag_el_conv conv n =
   RAND_CONV (bag_el_conv conv n)


fun var_res_prop_unequal_SYM_CONV t =
    let
       val (f,l,r) = dest_var_res_prop_unequal t;
    in
       ISPECL [f,l,r] var_res_prop_unequal_symmetric
    end;

fun var_res_prop_equal_SYM_CONV t =
    let
       val (f,l,r) = dest_var_res_prop_equal t;
    in
       ISPECL [f,l,r] var_res_prop_equal_symmetric
    end


fun var_res_prop___COND_RESORT_CONV rl = RAND_CONV (bagLib.BAG_RESORT_CONV rl);
fun VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV rl =
    (RATOR_CONV o RATOR_CONV o RAND_CONV) (var_res_prop___COND_RESORT_CONV rl)

val VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND___CONV =
    ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV o
       RAND_CONV o RATOR_CONV o RAND_CONV))


fun first_opt___simple_pred p (n:int) (t:term) =
   if p t then SOME n else NONE

fun VAR_RES_COND_HOARE_TRIPLE___find_prop_in_precond p tt =
   let
      val (_, pre, _, _) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
      val (_,_,_,sfb) = dest_var_res_prop pre;
      val (sfs, _) = bagSyntax.dest_bag sfb;
   in
      first_opt p sfs
   end

fun VAR_RES_COND_HOARE_TRIPLE___FIND_RESORT_PRECOND_CONV p tt =
let
   val found_opt = VAR_RES_COND_HOARE_TRIPLE___find_prop_in_precond
       (first_opt___simple_pred p) tt
   val _ = if (isSome found_opt) then () else raise UNCHANGED;
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [valOf found_opt] tt
in
   thm0
end


fun VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV pre_conv t =
let
   val (f, pre, prog, post) = dest_VAR_RES_COND_HOARE_TRIPLE t;
   val thm0 = pre_conv pre;
   val term0 = concl thm0;
in
   if (is_eq term0) then
      let
         val b = (rator o rator o rator) t
         val thm1 = AP_TERM b thm0;
         val thm2 = AP_THM thm1 prog;
         val thm3 = AP_THM thm2 post;
      in
         thm3
      end
   else if (is_COND_PROP___IMP term0) then
      let
         val (p1,p2) = dest_COND_PROP___IMP (concl thm0);
         val thm1 = ISPECL [f, p1,p2,prog,post] VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP
         val thm2 = MP thm1 thm0;
      in
         thm2
      end
   else if (is_COND_PROP___EQUIV term0) then
      let
         val (p1,p2) = dest_COND_PROP___EQUIV (concl thm0);
         val thm1 = ISPECL [f, p1,p2,prog,post] VAR_RES_COND_HOARE_TRIPLE___COND_PROP_EQUIV
         val thm2 = MP thm1 thm0;
      in
         thm2
      end
   else raise UNCHANGED
end;


(******************************************************************************)
(* Conversions for entailments                                                *)
(******************************************************************************)


fun VAR_RES_FRAME_SPLIT___imp_CONV c  =
    (RATOR_CONV o RAND_CONV) c 

fun VAR_RES_FRAME_SPLIT___split_CONV c  =
    (RATOR_CONV o RATOR_CONV o RAND_CONV) c 

fun VAR_RES_FRAME_SPLIT___context_CONV c  =
    (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) c 

fun VAR_RES_FRAME_SPLIT___context_split_imp_CONV c =
   (VAR_RES_FRAME_SPLIT___context_CONV c THENC
    VAR_RES_FRAME_SPLIT___split_CONV c THENC
    VAR_RES_FRAME_SPLIT___imp_CONV c)


fun VAR_RES_FRAME_SPLIT___PROP_CONV c t =
    if (is_VAR_RES_FRAME_SPLIT t) then
       VAR_RES_FRAME_SPLIT___context_split_imp_CONV c t
    else raise UNCHANGED


(******************************************************************************)
(* Normalising equations                                                      *)
(******************************************************************************)

fun var_res_prop_equal_unequal___NORMALISE_CONV t =
    let
       val (uneq, (f,l,r)) = (false, dest_var_res_prop_equal t) handle HOL_ERR _ =>
                             (true,  dest_var_res_prop_unequal t) handle HOL_ERR _ =>
                             raise UNCHANGED;
       val do_rewrite = (aconv l r) orelse ((is_var_res_exp_const l) andalso (is_var_res_exp_const r));
       val do_turn = (not do_rewrite) andalso
             ((is_var_res_exp_var r andalso not (is_var_res_exp_var l)) orelse
              ((not ((not (is_var_res_exp_var r)) andalso (is_var_res_exp_var l)))
                 andalso (Term.compare (r, l) = LESS)))
    in
       if do_turn then
          ISPECL [f,l,r]
             (if uneq then var_res_prop_unequal_symmetric else
                           var_res_prop_equal_symmetric)
       else if do_rewrite then
             REWRITE_CONV [var_res_prop_equal_unequal_REWRITES,
                var_res_exp_is_defined___const, var_res_bool_proposition_TF]
             t
       else raise UNCHANGED
    end;


(******************************************************************************)
(* Normalising conditions                                                     *)
(******************************************************************************)

(*
   val tt = find_term is_var_res_prop_binexpression_cond (snd (top_goal ()))
*)
fun var_res_prop_binexpression_cond___asl_false___NORMALISE_CONV tt =
    let
       val (f, p,e1,e2,p1,p2) = dest_var_res_prop_binexpression_cond tt

       val (P, thm0) = if is_asl_false p1 then 
                     (p2, var_res_prop_binexpression_cond___asl_false___true)
                  else if is_asl_false p2 then
                     (p1, var_res_prop_binexpression_cond___asl_false___false)
                  else raise UNCHANGED;

       val thm1 = ISPECL [f,p,e1,e2,P] thm0
       val thm2 = var_res_precondition_prove thm1
    in
       thm2
    end;



(******************************************************************************)
(* Introduce new constants                                                    *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun var_res_exp___is_equals_const e n t =
   let
      val (_,l,r) = dest_var_res_prop_equal t
   in
      if (aconv l e) andalso (is_var_res_exp_const r) then
         SOME (n, false, dest_var_res_exp_const r)
      else if (aconv r e) andalso (is_var_res_exp_const l) then
         SOME (n, true, dest_var_res_exp_const l)
      else NONE
   end handle HOL_ERR _ => NONE;



fun var_res_exp_vars___is_equals_const vL n t =
   let
      val (_,l,r) = dest_var_res_prop_equal t
      val v' = dest_var_res_exp_var l;
      val c = dest_var_res_exp_const r;
   in
      if (mem v' vL) then SOME (n, v', c) else NONE
   end handle HOL_ERR _ => NONE;


fun get_const_name_for_exp suffix e =
let
   val v_st = var_res_param.exp_to_string e
   val v_st' = (String.translate (fn c =>
      if c = #"(" then Feedback.fail() else
      if c = #")" then Feedback.fail() else
      if c = #"*" then Feedback.fail() else
      if c = #"-" then Feedback.fail() else
      if c = #"/" then Feedback.fail() else
      if c = #"+" then Feedback.fail() else
      if c = #" " then Feedback.fail() else str c) v_st)
      handle HOL_ERR _ => "c";
in
  v_st' ^ suffix
end;


(*find pattern (v1 = v2) * ... (v2 = c) and
  reduce it to (v1 = c) * .... (v2 = c) *)

fun var_res_exp_var___is_equals_var_eq_const sfs n tt =
   let
      val (_,l,r) = dest_var_res_prop_equal tt
      val v1 = dest_var_res_exp_var l;
      val v2 = dest_var_res_exp_var r;

      val v_opt = first_opt (var_res_exp_vars___is_equals_const [v1, v2]) sfs
   in
      if isSome v_opt then
         let
            val (n', v', c) = valOf v_opt
            val turn = not (aconv v' v2)
         in
            SOME (n, n', turn, v1, v2, v', c)
         end
      else NONE
   end


fun var_res_prop___VAR_EQ_PROPAGATE___STEP tt =
let
   val (_, _, _, sfb) = dest_var_res_prop tt
   val sfs = fst (bagSyntax.dest_bag sfb)

   val foundOpt = first_opt
      (var_res_exp_var___is_equals_var_eq_const sfs) sfs

   val _ = if isSome foundOpt then () else raise UNCHANGED;

   val (n1, n2, turn, _, _, _, _) = valOf foundOpt

   val thm0 = var_res_prop___COND_RESORT_CONV [n1, n2] tt
   val thm1 = if turn then
                CONV_RULE (RHS_CONV (var_res_prop___bag_el_conv
                    var_res_prop_equal_SYM_CONV 0)) thm0
              else
                thm0

   val thm2a = PART_MATCH (lhs o snd o dest_imp) var_res_prop___equal_const___equal_var
               (rhs (concl thm1));
   val thm2b = var_res_precondition_prove thm2a

   val thm2 = TRANS thm1 thm2b
in
   thm2
end handle HOL_ERR _ => raise UNCHANGED;



fun var_res_prop___VAR_EQ_PROPAGATE tt =
if not (is_var_res_prop tt) then raise UNCHANGED else
((DEPTH_CONV var_res_prop_equal_unequal___NORMALISE_CONV) THENC
REPEATC (var_res_prop___VAR_EQ_PROPAGATE___STEP)) tt


fun VAR_RES_COND_INFERENCE___FORCED_CONST_INTRO___CONV e c_name_opt tt =
let
   (*instantiate theorem*)
   val thm1a = ISPEC e VAR_RES_COND_INFERENCE___CONST_INTRO;
   val thm1 = PART_MATCH (lhs o snd o dest_imp) thm1a tt

   (*remove precondition*)
   val thm2 = var_res_precondition_prove thm1;

   (*use nice new constant name*)
   val c_name = if (isSome c_name_opt) then valOf c_name_opt else
                   (get_const_name_for_exp "_const" e);
   val thm3 = CONV_RULE (RHS_CONV (RENAME_VARS_CONV [c_name])) thm2
   val c = (fst o dest_forall o rhs o concl) thm3;
in
   (c, thm3)
end;


fun VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e c_name_opt tt =
let
   val _ = if is_VAR_RES_COND_HOARE_TRIPLE tt then () else raise UNCHANGED;
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV
                    (var_res_prop___VAR_EQ_PROPAGATE) tt handle UNCHANGED =>
              REFL tt
   val tt' = rhs (concl thm0);

   val foundOpt = VAR_RES_COND_HOARE_TRIPLE___find_prop_in_precond
      (var_res_exp___is_equals_const e) tt'
in
   if isSome(foundOpt) then
      let
          val (pos,turn,c) = valOf foundOpt
          val thm1 = CONV_RULE (RHS_CONV (
                        VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [pos])) thm0
          val thm2 = if turn then CONV_RULE (RHS_CONV (
                        VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV
                        (var_res_prop___bag_el_conv var_res_prop_equal_SYM_CONV 0
                        ))) thm1 else thm1
      in
         (false, c, thm2)
      end
   else
      if (is_var_res_exp_const e) then let
         val c = dest_var_res_exp_const e;
         val thm1a = ISPEC c VAR_RES_COND_INFERENCE___TRIVIAL_CONST_INTRO;
         val thm1 = PART_MATCH lhs thm1a tt
         val thm2 = TRANS thm0 thm1
      in
         (false, c, thm2)
      end else let
          val (c, thm1) = VAR_RES_COND_INFERENCE___FORCED_CONST_INTRO___CONV
                             e c_name_opt tt'

          (*incorparate original modifications*)
          val thm2 = TRANS thm0 thm1
      in
          (true, c, thm2)
      end
end


fun VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV [] tt =
   raise UNCHANGED
| VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV ((e, c_name_opt)::vL) tt =
  let
     val (intro, _, thm0) =
       VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e c_name_opt tt
     val conv2 = VAR_RES_COND_INFERENCE___CONST_LIST_INTRO___CONV vL;
     val conv2' = if intro then QUANT_CONV conv2 else conv2

     val thm1 = CONV_RULE (RHS_CONV conv2') thm0
  in
     thm1
  end;


fun VAR_RES_FRAME_SPLIT_INFERENCE___SIMPLE_CONST_INTRO___CONV e tt =
let
   val thm1a = ISPEC e VAR_RES_FRAME_SPLIT___CONST_INTRO
   val thm1 = PART_MATCH (lhs o snd o dest_imp) thm1a tt

   (*remove precondition*)
   val thm2 = var_res_precondition_prove thm1;
in
   thm2
end;


fun VAR_RES_FRAME_SPLIT_INFERENCE___FORCED_CONST_INTRO___CONV e c_name_opt tt =
let
   (*remove precondition*)
   val thm2 = VAR_RES_FRAME_SPLIT_INFERENCE___SIMPLE_CONST_INTRO___CONV e tt;

   (*use nice new constant name*)
   val c_name = if (isSome c_name_opt) then valOf c_name_opt else 
                   (get_const_name_for_exp "_const" e);
   val thm3 = CONV_RULE (RHS_CONV (RENAME_VARS_CONV [c_name])) thm2
in
   thm3
end


(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun VAR_RES_FRAME_SPLIT_INFERENCE___CONST_INTRO___CONV e c_name_opt tt =
let
   val (_, _, _, _, context_sfb, split_sfb, _, _) = dest_VAR_RES_FRAME_SPLIT tt

   val sfs = append (fst (dest_bag context_sfb)) (fst (dest_bag split_sfb))
   val foundOpt = first_opt (var_res_exp___is_equals_const e) sfs;
   val _ = if (isSome foundOpt) then raise UNCHANGED else ();
in
   VAR_RES_FRAME_SPLIT_INFERENCE___FORCED_CONST_INTRO___CONV e c_name_opt tt
end


fun VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV []  = ALL_CONV 
  | VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV ((e, c_name_opt)::vL) =
     (VAR_RES_FRAME_SPLIT_INFERENCE___CONST_INTRO___CONV e c_name_opt) THENC
     (STRIP_QUANT_CONV (
        VAR_RES_FRAME_SPLIT_INFERENCE___CONST_LIST_INTRO___CONV vL))




(******************************************************************************)
(* Simplify predicates                                                        *)
(******************************************************************************)

local
   fun prepare_context acc [] = acc
     | prepare_context acc (thm::thms) =
       if (is_eq (concl thm)) then
          let
             val (l,r) = dest_eq (concl thm)
             val turn = (is_var r) andalso (not (is_var l))
             val new_eq = if turn then GSYM thm else thm
          in
             prepare_context (new_eq::acc) thms
          end 
       else 
          prepare_context (thm::acc) thms

   val var_res_prop_general_rewrites = [
         var_res_bool_proposition_TF,
         var_res_prop_binexpression___emp___consts,
         var_res_prop_expression___NIL,
         var_res_prop_expression___CONS_CONST,
         asl_trivial_cond_TF,
         BOOL_TO_NUM_REWRITE,
         asl_trivial_cond___asl_false,
         asl_trivial_cond___var_res_stack_true,
         var_res_exp_binop___const_eval,
         var_res_exp_add_sub_REWRITES,
         asl_false___asl_star_THM,
         var_res_prop_binexpression_cond___CONST_REWRITE,
         var_res_exp_op_CONS_CONST, var_res_exp_op_NIL,
         var_res_exp_is_defined___const,
         GSYM var_res_prop_equal_def,
         GSYM var_res_prop_unequal_def]
   
   val ss_1 = std_ss ++ (simpLib.rewrites var_res_prop_general_rewrites);
   val ss_2 = ss_1 ++ (simpLib.merge_ss [
            simpLib.conv_ss {conv = K (K var_res_prop_equal_unequal___NORMALISE_CONV),
                 key = NONE, name = "var_res_prop_equal_unequal___NORMALISE_CONV", 
                 trace = 2},
            simpLib.conv_ss {conv = K (K var_res_prop_binexpression_cond___asl_false___NORMALISE_CONV),
                 key = NONE, name = "var_res_prop_binexpression_cond___asl_false___NORMALISE_CONV", 
                 trace = 2}])

   val ss_final = ss_2

in

fun VAR_RES_PROP_REWRITE_CONV (do_something, ss) context =
   if not do_something then ALL_CONV else
   SIMP_CONV (ss_final++ss++simpLib.rewrites (prepare_context [] context)) []

end


(******************************************************************************)
(* Eliminate var_res_prop_varlist_update                                      *)
(******************************************************************************)

val BAG_NORMALISE_CONV = REWRITE_CONV [
     var_res_prop___var_eq_const_BAG_THM,
     el 1 (BODY_CONJUNCTS BAG_UNION_INSERT), BAG_UNION_EMPTY];


val BAG_ALL_DISTINCT_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [BAG_ALL_DISTINCT_THM, BAG_ALL_DISTINCT_BAG_UNION,
    BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, BAG_DISJOINT_EMPTY, BAG_DISJOINT_BAG_INSERT,
    BAG_IN_BAG_UNION, DE_MORGAN_THM, GSYM CONJ_ASSOC]
    BAG_ALL_DISTINCT_cs;


fun GENERATE___var_res_exp_varlist_update___REWRITES wpb rpb vcL_t =
let
   (*get the unequal rewrites*)
   val ass_rewr_0 = ASSUME (mk_all_distinct (mk_union (wpb, rpb)))
   val ass_rewr = CONV_RULE (computeLib.CBV_CONV BAG_ALL_DISTINCT_cs) ass_rewr_0;

   val ass_rewrL0 = filter (fn thm => is_eq (dest_neg (concl thm)) handle HOL_ERR _ => false)
          (BODY_CONJUNCTS ass_rewr)
   val ass_rewrL = append ass_rewrL0 (map GSYM ass_rewrL0)


   (*for which variables?*)
   val vL = (fst (dest_bag wpb)) @  (fst (dest_bag rpb))

   val (var_ty, data_ty) = (pairSyntax.dest_prod (listSyntax.dest_list_type (type_of vcL_t)))

   val vcL_t_v = 
       let
          val vL_tL = map (fst o pairSyntax.dest_pair) ((fst o listSyntax.dest_list) vcL_t)
          val vL_tvL = map (fn v => pairSyntax.mk_pair (v, genvar data_ty)) vL_tL
       in
          listSyntax.mk_list (vL_tvL, pairSyntax.mk_prod (var_ty, data_ty))
       end;
   val base_t0 = inst [Type.alpha |-> var_ty,
                       Type.beta  |-> data_ty,
                       Type.gamma |-> (optionSyntax.mk_option data_ty)] var_res_exp_varlist_update_term;
   val base_t = mk_comb (base_t0, vcL_t_v);
   val var_exp_t = inst [Type.beta |-> var_ty, Type.alpha |-> data_ty]
         var_res_exp_var_term;


   fun mk_var_rewr v = let
     val t0 = mk_comb(base_t, mk_comb (var_exp_t, v));
     val thm0 = REWRITE_CONV
        (var_res_exp_varlist_update___var_EVAL::
         var_res_exp_varlist_update_NIL::ass_rewrL) t0
   in
     thm0
   end;

   val thmL = map mk_var_rewr vL
in
   (concl ass_rewr_0, thmL)
end;


local

fun o_ABS_R___PAIRED_CONV t =
   let
      val _ = combinSyntax.dest_o t;
      val (vs,_) = pairSyntax.dest_pabs (rand t);
      val conv1 = (RAND_CONV pairTools.PABS_ELIM_CONV)
      val conv2 = HO_REWR_CONV combinTheory.o_ABS_R
      val conv3 = pairTools.PABS_INTRO_CONV vs     
   in
      (conv1 THENC conv2 THENC conv3) t
   end handle HOL_ERR _ => raise UNCHANGED;

val conv_termL = COND_REWRITE_CONV___PREPOCESS 
   (var_res___varlist_update_NO_VAR_THM::MAP::
    (GSYM o_f_FUPDATE_WEAK)::
    o_f_FEMPTY::(var_res_param.varlist_rwts))@
   [(o_ABS_R___PAIRED_CONV,Term `var_res_prop_varlist_update vcL o X`)];

in

(* 
val SOME (rewrL, t) = !tref *)
fun cond_rewrite___varlist_update rewrL =
    let val conv = EXT_COND_REWRITE_CONV false conv_termL rewrL in
    fn t => let
       val thm0 = conv t;
       val _ = let
           val ct_opt = SOME (find_term (
                  fn t => same_const var_res_prop_varlist_update_term (fst (strip_comb t))) (rhs (concl thm0))) handle HOL_ERR _ => NONE
           val ct_opt = if isSome ct_opt then ct_opt else (SOME (find_term (
                  fn t => same_const var_res_exp_varlist_update_term (fst (strip_comb t))) (rhs (concl thm0))) handle HOL_ERR _ => NONE)
         in
           if isSome ct_opt then (
            print "\n\n\n!!!Could not simplify:\n";
            print_term (valOf ct_opt);
            print "\nin\n";
            print_term (rhs (concl thm0));
            print "\n\n";
            Feedback.fail()) else ()
         end 
    in
       thm0
    end end;

end

fun var_res_prop___var_res_prop_varlist_update___EVAL vcL_t tt =
let
    val (f, wpb, rpb, sfb) = dest_var_res_prop tt;
    val (precond, rewrL) = GENERATE___var_res_exp_varlist_update___REWRITES wpb rpb vcL_t;

    val sfb_thm0 = cond_rewrite___varlist_update rewrL sfb handle UNCHANGED => REFL sfb

    val sfb_thm1 = DISCH precond sfb_thm0
    val sfb_thm = var_res_assumptions_prove sfb_thm1

    val thm0 = ISPECL [f, wpb, rpb, sfb, rhs (concl sfb_thm0)]  COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE;
    val thm1 = MP thm0 sfb_thm
in
    thm1
end;


fun VAR_RES_COND_INFERENCE___PRECOND_var_res_prop_varlist_update___EVAL vcL_t tt =
let
   val (f, pre, prog, post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;

   val pre_thm = RAND_CONV ((DEPTH_CONV BAG_IMAGE_CONV) THENC BAG_NORMALISE_CONV) pre
        handle UNCHANGED => REFL pre
   val imp_thm = var_res_prop___var_res_prop_varlist_update___EVAL vcL_t (rhs (concl pre_thm))
   val imp_thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) (K (GSYM pre_thm))) imp_thm
   val pre' = rand (concl imp_thm2);
   
   val thm0 = ISPECL [f, pre, pre', prog, post] VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_EQUIV;
   val thm1 = MP thm0 imp_thm2
in
   thm1
end;





(******************************************************************************)
(* var_res_inference                                                          *)
(******************************************************************************)

type var_res_inference = bool -> (bool * simpLib.ssfrag) -> thm list -> directed_conseq_conv

fun no_context_conseq_conv conv =
    (K (K (K conv))):var_res_inference

fun no_context_strengthen_conseq_conv conv =
    (no_context_conseq_conv (STRENGTHEN_CONSEQ_CONV conv))

fun context_strengthen_conseq_conv conv =
   (K (K (fn context => (STRENGTHEN_CONSEQ_CONV (conv context))))):var_res_inference

fun simpset_no_context_strengthen_conseq_conv conv =
   (K (fn ss => (K (STRENGTHEN_CONSEQ_CONV (conv ss))))):var_res_inference

fun simpset_strengthen_conseq_conv conv =
   (K (fn ss => (fn context => (STRENGTHEN_CONSEQ_CONV (conv ss context))))):var_res_inference
									     
end
