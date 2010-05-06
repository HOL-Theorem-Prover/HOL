structure holfootLib :> holfootLib =
struct


(*
quietdec := true;
use (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/header.sml");

loadPath := 
            (concat [Globals.HOLDIR, "/src/quantHeuristics"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) :: 
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "stringTheory", "vars_as_resourceTheory", "stringLib", "listLib",
    "holfootTheory"]; 

show_assums := true; *)

open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory finite_mapTheory pred_setTheory
open generalHelpersTheory
open separationLogicTheory;
open separationLogicSyntax
open vars_as_resourceSyntax
open vars_as_resourceTheory
open vars_as_resourceSyntax
open quantHeuristicsLib
open quantHeuristicsArgsLib
open treeTheory
open ConseqConv
open holfootSyntax treeSyntax
open holfootParser 
open holfoot_pp_print 
open holfootTheory 
open bagLib bagTheory
open separationLogicLib
open simpLib
open permLib;
open HolSmtLib;

(*
open vars_as_resourceBaseFunctor
open vars_as_resourceFunctor
*)

(*
structure holfootTacs = vars_as_resourceFunctor (holfoot_param)

val examplesDir = concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot/EXAMPLES/automatic/"]
val file = concat [examplesDir, "parallel_mergesort_data.sf"]; 
val file = concat [examplesDir, "mergesort.dsf"]; 
val file = concat [examplesDir, "tree.dsf"]; 


val t = parse_holfoot_file file
set_goal ([], t)
STEP_TAC ([],[],[]) 1
val _ = set_goal ([], t)
SOLVE_TAC

backend_use_annotations := false
val _ = Parse.current_backend := emacs_terminal;

val _ = Parse.current_backend := vt100_user_style_terminal;


VAR_RES_SPECIFICATION_TAC
SOLVE_TAC
STEP_TAC 1000
STEP_TAC 0

SIMP_TAC std_ss [SORTED_DEF, PERM_REFL, FORALL_AND_THM,
   IMP_CONJ_THM]


REPEAT CONJ_TAC
rotate 1

*)

fun holfoot_term_to_string t =
   if (is_var t) then
       fst (dest_var t)
   else if (is_holfoot_exp_null t) then "null" 
   else if (is_var_res_exp_const t) then
       holfoot_term_to_string (dest_var_res_exp_const t)
   else if (is_holfoot_tag t) then
       stringLib.fromHOLstring (dest_holfoot_tag t)
   else if (is_var_res_exp_var t) then
       holfoot_term_to_string (dest_var_res_exp_var t) 
   else if (is_holfoot_var t) then
       stringLib.fromHOLstring (dest_holfoot_var t)
   else term_to_string t;


fun is_no_proper_diseq thm = 
   let
      val (t1, t2) = dest_eq (dest_neg (concl thm));
   in
      (same_const t1 numSyntax.zero_tm) orelse
      (same_const t2 numSyntax.zero_tm)
   end handle HOL_ERR _ => true;


structure holfoot_base_param = 
struct
   val exp_to_string = holfoot_term_to_string;

   val combinator_thmL = 
       [IS_VAR_RES_COMBINATOR___holfoot_separation_combinator,
        GET_VAR_RES_COMBINATOR___holfoot_separation_combinator,
        REWRITE_RULE [holfoot_separation_combinator_def] IS_VAR_RES_COMBINATOR___holfoot_separation_combinator,
        REWRITE_RULE [holfoot_separation_combinator_def] GET_VAR_RES_COMBINATOR___holfoot_separation_combinator,
        IS_SEPARATION_COMBINATOR___FINITE_MAP, IS_SEPARATION_COMBINATOR___holfoot_separation_combinator,
        REWRITE_RULE [holfoot_separation_combinator_def] IS_SEPARATION_COMBINATOR___holfoot_separation_combinator];

   val varlist_rwts = [holfoot___varlist_update_NO_VAR_THM];

   val prover_extra = ([holfoot_tag_11, holfoot_var_11],
                    [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___HOLFOOT_REWRITES]);
end

(*
structure var_res_param = holfoot_base_param
*)

structure holfoot_base = vars_as_resourceBaseFunctor (holfoot_base_param)
open holfoot_base


(******************************************************************************)
(* Decide whether something is inside array bound                             *)
(******************************************************************************)
(*
val cref = ref NONE
fun array_bound_DECIDE context t = 
   let
      val _ = cref := SOME context;
      val _ = print_term t;
      val thm_opt = SOME (EQT_ELIM (SIMP_CONV arith_ss context t)) handle HOL_ERR _ => NONE;
      val _ = print (if isSome thm_opt then "OK" else "FAIL");
      val _ = print "\n";
      val _ = if isSome thm_opt then () else Feedback.fail()
   in
      valOf thm_opt
   end
*)

val sub_add_simp = prove (``(((x:num) + (c1:num)) - (x + c2)) = (c1 - c2)``, DECIDE_TAC)

val arith_simp_ss = 
   std_ss ++ simpLib.merge_ss [
     (numSimps.ARITH_DP_FILTER_ss is_no_proper_diseq),
     simpLib.rewrites [arithmeticTheory.ADD1, SUB1,
      sub_add_simp]]

fun holfoot_arith_simp_CONV context t = 
   SIMP_CONV arith_simp_ss context t
  handle UNCHANGED => REFL t

fun array_bound_DECIDE___HOL context t = 
   (EQT_ELIM (holfoot_arith_simp_CONV context t)) 


fun array_bound_DECIDE___YICES context t = 
let
   val (_, vali) = YICES_TAC (map concl context, t)
   val xthm0 = vali [];
   val xthm1 = foldl (fn (h, thm) => PROVE_HYP h thm) xthm0 context
in
   xthm1
end;


val (array_bound_DECIDE___YICES, _) =
  Cache.CACHE ((K true), array_bound_DECIDE___YICES)

val holfoot_use_yices = ref 0;
val _ = Feedback.register_trace ("holfoot use Yices", holfoot_use_yices, 4);

fun array_bound_DECIDE context t = 
   if (!holfoot_use_yices = 1) then array_bound_DECIDE___YICES context t else
   if (!holfoot_use_yices = 0) then array_bound_DECIDE___HOL context t else
   let
      fun run f context t = 
        (let
            val thm = f context t
         in
            if (aconv (concl thm) t) then SOME thm else 
            (print "PROBLEM\n\n\n";NONE)
         end) handle Interrupt => raise Interrupt
                   | HOL_ERR _ => Feedback.fail()
                   | e => (print "EXN-problem\n\n";Raise e)

      val thm1_opt = run array_bound_DECIDE___YICES context t;
      val thm2_opt = run array_bound_DECIDE___HOL context t;

      fun print_thm_opt NONE = print "-"
        | print_thm_opt (SOME thm) = print_thm thm;

      val _ = if (isSome thm1_opt = isSome thm2_opt) then () else
              let
                  val _ = print "Yices: ";
                  val _ = print_thm_opt thm1_opt;
                  val _ = print "\n";
                  val _ = print "HOL: ";
                  val _ = print_thm_opt thm2_opt;
                  val _ = print "\n";
              in () end
      val thm_opt = if (!holfoot_use_yices mod 2 = 1) then thm1_opt else thm2_opt
   in
      if isSome thm_opt then valOf thm_opt else Feedback.fail()
   end;


fun prove_in_array_bound context ec (ec', nc') =
   let
      val thm_t = mk_conj (
                      numSyntax.mk_leq (ec', ec),
                      numSyntax.mk_less (ec, numSyntax.mk_plus (ec', nc')))
   in 
      array_bound_DECIDE context thm_t
   end;


fun prove_in_interval_bound context ec (ec2, ec3) =
   let
      val thm_t = mk_conj (
                      numSyntax.mk_leq (ec2, ec),
                      numSyntax.mk_leq (ec, ec3))
   in 
      array_bound_DECIDE context thm_t
   end;

fun prove_in_array_interval_bound true = prove_in_interval_bound
  | prove_in_array_interval_bound false = prove_in_array_bound


(******************************************************************************)
(* Generate additional information about var_res_prop by analysing, what's    *)
(* in the stack                                                               *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
   val context = map ASSUME (fst (top_goal()))
   val (_, pre, _, _) = dest_VAR_RES_COND_HOARE_TRIPLE tt
   val (_, wpb, rpb, sfb) = dest_var_res_prop pre

val sfb = ``BAG_INSERT (var_res_prop_unequal DISJOINT_FMAP_UNION e3 e4) ^sfb``
val sfb = ``BAG_INSERT (var_res_prop_unequal DISJOINT_FMAP_UNION e5 e3) ^sfb``
         
*)

fun dest_neq t = dest_eq (dest_neg t)
val is_neq = can dest_neg

exception var_res_implies_unequal_found_expn 
local
   fun is_var_res_prop_unequal_opt_pred e1 e2 (n:int) t =
   let
       val (_,e1', e2') = dest_var_res_prop_unequal t;
       val no_turn = (aconv e1 e1') andalso (aconv e2 e2');
       val turn = (not no_turn) andalso
                  (aconv e1 e2') andalso (aconv e2 e1')
   in
       if no_turn orelse turn then SOME (n, turn) else NONE
   end;
   val BAG_IN_TRIVIAL_THM = prove (Term `!e:'a b. BAG_IN e (BAG_INSERT e b)`,
       REWRITE_TAC [bagTheory.BAG_IN_BAG_INSERT])

   val var_res_implies_unequal___trivial_unequal_1 =
       var_res_implies_unequal___trivial_unequal
   val var_res_implies_unequal___trivial_unequal_2 =
       ONCE_REWRITE_RULE [var_res_implies_unequal_SYM] var_res_implies_unequal___trivial_unequal

in

fun var_res_implies_unequal___prove___in_bag no_thm context sfb e1 e2 =
let
   val sfs = fst (dest_bag sfb)
   val found_opt = first_opt (is_var_res_prop_unequal_opt_pred e1 e2) sfs
   val _ = if isSome (found_opt) then () else Feedback.fail();
   val _ = if no_thm then raise var_res_implies_unequal_found_expn else ()
   val (n, turn) = valOf found_opt;

   val thm0 = if turn then var_res_implies_unequal___trivial_unequal_2 else
                           var_res_implies_unequal___trivial_unequal_1

   val thm1 = ISPECL [holfoot_disjoint_fmap_union_term, sfb, e1,e2] thm0

   val sfb_resort_thm = BAG_RESORT_CONV [n] sfb
   val sfb' = rhs (concl sfb_resort_thm)   
   val precond_thm0 = PART_MATCH rand BAG_IN_TRIVIAL_THM sfb';
   val precond_thm1 = CONV_RULE (RAND_CONV (K (GSYM sfb_resort_thm)))
                         precond_thm0

   val thm2 = MP thm1 precond_thm1
in
   thm2
end;
end;


local
   fun unequal_opt_pred c1 c2 (n:int) thm =
   let
       val (c1', c2') = dest_neq (concl thm);
       val no_turn = (aconv c1 c1') andalso (aconv c2 c2');
       val turn = (not no_turn) andalso
                  (aconv c1 c2') andalso (aconv c2 c1')
   in
       if no_turn orelse turn then 
          SOME (if turn then (GSYM thm) else thm) else NONE
   end;
in
fun var_res_implies_unequal___prove___context no_thm context sfb e1 e2 =
let
   val c1 = dest_var_res_exp_const e1;
   val c2 = dest_var_res_exp_const e2;
   
   val found_opt = first_opt (unequal_opt_pred c1 c2) context
   val found_opt = if isSome (found_opt) then found_opt else 
          SOME (array_bound_DECIDE___HOL context (mk_neg (mk_eq (c1, c2))))
   val _ = if no_thm then raise var_res_implies_unequal_found_expn else ();
   val thm_context = valOf found_opt;

   val thm1 = ISPECL [holfoot_disjoint_fmap_union_term, sfb, c1,c2] 
          var_res_implies_unequal___trivial_context
   val thm2 = MP thm1 thm_context
in
   thm2
end;
end


fun var_res_implies_unequal___prove_opt no_thm context sfb e1 e2 =
   let
      val sfb_thm_opt = 
            (SOME (bagLib.SIMPLE_BAG_NORMALISE_CONV sfb)) handle UNCHANGED => NONE
      val sfb' = if isSome (sfb_thm_opt) then rhs (concl (valOf sfb_thm_opt)) else sfb
   val thm = tryfind (fn f => ((f no_thm context sfb' e1 e2)
             handle var_res_implies_unequal_found_expn => TRUTH) )
             [var_res_implies_unequal___prove___context,
              var_res_implies_unequal___prove___in_bag]
   val thm2 = if not (isSome sfb_thm_opt) then thm else
              (CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                          (K (GSYM (valOf sfb_thm_opt)))) thm)
in
   thm2
end;

fun var_res_implies_unequal___prove context =
    var_res_implies_unequal___prove_opt false context;

fun var_res_implies_unequal___check context sfb e1 e2=
   (var_res_implies_unequal___prove_opt true context sfb e1 e2;true) handle
       HOL_ERR _ => false

fun var_res_implies_unequal___prove___term context ttt =
   let
      val (_, sfb, e1, e2) = dest_var_res_implies_unequal ttt
   in
      var_res_implies_unequal___prove context sfb e1 e2
   end;






fun holfoot_implies_in_heap_GENERATE___points_to _ _ sfb tt =
let
   val (e,L) = dest_holfoot_ap_points_to tt;
   val thm0 = ISPECL [sfb, e, L] holfoot_ap_points_to___implies_in_heap___COMPUTE    
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []

fun holfoot_implies_in_heap_GENERATE___data_list_seg _ context sfb tt =
let
   val (tag_t,e1,data,e2) = dest_holfoot_ap_data_list_seg tt;
   val unequal_thm_opt = SOME (var_res_implies_unequal___prove context sfb e1 e2) handle HOL_ERR _ => NONE
in
   if (isSome unequal_thm_opt) then
   let
      val thm0 = ISPECL [e1, e2, sfb, tag_t, data]
           holfoot_ap_data_list_seg___implies_in_heap___COMPUTE
      val thm1 = MP thm0 (valOf unequal_thm_opt)
      val thm2 = var_res_precondition_prove thm1
   in
      [thm2]
   end else let
      val _ = if (is_holfoot_exp_null e2) then () else raise UNCHANGED;
      val thm0 = ISPECL [sfb, e1, tag_t, data]
           holfoot_ap_data_list___implies_in_heap_or_null___COMPUTE
      val thm1 = var_res_precondition_prove thm0
   in
      [thm1]
   end
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE___tree _ _ sfb tt =
let
   val (tagL,e1) = dest_holfoot_ap_tree tt;
   val thm0 = ISPECL [e1, tagL, sfb]
           holfoot_ap_tree___implies_in_heap_or_null___COMPUTE
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE___data_tree _ _ sfb tt =
let
   val (tagL,e1,data) = dest_holfoot_ap_data_tree tt;
   val thm0 = ISPECL [e1, tagL, data, sfb]
           holfoot_ap_data_tree___implies_in_heap_or_null___COMPUTE
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE___data_array_interval tL context sfb tt =
let
   val (is_interval, (e1,e2,data)) = dest_holfoot_ap_data_array_interval tt;
   val c1 = dest_var_res_exp_const e1
   val c2 = dest_var_res_exp_const e2
   val base_thm = ISPECL [c1, c2, data, sfb]
          (if (is_interval) then
              holfoot_ap_data_interval___implies_in_heap___COMPUTE
           else
              holfoot_ap_data_array___implies_in_heap___COMPUTE);

   val ec_vars = FVL [c1,c2] empty_tmset;
   fun term_filter t = (type_of t = numSyntax.num) andalso
       ((is_var t) orelse (not (HOLset.isEmpty (HOLset.intersection (FVL [t] empty_tmset, ec_vars)))))
   val constL = 
       HOLset.listItems (
         foldl (fn (l,s) => HOLset.addList (s,l)) empty_tmset
            (map (find_terms term_filter) (sfb::tL)));

   fun inst_const c =
   let
       val xthm0 = SPEC c base_thm;
       val pre = (fst o dest_imp o concl) xthm0
       val pre_thm = array_bound_DECIDE context pre       
   in
     MP xthm0 pre_thm
   end
in
   mapfilter inst_const constL
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE tL context sfb tt =
   flatten
   (map (fn f => (f tL context sfb tt) handle Interrupt => raise Interrupt
                                         | e => []) [
       holfoot_implies_in_heap_GENERATE___points_to,
       holfoot_implies_in_heap_GENERATE___data_list_seg,
       holfoot_implies_in_heap_GENERATE___tree,
       holfoot_implies_in_heap_GENERATE___data_tree,
       holfoot_implies_in_heap_GENERATE___data_array_interval])


fun holfoot_implies_in_heap___or_null___EXTEND_BAG sfb2 thm =
let
   val ((sfb,sfb1,ex), sub_thm) = 
        (dest_holfoot_implies_in_heap_or_null (concl thm),
         holfoot_implies_in_heap_or_null___SUB_BAG) handle HOL_ERR _ =>
        (dest_holfoot_implies_in_heap (concl thm),
         holfoot_implies_in_heap___SUB_BAG) handle HOL_ERR _ => Feedback.fail()

   val thm1a = ISPECL [sfb, sfb1, sfb2,ex] sub_thm;

   val pre1 = SUB_BAG_INSERT_SOLVE ((fst o dest_imp o concl) thm1a)
   val thm1b = MP thm1a pre1;
   val thm1c = var_res_precondition_prove thm1b
   val thm1 = MP thm1c thm
in
   thm1
end;


fun holfoot_implies_in_heap_or_null___prove context sfb ex =
if is_holfoot_exp_null ex then
   ISPECL [sfb,sfb] holfoot_implies_in_heap_or_null___const_null
else let
   val sfb_thm = BAG_NORMALISE_CONV sfb handle UNCHANGED => REFL sfb;
   val sfb' = rhs (concl sfb_thm)
   val sfs = fst (dest_bag sfb');

   val implies_in_heapL =
      flatten (map (holfoot_implies_in_heap_GENERATE [] context sfb') sfs);


   fun holfoot_implies_in_heap_or_null___check thm =
       let
           val (_,_,ex') = dest_holfoot_implies_in_heap_or_null (concl thm);
       in
           if (aconv ex ex') then SOME thm else NONE
       end handle HOL_ERR _ => NONE

   fun holfoot_implies_in_heap___check thm =
       let
           val (_,_,ex') = dest_holfoot_implies_in_heap (concl thm);
           val _ = if (aconv ex ex') then () else Feedback.fail ();
       in
           SOME (MATCH_MP holfoot_implies_in_heap___implies___or_null thm)           
       end handle HOL_ERR _ => NONE

   fun holfoot_implies_check thm =
       case holfoot_implies_in_heap_or_null___check thm of
          NONE   => holfoot_implies_in_heap___check thm
        | SOME t => SOME t;

   val thm_opt = first_opt (K holfoot_implies_check) implies_in_heapL;
   val thm = if isSome thm_opt then valOf thm_opt else Feedback.fail();

   val thm2 = holfoot_implies_in_heap___or_null___EXTEND_BAG sfb' thm

   val thm3a = CONV_RULE (RATOR_CONV (RAND_CONV (K (GSYM sfb_thm)))) thm2
   val thm3  = CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV (K (GSYM sfb_thm))))) thm3a
in
 thm3
end;

fun holfoot_implies_GENERATE___data_array_interval ss context (wpb, rpb) sfb =
let
   val sfs = fst (dest_bag sfb);
   fun indexes n p [] = []
     | indexes n p (e::es) =
         let
            val r_opt = p (e);
            val l = indexes (n + 1) p es;
         in
            if (isSome  r_opt) then ((n, (valOf r_opt))::l) else l
         end;

   fun my_holfoot_ap_data_array___pred tt =
   let
      val (is_interval, (e1, e2, dataL)) = dest_holfoot_ap_data_array_interval tt;
      val (td, _) = listSyntax.dest_cons dataL;
      val (_, d) = pairSyntax.dest_pair td;      
      val length_d0 = listSyntax.mk_length d;
      val length_thm = (VAR_RES_PROP_REWRITE_CONV ss context length_d0)
                       handle UNCHANGED => REFL length_d0;
      val length_d = rhs (concl length_thm);
      val length_const = mk_comb (holfoot_exp_const_term, length_d);

      (*check, whether this lenght should be introduced*)
      val _ = if is_interval then
                 let
                    val c1 = dest_var_res_exp_const e1;
                    val c2 = dest_var_res_exp_const e2;
                    val b_t = mk_eq (length_d, 
                        numSyntax.mk_minus (numSyntax.mk_suc c2, c1))
                    val is_new = ((array_bound_DECIDE context b_t);false)
                        handle HOL_ERR _ => true;
                 in
                    if (is_new) then () else Feedback.fail()
                 end
              else (
                 (* its an array*)
                 if (exists (is_var_res_prop_equal_sym e2 length_const) sfs) then
                    (Feedback.fail ())
                 else if not (is_var_res_exp_const e2) then () else
                 let                  
                    val c2 = dest_var_res_exp_const e2;
                    val b_t = mk_eq (length_d, c2)
                    val is_new = ((array_bound_DECIDE context b_t);false)
                        handle HOL_ERR _ => true;
                 in
                    if (is_new) then () else Feedback.fail()
                 end)
   in
      SOME (is_interval, length_thm)
   end handle HOL_ERR _ => NONE;

   val iL = indexes 0 my_holfoot_ap_data_array___pred sfs;

   fun process_index (i, (is_interval, l_thm)) = 
   let
       val sfb_thm = BAG_RESORT_CONV [i] sfb;
       val xthm0 = if (is_interval) then
            (PART_MATCH (rand o rator) 
                (ISPECL [wpb, rpb] holfoot_ap_data_interval___var_res_prop_implies___length_eq)
                (rhs (concl sfb_thm))) else 
            let
               val ythm0 = PART_MATCH (rand o rator o snd o dest_imp) 
                   (ISPECL [wpb, rpb] holfoot_ap_data_array___var_res_prop_implies___length_eq)
                    (rhs (concl sfb_thm));
               val ythm1 = var_res_precondition_prove ythm0;
            in
               ythm1
            end;
       val xthm1 = CONV_RULE (RATOR_CONV (RAND_CONV (K (GSYM sfb_thm)))) xthm0
       val xthm2 = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [l_thm])) xthm1
   in
      [xthm2]
   end handle HOL_ERR _ => [];
in
   flatten (map process_index iL)
end handle HOL_ERR _ => []
         | UNCHANGED => []


local
   fun mk_unequal_null context thm0 =
   let
       val (sfb, b, e) = dest_holfoot_implies_in_heap (concl thm0)
       val already_known = 
          var_res_implies_unequal___check context sfb e holfoot_exp_null_term;
       val _ = if already_known then Feedback.fail () else ();

       val sub_bag_thm = SUB_BAG_INSERT_SOLVE (bagSyntax.mk_sub_bag (b, sfb))
       
       val thm1 = ISPECL [sfb,b,e] holfoot_implies_in_heap___implies_unequal___null;
       val thm2 = MP thm1 (CONJ sub_bag_thm thm0)
   in
      thm2
   end;

   fun mk_in_heap_pair acc [] = acc
     | mk_in_heap_pair acc (thm::thmL) =
         mk_in_heap_pair
           ((map (fn thm2 => 
               if (is_holfoot_implies_in_heap (concl thm)) then
                  (thm, thm2) else (thm2, thm)) thmL)@acc) thmL;


   fun mk_unequal___in_heap___in_heap context (thm1, thm2) =
   let
      val (sfb, b1, e1) = dest_holfoot_implies_in_heap (concl thm1)
      val (thm, (_, b2, e2)) = 
           (holfoot_implies_in_heap___implies_unequal,
            dest_holfoot_implies_in_heap (concl thm2)) handle HOL_ERR _ =>
           (holfoot_implies_in_heap___or_null___implies_unequal,
            dest_holfoot_implies_in_heap_or_null (concl thm2))
      val already_known = 
          var_res_implies_unequal___check context sfb e1 e2;
      val _ = if already_known then Feedback.fail () else ();

      val sub_bag_thm = SUB_BAG_INSERT_SOLVE (bagSyntax.mk_sub_bag (
              bagSyntax.mk_union(b1, b2), sfb))

      val result0 = ISPECL [sfb, b1, b2, e1, e2] thm
      val result = MP result0 (LIST_CONJ [sub_bag_thm, thm1, thm2])
   in
      result
   end;

   fun mk_equal___in_heap_or_null___in_heap_or_null wpb rpb (thm1, thm2) =
   let
      val (sfb, b1, e1) = dest_holfoot_implies_in_heap_or_null (concl thm1)
      val (_,   b2, e2) = dest_holfoot_implies_in_heap_or_null (concl thm2)
      val _ = if (aconv e1 e2) then () else Feedback.fail ();

      val sub_bag_thm = SUB_BAG_INSERT_SOLVE (bagSyntax.mk_sub_bag (
              bagSyntax.mk_union(b1, b2), sfb))

      val result0 = ISPECL [wpb,rpb,sfb, b1, b2, e1] 
             holfoot_implies_in_heap_or_null___implies_equal
      val result1 = MP result0 (LIST_CONJ [sub_bag_thm, thm1, thm2])
      val result2 = var_res_precondition_prove result1
   in
      result2
   end;

   fun var_res_implies_unequal___normalise thm =
   let
       val (_, _, e1, e2) = dest_var_res_implies_unequal (concl thm)
       val do_turn = 
             ((is_var_res_exp_var e2 andalso not (is_var_res_exp_var e1)) orelse
              ((not ((not (is_var_res_exp_var e2)) andalso (is_var_res_exp_var e1)))
                 andalso (Term.compare (e2, e1) = LESS)))      
   in
       if do_turn then 
          CONV_RULE (PART_MATCH lhs var_res_implies_unequal_SYM) thm
       else
          thm
   end handle HOL_ERR _ => thm


   fun var_res_implies_unequal___remove_duplicates acc [] = acc
     | var_res_implies_unequal___remove_duplicates acc (thm::thmL) =
   let
       val (_, _, e1, e2) = dest_var_res_implies_unequal (concl thm)
       val thmL' = filter (fn thm => not (is_var_res_implies_unequal_sym e1 e2 (concl thm)))
                      thmL
   in         
      var_res_implies_unequal___remove_duplicates (thm::acc) thmL'
   end handle HOL_ERR _ => 
      var_res_implies_unequal___remove_duplicates (thm::acc) thmL


   fun var_res_implies_unequal___INTRO_PROP_IMPLIES wpb rpb thm =
   let
       val (f, sfb, e1, e2) = dest_var_res_implies_unequal (concl thm)
       val thm0 = ISPECL [f, e1, e2, wpb, rpb, sfb] var_res_implies_unequal___prop_implies
       val thm1 = MP thm0 thm
       val thm2 = var_res_precondition_prove thm1
   in
       thm2
   end;


in

(*
   val context = map ASSUME (fst (top_goal()))
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))

   val (f, _, wpbrpb, _, sfb_context, sfb_split, sfb_imp, _) = dest_VAR_RES_FRAME_SPLIT tt
   val (wpb,rpb) = pairSyntax.dest_pair wpbrpb
   val sfb = sfb_context
*)

fun holfoot___var_res_prop_implies___GENERATE tL ss context 
    (f, wpb, rpb, sfb) =
let
   val sfb_thm = bagLib.SIMPLE_BAG_NORMALISE_CONV sfb handle UNCHANGED => REFL sfb
   val sfb' = rhs (concl sfb_thm)
   val sfs = fst (dest_bag sfb');

   val implies_in_heapL =
      flatten (map (holfoot_implies_in_heap_GENERATE tL context sfb') sfs);
   val implies_in_heap_pairL = mk_in_heap_pair [] implies_in_heapL

   val res1_L1 = mapfilter (mk_unequal_null context) implies_in_heapL;
   val res1_L2 = mapfilter (mk_unequal___in_heap___in_heap context) implies_in_heap_pairL

   val res1L_0 = flatten [res1_L1, res1_L2]
   val res1L_1 = map var_res_implies_unequal___normalise res1L_0
   val res1L_2 = var_res_implies_unequal___remove_duplicates [] res1L_1
   val res1L = map (var_res_implies_unequal___INTRO_PROP_IMPLIES wpb rpb) res1L_2

   val res2L = mapfilter (mk_equal___in_heap_or_null___in_heap_or_null wpb rpb) implies_in_heap_pairL

   val res3L = holfoot_implies_GENERATE___data_array_interval ss context (wpb,rpb) sfb'
   val res = flatten [res1L, res2L, res3L]
   val res2 = map (CONV_RULE (RATOR_CONV (RAND_CONV (K (GSYM sfb_thm))))) res
in
   res2
end;

end



(******************************************************************************)
(* Get some points-to to front                                                *)
(******************************************************************************)


(*
val sfb1 = ``EMPTY_BAG:holfoot_a_proposition -> num`` 
val sfb2 = sfb
val context = map ASSUME (fst (top_goal()))
*)

fun points_to_intro___var_res_prop_implies_eq___list_seg ss context wpb rpb e sfb1 sfb2 sfb12_thm =
let
   val sfb12 = rhs (concl sfb12_thm)
   val sfs2 = fst (dest_bag sfb2)

   val found_opt = first_opt (fn n => fn ttt =>
     let
        val (_, e1, _, e2) = dest_holfoot_ap_data_list_seg ttt;
        val _ = if (aconv e1 e) then () else Feedback.fail();

        val unequal_thm = var_res_implies_unequal___prove context sfb12 e1 e2
     in
        SOME (n, ttt, unequal_thm)
     end) sfs2
   val _ = if isSome found_opt then () else Feedback.fail();

   val (pos, ls_t, implies_thm) = valOf found_opt

   (*sort it to front*)
   val sfb2_thm = BAG_RESORT_CONV [pos] sfb2;
   val sfb12_thm' = AP_TERM (mk_icomb (bagSyntax.BAG_UNION_tm, sfb1)) sfb2_thm

   val implies_thm' = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) 
       (K (GSYM (TRANS (GSYM sfb12_thm') sfb12_thm)))) implies_thm


   val (tl_t, _, data_t, e2) = dest_holfoot_ap_data_list_seg ls_t
   val (_, sfb2') = bagSyntax.dest_insert (rhs (concl sfb2_thm))   

   (*combine everything*)
   val thm0 = ISPECL [tl_t, e, e2, data_t, sfb1, sfb2', wpb,rpb] 
        holfoot_ap_data_list_seg___var_res_prop_implies_eq___split;
   val thm1 = MP thm0 implies_thm';
   val thm2 = var_res_precondition_prove thm1;
   val thm3 = CONV_RULE ((RATOR_CONV o RAND_CONV) 
          (K (GSYM sfb2_thm))) thm2
   val thm4 = CONV_RULE (RAND_CONV (VAR_RES_PROP_REWRITE_CONV ss context)) thm3

   (*give new constant a nice name*)
   val c_const_name = get_const_name_for_exp 
                          ("_"^(holfoot_term_to_string tl_t)) e
   val thm5 = CONV_RULE 
               ((RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) 
               (RENAME_VARS_CONV [c_const_name])) thm4
in
   thm5
end;

local
   val my_compset = listLib.list_compset ()
   val _ = computeLib.add_thms [asl_bigstar_list_REWRITE, 
      asl_star_holfoot_THM, LIST_TO_FMAP_THM, asl_trivial_cond_TF,
      pairTheory.SND, pairTheory.FST] my_compset
in
   val tree_prop_implies_eq_SIMP_CONV = computeLib.CBV_CONV my_compset
end


fun points_to_intro___var_res_prop_implies_eq___tree ss context wpb rpb e sfb1 sfb2 sfb12_thm =
let
   val sfb12 = rhs (concl sfb12_thm)
   val sfs2 = fst (dest_bag sfb2)

   val found_opt = first_opt (fn n => fn ttt =>
     let
        val (has_data, e1) = 
            (false, #2 (dest_holfoot_ap_tree ttt)) handle HOL_ERR _ =>
            (true,  #2 (dest_holfoot_ap_data_tree ttt))
        val _ = if (aconv e1 e) then () else Feedback.fail();

        val unequal_thm = var_res_implies_unequal___prove context sfb12 e1 holfoot_exp_null_term
     in
        SOME (n, ttt, unequal_thm, has_data)
     end) sfs2
   val _ = if isSome found_opt then () else Feedback.fail();

   val (pos, ls_t, implies_thm, has_data) = valOf found_opt

   (*sort it to front*)
   val sfb2_thm = BAG_RESORT_CONV [pos] sfb2;
   val sfb12_thm' = AP_TERM (mk_icomb (bagSyntax.BAG_UNION_tm, sfb1)) sfb2_thm

   val implies_thm' = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) 
       (K (GSYM (TRANS (GSYM sfb12_thm') sfb12_thm)))) implies_thm


   val (_, sfb2') = bagSyntax.dest_insert (rhs (concl sfb2_thm))   

   (*combine everything*)
   val thm0 = if has_data then
         let
            val (tagL_t, _, data') = dest_holfoot_ap_data_tree ls_t;
            val (dtagL, data) = pairSyntax.dest_pair data';
         in
            ISPECL [tagL_t, e, dtagL, data, sfb1, sfb2', wpb,rpb] 
               holfoot_ap_data_tree___var_res_prop_implies_eq___split
         end
       else
         let
            val (tagL_t, _) = dest_holfoot_ap_tree ls_t
         in
            ISPECL [tagL_t, e, sfb1, sfb2', wpb,rpb] 
               holfoot_ap_tree___var_res_prop_implies_eq___split
         end
   val thm1 = MP thm0 implies_thm';
   val thm2 = var_res_precondition_prove thm1;
   val thm3 = CONV_RULE ((RATOR_CONV o RAND_CONV) 
          (K (GSYM sfb2_thm))) thm2
   fun my_asl_exists_list_CONV b =  asl_exists_list_CONV (holfoot_term_to_string b) holfoot_term_to_string

   val exists_list_CONV = if not has_data then
         my_asl_exists_list_CONV e
      else let
         val (_, _, data') = dest_holfoot_ap_data_tree ls_t;
         val (_, data) = pairSyntax.dest_pair data';
      in
         QUANT_CONV (QUANT_CONV (my_asl_exists_list_CONV data)) THENC
         (QUANT_CONV (my_asl_exists_list_CONV e)) THENC
         (my_asl_exists_list_CONV e)
      end
   val thm4 = CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV
              (exists_list_CONV THENC
               tree_prop_implies_eq_SIMP_CONV)))) thm3
in
   thm4
end;


fun points_to_intro___var_res_prop_implies_eq___data_tree___NODE ss context wpb rpb e sfb1 sfb2 sfb12_thm =
let
   val sfb12 = rhs (concl sfb12_thm)
   val sfs2 = fst (dest_bag sfb2)
   val found_opt = first_opt (fn n => fn ttt =>
     let
        val (_,e1,tagL_data) = dest_holfoot_ap_data_tree ttt;
        val _ = if (aconv e1 e) then () else Feedback.fail();
        val (_, data_t) = pairSyntax.dest_pair tagL_data
        val _ = if (is_node data_t) then () else Feedback.fail();
     in
        SOME (n, ttt)
     end) sfs2
   val _ = if isSome found_opt then () else Feedback.fail();

   val (pos, ls_t) = valOf found_opt

   (*sort it to front*)
   val sfb2_thm = BAG_RESORT_CONV [pos] sfb2;
   val sfb12_thm' = AP_TERM (mk_icomb (bagSyntax.BAG_UNION_tm, sfb1)) sfb2_thm
   val (_, sfb2') = bagSyntax.dest_insert (rhs (concl sfb2_thm))   


   (*combine everything*)
   val (tagL_t, _, data') = dest_holfoot_ap_data_tree ls_t;
   val (dtagL, data) = pairSyntax.dest_pair data';
   val (v_t, tL_t) = dest_node data;
   val thm0 =  ISPECL [tagL_t, e, dtagL, v_t, tL_t, sfb1, sfb2', wpb,rpb] 
                  holfoot_ap_data_tree___var_res_prop_implies_eq___split___NODE
   val thm1 = var_res_precondition_prove thm0;
   val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV) 
          (K (GSYM sfb2_thm))) thm1
   fun my_asl_exists_list_CONV b = asl_exists_list_CONV (holfoot_term_to_string b) holfoot_term_to_string

   val exists_list_CONV =  my_asl_exists_list_CONV e
   val thm3 = CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV
              (exists_list_CONV THENC
               tree_prop_implies_eq_SIMP_CONV)))) thm2
in
   thm3
end;


fun points_to_intro___var_res_prop_implies_eq ss context wpb rpb e sfb1 sfb2 =
let
   val sfb12_thm = bagLib.SIMPLE_BAG_NORMALISE_CONV (bagSyntax.mk_union(sfb1, sfb2))
in
   tryfind (fn f => f ss context wpb rpb e sfb1 sfb2 sfb12_thm)
      [points_to_intro___var_res_prop_implies_eq___list_seg,
       points_to_intro___var_res_prop_implies_eq___data_tree___NODE,
       points_to_intro___var_res_prop_implies_eq___tree]
end


fun is_holfoot_ap_points_to___found_opt_pred e (n:int) ttt =
let
   val (e', L) = dest_holfoot_ap_points_to ttt;
in
   if (aconv e e') then SOME (n, L) else NONE
end;

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
   val context = map ASSUME (fst (top_goal()))
   val e = ``(var_res_exp_const t_const'):holfoot_a_expression``
*)
fun HOLFOOT_INFERENCE___points_to_intro ss context e tt =
let
   val (f,pre,prog,post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (_,wpb,rpb,sfb,sfs) = dest_var_res_prop___propL pre;
   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   (*here we abort if the points to is trivially present*)
   val _ = if isSome found_opt then raise UNCHANGED else ();

   (*generate the appropriate var_res_prop_implies_eq theorem*)
   val implies_eq_thm = points_to_intro___var_res_prop_implies_eq
         ss context wpb rpb e holfoot_empty_prop_bag_term sfb 
   val sfb' = rand (concl implies_eq_thm)

   val thm0 = ISPECL [f, wpb, rpb, sfb, sfb', prog, post]
                 VAR_RES_COND_INFERENCE___prop_implies_eq;
   val thm1 = MP thm0 implies_eq_thm
in
   thm1
end;



local
   open stringTheory stringLib
   val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
   val in_compset = listLib.list_compset ()
   val _ = computeLib.add_conv (ord_tm, 1, ORD_CHR_CONV) in_compset
   val _ = computeLib.add_thms char_eq_thms in_compset
   val _ = computeLib.add_thms [FDOM_FUPDATE, FDOM_FEMPTY,
            IN_INSERT, NOT_IN_EMPTY, holfoot_tag_11] in_compset


   fun search_fun_points_to e (n:int) ttt =
   let
      val (e', L) = dest_holfoot_ap_points_to ttt;
   in
      if (aconv e e') then SOME (n, NONE:thm option, ttt) else NONE
   end;

   fun search_fun_array_interval context ec (n:int) ttt =
       let
          val (is_interval, (e',n',_)) = dest_holfoot_ap_data_array_interval ttt
          val nc' = dest_var_res_exp_const n';
          val ec' = dest_var_res_exp_const e';
          val thm = prove_in_array_interval_bound is_interval context ec (ec',nc')
       in          
          SOME (n, SOME thm, ttt)
       end handle HOL_ERR _ => NONE;


   fun points_to___intro_const tag_t sf thm =
   let
      val (e_t, L_t) = dest_holfoot_ap_points_to sf;

      val in_thm_term = pred_setSyntax.mk_in (tag_t, finite_mapSyntax.mk_fdom L_t);
      val in_thm0 = computeLib.CBV_CONV in_compset in_thm_term;
      val (in_thm, need_intro) = 
           if aconv (rhs (concl in_thm0)) T then
             (EQT_ELIM in_thm0, false) else
           if aconv (rhs (concl in_thm0)) F then
             (EQF_ELIM in_thm0, true) else
           raise UNCHANGED

      val thm0 = if not need_intro then thm else
        let
           val xthm0 = PART_MATCH (lhs o snd o dest_imp o snd o dest_imp) 
                         (ISPEC tag_t HOLFOOT_COND_INFERENCE___points_to___ADD_TAG)
                        (rhs (concl thm))
           val xthm1 = MP xthm0 in_thm
           val xthm2 = var_res_precondition_prove xthm1;

           (*give new constant a nice name*)
           val c_const_name = get_const_name_for_exp 
                          ("_"^(holfoot_term_to_string tag_t)) e_t
           val xthm3 = CONV_RULE 
                   (RHS_CONV
                    (RENAME_VARS_CONV [c_const_name])) xthm2

           val xthm4 = TRANS thm xthm3
        in
           xthm4
        end;
   in
     (thm0, need_intro)
   end;


   fun array_interval___intro_const resort tag_t sf thm =
   let
      val (is_interval, (e1, e2, data)) = dest_holfoot_ap_data_array_interval sf;  
      val (dataL, data_ty) = listSyntax.dest_list data;
      val data_pL = map pairSyntax.dest_pair dataL;
      val data_opt = SOME (assoc tag_t data_pL) handle HOL_ERR _ => NONE;
      val need_intro = not (isSome data_opt);

      val (thm0,data) = if need_intro then 
        let
           val rewr_thm0 = SPEC tag_t (if is_interval then
                          holfoot_ap_data_interval___ADD_TAG
                          else holfoot_ap_data_array___ADD_TAG)
           val rewr_thm1 = PART_MATCH (lhs o snd o dest_imp) rewr_thm0 sf;
           val rewr_thm = var_res_precondition_prove rewr_thm1;

           val xthm0 = CONV_RULE ((RHS_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o
                                   RAND_CONV o RATOR_CONV o RAND_CONV) (K rewr_thm)) thm;            

           val xthm1 = HO_PART_MATCH (lhs o snd o dest_imp) 
                        VAR_RES_COND_INFERENCE___asl_exists_pre
                        (rhs (concl xthm0));
           val xthm2 = var_res_precondition_prove xthm1;
           val xthm3 = TRANS xthm0 xthm2;

           (*give new constant a nice name*)
           val c_const_name = get_const_name_for_exp 
                          ("_"^(holfoot_term_to_string tag_t)) 
                          (mk_var ("data", holfoot_a_expression_ty));
           val xthm4 = CONV_RULE (RHS_CONV
                    (RENAME_VARS_CONV [c_const_name])) xthm3
           val (data, _) = dest_forall (rhs (concl xthm4))
        in
           (xthm4,data)
        end
     else if (not resort) then (thm, valOf data_opt) else
        let
        (*resort data_entry*)
        val (dataL2_h, dataL2) = trypluck (fn dt => let val (tag, dl) = pairSyntax.dest_pair dt in
                      if (aconv tag tag_t) then dt else Feedback.fail() end) dataL;
        val data' = listSyntax.mk_list (dataL2_h::dataL2, data_ty)
        val data_perm_thm = EQT_ELIM (permLib.PERM_NORMALISE_CONV (list_mk_icomb (permLib.PERM_tm, [data, data'])))
        val perm_thm = if is_interval then holfoot_ap_data_interval___DATA_PERM else holfoot_ap_data_array___DATA_PERM;
        val sf_thm = MATCH_MP (PART_MATCH (lhs o snd o dest_imp) perm_thm sf) data_perm_thm
        val xthm0 = CONV_RULE ((RHS_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o
                                RAND_CONV o RATOR_CONV o RAND_CONV) (K sf_thm)) thm;            
     in
        (xthm0, valOf data_opt)        
     end
   in
     (thm0, need_intro,SOME data)
   end;
in

fun HOLFOOT_INFERENCE___bring_points_to_to_front resort context e tag_t tt =
let
   val (_,pre,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE tt;   
   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre
   val found_opt = first_opt (search_fun_points_to e) sfs
   val found_opt = if (isSome found_opt) then found_opt else 
                   (first_opt (search_fun_array_interval context 
                       (dest_var_res_exp_const e)) sfs handle HOL_ERR _ => NONE)
   val _ = if isSome found_opt then () else raise UNCHANGED;               

   (*resort points to to front and insert tag if necessary*)
   val (pos,in_bound_thm_opt, sf) = valOf found_opt;

   val thm0 = VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [pos] tt
in
   if (is_holfoot_ap_points_to sf) then
      let
         val (thm, need_intro) = points_to___intro_const tag_t sf thm0;
      in
         ((thm, need_intro, NONE), (sf, NONE))
      end 
   else (array_interval___intro_const resort tag_t sf thm0, (sf, in_bound_thm_opt))
end;

end;

(******************************************************************************)
(* Inference for field lookup                                                 *)
(******************************************************************************)

(*
   REPEAT STRIP_TAC
   val context = map ASSUME (fst (top_goal ()))
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun HOLFOOT_INFERENCE___field_lookup___const_intro___CONV tt =
let
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (v, e, tag_t) = dest_holfoot_prog_field_lookup p1
   val _ = if is_var_res_exp_const e then raise UNCHANGED else ();

   val (intro, _, thm0) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e NONE tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   val thm1 = PART_MATCH (lhs o snd o dest_imp)
       HOLFOOT_COND_INFERENCE___prog_field_lookup___exp_rewrite body_t
   val thm2 = var_res_precondition_prove thm1
   val thm3 = CONV_RULE ((RHS_CONV o body_conv) (K thm2)) thm0
in
   thm3
end;


fun HOLFOOT_INFERENCE___field_lookup___points_to_intro___CONV ss context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, e, tag_t) = dest_holfoot_prog_field_lookup p1

   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre

   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   val _ = if isSome found_opt then Feedback.fail() else ()
in
    HOLFOOT_INFERENCE___points_to_intro ss context e tt   
end;


local
   open stringTheory stringLib
   val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
   val apply_compset = listLib.list_compset ()
   val _ = computeLib.add_conv (ord_tm, 1, ORD_CHR_CONV) apply_compset
   val _ = computeLib.add_thms char_eq_thms apply_compset
   val _ = computeLib.add_thms [FAPPLY_FUPDATE_THM, holfoot_tag_11] apply_compset
in

fun HOLFOOT_INFERENCE___field_lookup___main___CONSEQ_CONV context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (v, e, tag_t) = dest_holfoot_prog_field_lookup p1

   val ((thm0, intro, data_opt), (sf, bound_thm_opt)) =
      HOLFOOT_INFERENCE___bring_points_to_to_front false context e tag_t tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   (*introduce constant for variable*)
   val (intro2, c_t, thm1a) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV 
        (mk_var_res_exp_var v (type_of e)) NONE body_t

   val thm1 = CONV_RULE (RHS_CONV (body_conv (K thm1a))) thm0

   val body_t = if intro2 then 
        (snd o dest_forall o rhs o concl) thm1a else
        ((rhs o concl) thm1a)
   val varL = (fst o strip_forall o rhs o concl) thm1
    
   (*instantiate main theorem*)
   val is_points_to = is_holfoot_ap_points_to sf;
   val inf_thm = if is_points_to then
                    HOLFOOT_COND_INFERENCE___prog_field_lookup
                 else SPEC (valOf data_opt)
                    (if (is_holfoot_ap_data_array sf) then
                       HOLFOOT_COND_INFERENCE___prog_field_lookup___array
                    else
                       HOLFOOT_COND_INFERENCE___prog_field_lookup___interval)

   val thm2a = PART_MATCH ((if is_points_to then I else (snd o dest_imp)) o snd o dest_imp o snd o dest_imp) inf_thm body_t
   val thm2b = var_res_precondition_prove (if is_points_to then thm2a else (MP thm2a (valOf bound_thm_opt)))

   val thm2c = CONV_RULE ((RATOR_CONV o RAND_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o
                           RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV) 
                           (computeLib.CBV_CONV apply_compset)) thm2b

   val vc = pairSyntax.mk_pair (v, c_t);
   val vcL_t = listSyntax.mk_list ([vc], type_of vc);
   val thm2d = CONV_RULE ((RATOR_CONV o RAND_CONV)
         (VAR_RES_COND_INFERENCE___PRECOND_var_res_prop_varlist_update___EVAL vcL_t))
         thm2c

   val thm2e = LIST_GEN_IMP varL thm2d
   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm1))) thm2e
in
   thm2
end;

end;

fun HOLFOOT_INFERENCE___field_lookup___CONV tt =
let
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, p1') = dest_fasl_comment_location p1;
   val _ = dest_holfoot_prog_field_lookup p1'
in
   VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt
end


(******************************************************************************)
(* Inference for field assign                                                 *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun HOLFOOT_INFERENCE___field_assign___const_intro___CONV tt =
let
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (e1, tag_t, e2) = dest_holfoot_prog_field_assign p1

   val turn = if not (is_var_res_exp_const e1) then false else
              if not (is_var_res_exp_const e2) then true else raise UNCHANGED;
   val (e,inf_thm) = if turn then 
      (e2, HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite___value) else 
      (e1, HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite);

   val (intro, _, thm0) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e NONE tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   val thm1 = PART_MATCH (lhs o snd o dest_imp) inf_thm body_t
   val thm2 = var_res_precondition_prove thm1
   val thm3 = CONV_RULE ((RHS_CONV o body_conv) (K thm2)) thm0
in
   thm3
end;


fun HOLFOOT_INFERENCE___field_assign___points_to_intro___CONV ss context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (e, tag_t, _) = dest_holfoot_prog_field_assign p1

   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre

   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   val _ = if isSome found_opt then Feedback.fail() else ()
in
    HOLFOOT_INFERENCE___points_to_intro ss context e tt   
end;


(*
   REPEAT STRIP_TAC
   val context = map ASSUME (fst (top_goal ()))
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)

fun HOLFOOT_INFERENCE___field_assign___main___CONSEQ_CONV context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (e1, tag_t, e2) = dest_holfoot_prog_field_assign p1

   val ((thm0, intro, data_opt), (sf, bound_thm_opt)) =
      HOLFOOT_INFERENCE___bring_points_to_to_front true context e1 tag_t tt;

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   (*instantiate main theorem*)
   val is_points_to = is_holfoot_ap_points_to sf;
   val inf_thm = if is_points_to then
                    HOLFOOT_COND_INFERENCE___prog_field_assign
                 else 
                    (if (is_holfoot_ap_data_array sf) then
                       HOLFOOT_COND_INFERENCE___prog_field_assign___array
                    else
                       HOLFOOT_COND_INFERENCE___prog_field_assign___interval);
                    

   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp) inf_thm body_t
   val thm1b = if is_points_to then 
                 (CONV_RULE ((RATOR_CONV o RAND_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o
                              RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)
                              finite_mapLib.fupdate_NORMALISE_CONV) (var_res_precondition_prove thm1a)) else
                 (MP thm1a (valOf bound_thm_opt));
 

   val thm1 = if intro then
      GEN_IMP ((fst o dest_forall o rhs o concl) thm0) thm1b else thm1b


   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1
in
   thm2
end;



fun HOLFOOT_INFERENCE___field_assign___CONV tt =
let
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, p1') = dest_fasl_comment_location p1;
   val _ = dest_holfoot_prog_field_assign p1'
in
   VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt
end;


(******************************************************************************)
(* Inference for dispose                                                      *)
(******************************************************************************)

(*
set_trace "use holfoot_pp" 0
use_holfoot_pp := false
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun HOLFOOT_INFERENCE___dispose___const_intro___CONV tt =
let
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (ne, e1) = dest_holfoot_prog_dispose p1;

   (*which constant do we want to insert? *)
   val (e, inf_thm) = 
       if not (is_var_res_exp_const e1) then 
          (e1, HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite) else
       if not (is_var_res_exp_const ne) then
          (ne, HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite___count) else
       raise UNCHANGED;

   val (intro, _, thm0) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e NONE tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   val thm1 = PART_MATCH (lhs o snd o dest_imp) inf_thm body_t
   val thm2 = var_res_precondition_prove thm1
   val thm3 = CONV_RULE ((RHS_CONV o body_conv) (K thm2)) thm0
in
   thm3
end;

fun HOLFOOT_INFERENCE___dispose___points_to_intro___CONV ss context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (ne, e) = dest_holfoot_prog_dispose p1
   val _ = if (is_holfoot_exp_one ne) then () else raise UNCHANGED;

   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre

   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   val _ = if isSome found_opt then Feedback.fail() else ()
in
    HOLFOOT_INFERENCE___points_to_intro ss context e tt   
end;


fun is_holfoot_ap_data_array___found_opt_pred e ne (n:int) ttt =
let
   val (e', ne', d) = dest_holfoot_ap_data_array ttt;
in
   if (aconv e e') andalso (aconv ne ne') then SOME (n, d) else NONE
end;


fun HOLFOOT_INFERENCE___dispose___FRAME___CONSEQ_CONV tt =
let
   val (p1,prog,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, _) = dest_holfoot_prog_dispose p1
   val (c, _, prog_fun) = save_dest_list_fasl_comment_location prog

   (*apply inference*)
   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
      HOLFOOT_COND_INFERENCE___prog_dispose___FRAME tt
   val thm1 = var_res_precondition_prove thm1a 


   val new_c1 = fasl_comment_modify_APPEND_DEC ("abstracted dispose") c
   val thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o
                          RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                  ((fasl_comment_location2_INTRO_CONV new_c1) THENC
                   (fasl_comment_abstraction_INTRO_CONV "dispose"))) thm1
in
   thm2
end;


exception holfoot_too_complicated_expn;

fun HOLFOOT_INFERENCE___dispose___main___CONSEQ_CONV tt =
let
   (*destruct and search for points-to / array*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (ne, e1) = dest_holfoot_prog_dispose p1
   val (search_pred, inf_thm) = if (is_holfoot_exp_one ne) then 
      (is_holfoot_ap_points_to___found_opt_pred e1,
       HOLFOOT_COND_INFERENCE___prog_dispose_1) else
      (is_holfoot_ap_data_array___found_opt_pred e1 ne,
       HOLFOOT_COND_INFERENCE___prog_dispose);

   (*resort points-to/array to front*)
   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre
   val found_opt = first_opt search_pred sfs
   val _ = if isSome found_opt then () else 
      (if is_var_res_exp_const ne andalso is_var_res_exp_const e1 then
         raise holfoot_too_complicated_expn else raise UNCHANGED);               

   val (pos,_) = valOf found_opt;
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [pos] tt

   (*instantiate main theorem*)
   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
      inf_thm (rhs (concl thm0))
   val thm1 = var_res_precondition_prove thm1a 
 
   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1
in
   thm2
end handle holfoot_too_complicated_expn =>
   HOLFOOT_INFERENCE___dispose___FRAME___CONSEQ_CONV tt


fun HOLFOOT_INFERENCE___dispose___CONV tt =
let
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, p1') = dest_fasl_comment_location p1;
   val _ = dest_holfoot_prog_dispose p1'
in
   VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt
end


(******************************************************************************)
(* Inference for new                                                          *)
(******************************************************************************)
(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun HOLFOOT_INFERENCE___prog_new___CONSEQ_CONV tt =
let
   val (p1,_,_,pre,_,thm0_fun) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt;
   val (ne, v, tagL) = dest_holfoot_prog_new p1;
   val ve = mk_var_res_exp_var v (Type `:holfoot_a_expression`)

   (* intro var *)
   val thm0a = thm0_fun ()
   val (intro, c, thm0b) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV  ve NONE (rhs (concl thm0a));
   val thm0 = TRANS thm0a thm0b
   val t' = let val ttt = rhs (concl thm0) in
               if intro then (snd (dest_forall ttt)) else ttt end


   val inf_thm = if (is_holfoot_exp_one ne) then
                 HOLFOOT_COND_INFERENCE___prog_new_1 else
                 HOLFOOT_COND_INFERENCE___prog_new;
   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
                 inf_thm t'
   val thm1b = var_res_precondition_prove thm1a;
   val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV o
      VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o RAND_CONV)
      ((DEPTH_CONV BAG_IMAGE_CONV) THENC
        BAG_NORMALISE_CONV)) thm1b


   (* simplifying new precond *)
   val pre = (rand o rator o rator o fst o dest_imp o concl) thm1

   val vc = pairSyntax.mk_pair (v, c);
   val vcL_t = listSyntax.mk_list ([vc], type_of vc);
   val pre_imp_thm = var_res_prop___var_res_prop_varlist_update___EVAL vcL_t pre


   val rw_thm = MATCH_MP VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_EQUIV pre_imp_thm
   val thm2 = ANTE_CONV_RULE (REWR_CONV rw_thm) thm1

   (* add new variable if necessary *)
   val thm3 = if intro then GEN_IMP c thm2 else thm2

   (* recombine *)
   val thm4 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm3

   (*eliminate new const, if not used*)
   val thm5 = ANTE_CONV_RULE (REWR_CONV FORALL_SIMP) thm4 handle 
                  UNCHANGED => thm4
                | HOL_ERR _ => thm4


   (*intro needed data*)
   val add_tag_thm = if (is_holfoot_exp_one ne) then
       holfoot_ap_points_to___ADD_TAG
       else holfoot_ap_data_array___ADD_TAG

   fun intro_conv tag_t tt =
      let
         val xthm0 = SPEC tag_t add_tag_thm
         val xthm1 = PART_MATCH (lhs o snd o dest_imp) xthm0 tt;         
      in
         var_res_precondition_prove xthm1
      end;

   fun intro_all_conv [] = ALL_CONV
     | intro_all_conv (tag_t::tagL) =
       (intro_conv tag_t) THENC
       QUANT_CONV (intro_all_conv tagL)

   val (tagL_list, _) = listSyntax.dest_list tagL
   val thm6 = ANTE_CONV_RULE ((STRIP_QUANT_CONV o 
      VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o RAND_CONV o
      RATOR_CONV o RAND_CONV) (intro_all_conv tagL_list)) thm5

in
   thm6
end;


(******************************************************************************)
(* FRAME_SPLIT                                                                *)
(******************************************************************************)


(* ---------------------------------------- *)
(* data_list_seg - points to - points to    *)
(* ---------------------------------------- *)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (e1,_) = dest_holfoot_ap_points_to ttt
          fun search_fun2 m tttt =
          let
             val (e1', _) = dest_holfoot_ap_points_to tttt
          in
             if (aconv e1 e1') then
                SOME m
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
             SOME (n, valOf found_opt)
       end

   open stringTheory stringLib

   val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
   val my_compset = listLib.list_compset ()
   val _ = computeLib.add_conv (ord_tm, 1, ORD_CHR_CONV) my_compset
   val _ = computeLib.add_thms char_eq_thms my_compset
   val _ = computeLib.add_thms [FAPPLY_FUPDATE_THM, holfoot_tag_11,
      asl_bigstar_list_REWRITE, var_res_prop_equal_unequal_REWRITES,
      asl_star_holfoot_THM] my_compset
in

fun VAR_RES_FRAME_SPLIT_INFERENCE___points_to_points_to___CONV tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, m) = valOf found_opt;

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt

   fun my_strip_fupdate tt = if finite_mapSyntax.is_fempty tt then [] else
   let
      val (rest, fmL) = finite_mapSyntax.strip_fupdate tt;
      val _ = if finite_mapSyntax.is_fempty rest then () else raise UNCHANGED
   in
      fmL
   end;

   val fm_splitL = 
       my_strip_fupdate (snd (
          dest_holfoot_ap_points_to (el (n+1) split_sfs)))
   val fm_impL = 
       my_strip_fupdate (snd (
          dest_holfoot_ap_points_to (el (m+1) imp_sfs)))

   val fm_splitpL = map pairSyntax.dest_pair fm_splitL
   val fm_imppL = map pairSyntax.dest_pair fm_impL

   val l' = map fst (filter (fn (tag_t, e_t) =>
        let
            val (_, e_t') = first (fn (tag_t', _) => aconv tag_t tag_t') fm_splitpL
        in          
            not (aconv e_t e_t')
        end handle HOL_ERR _ => true) fm_imppL)
   val l'_t = listSyntax.mk_list (l', Type `:holfoot_tag`)

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
      (SPEC l'_t VAR_RES_FRAME_SPLIT___points_to___points_to___SUBMAP)
      (rhs (concl thm0))

   val thm2 = var_res_precondition_prove thm1;

   (*undo resorting*)
   val thm3 = TRANS thm0 thm2


   (*simplify*)
   val conv = computeLib.CBV_CONV my_compset
   val thm4 = CONV_RULE ((RHS_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) conv) thm3
in
   thm4
end;

end;




(* ---------------------------------------- *)
(* data_list_seg - points to                *)
(* ---------------------------------------- *)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (e1,_) = dest_holfoot_ap_points_to ttt
          fun search_fun2 m tttt =
          let
             val (_, e1', _, e2') = dest_holfoot_ap_data_list_seg tttt
          in
             if (aconv e1 e1') then
                SOME m
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
             SOME (n, valOf found_opt)
       end

  val simplify_cs = computeLib.bool_compset ();
  val _ = computeLib.add_thms [listTheory.MAP, pairTheory.FST,
                               pairTheory.SND, listTheory.MEM,
                               BAG_UNION_INSERT, BAG_UNION_EMPTY,
                               FAPPLY_FUPDATE_THM,
                               containerTheory.LIST_TO_BAG_def,
                               EVERY_DEF, holfoot_tag_11,
                               holfoot_var_11,
                               ALL_DISTINCT] simplify_cs;


  val _ = computeLib.add_conv (Term `($=):'a -> 'a -> bool`, 2, stringLib.string_EQ_CONV) simplify_cs;

in

fun VAR_RES_FRAME_SPLIT_INFERENCE___points_to_list_seg___CONV context tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, m) = valOf found_opt;

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp o snd o dest_imp)
      VAR_RES_FRAME_SPLIT___points_to___data_list_seg
      (rhs (concl thm0))

   val precond = (fst o dest_imp o concl) thm1
   val precond_thm = var_res_implies_unequal___prove___term context precond
   val thm2 = MP thm1 precond_thm 
   val thm3 = var_res_precondition_prove thm2

   (*undo resorting*)
   val thm4 = TRANS thm0 thm3


   (*simplify*)
   val my_conv = computeLib.CBV_CONV simplify_cs
   val thm5 =  CONV_RULE (RHS_CONV (VAR_RES_FRAME_SPLIT___imp_CONV my_conv)) thm4
in
   thm5
end;

end;



(* ---------------------------------------- *)
(* data_list_seg - same start and end       *)
(* ---------------------------------------- *)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (_, e1, _, e2) = dest_holfoot_ap_data_list_seg ttt
          fun search_fun2 m tttt =
          let
             val (_, e1', _, e2') = dest_holfoot_ap_data_list_seg tttt
          in
             if (aconv e1 e1') andalso (aconv e2 e2') then
                SOME (m, tttt)
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
          let
             val (m, tttt) = valOf found_opt;
          in
             SOME (n, ttt, m, tttt)
          end           
       end

in

fun VAR_RES_FRAME_SPLIT_INFERENCE___list_seg_same_start_end___CONV tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, sf1, m, sfb2) = valOf found_opt;

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt


   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
      VAR_RES_FRAME_SPLIT___data_list_seg___SAME_START_END___REMOVE
      (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1

   (*undo resorting*)
   val thm3 = TRANS thm0 thm2
in
   thm3
end;

end;


(* ---------------------------------------- *)
(* data_list_seg - same start               *)
(* ---------------------------------------- *)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun (context_sfb, split_sfs, context) sfs n ttt =
       let
          val (_, e1, _, _) = dest_holfoot_ap_data_list_seg ttt
          fun search_fun2 m tttt =
          let
             val (_, e1', _, e2') = dest_holfoot_ap_data_list_seg tttt
          in
             if (aconv e1 e1') then
                SOME (m, e2', tttt)
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
          let
             val (m, e2', tttt) = valOf found_opt;

             val split_sfb' = let
                val (l1, l2) = Lib.split_after n split_sfs;
                val l3 = append l1 (tl l2);
             in
                bagSyntax.mk_bag (l3, type_of (hd split_sfs))
             end;
             val bag_t = bagSyntax.mk_union (split_sfb', context_sfb)
             val thm = holfoot_implies_in_heap_or_null___prove context  bag_t e2'
          in
             SOME (n, ttt, m, tttt, thm)
          end handle HOL_ERR _ => NONE
       end
in

fun VAR_RES_FRAME_SPLIT_INFERENCE___list_seg_same_start___CONV context tt =
let
   val (f, _, wpbrpb, _, context_sfb, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;
   val (wpb,rpb) = pairSyntax.dest_pair wpbrpb

   (*search lists*)
   val found_opt = first_opt (search_fun (context_sfb, split_sfs, context) imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, sf1, m, sfb2, imp_thm) = valOf found_opt;

   (*resort*)
   val split_thm = BAG_RESORT_CONV [n] split_sfb
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (K split_thm) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp o snd o dest_imp)
      VAR_RES_FRAME_SPLIT___data_list_seg___REMOVE_START
      (rhs (concl thm0))
   val thm2 = MP thm1 imp_thm
   val thm3 = var_res_precondition_prove thm2

   (*undo resorting*)
   val thm4 = TRANS thm0 thm3
in
   thm4
end;


end;


(* ---------------------------------------- *)
(* tree - points to                         *)
(* ---------------------------------------- *)

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (e1,_) = dest_holfoot_ap_points_to ttt
          fun search_fun2 m tttt =
          let
             val (has_data, e1') = 
                (false, #2 (dest_holfoot_ap_tree tttt)) handle HOL_ERR _ =>
                (true,  #2 (dest_holfoot_ap_data_tree tttt))
          in
             if (aconv e1 e1') then
                SOME (m, has_data, tttt)
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
             let
                val (m, has_data, t) = valOf found_opt
             in
                SOME (e1, t, has_data, n, m)
             end
       end

  val simplify_cs = computeLib.bool_compset ();
  val _ = computeLib.add_thms [listTheory.MAP, pairTheory.FST,
                    pairTheory.SND, FAPPLY_FUPDATE_THM,
                    holfoot_tag_11,asl_bigstar_list_REWRITE, 
                    asl_star_holfoot_THM, ZIP,
                    holfoot_var_11, APPEND,
                    var_res_prop_equal_unequal_REWRITES,
                    asl_star_holfoot_THM, tree_11, tree_distinct,
                    GSYM tree_distinct, 
                    var_res_exp_is_defined___const,
                    listTheory.LENGTH, asl_trivial_cond_TF] simplify_cs;
  val _ = computeLib.add_conv (Term `($=):'a -> 'a -> bool`, 2, stringLib.string_EQ_CONV) simplify_cs;

in

fun VAR_RES_FRAME_SPLIT_INFERENCE___points_to_tree___CONV tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (e1, ttt, has_data, n, m) = valOf found_opt;

   val has_data_node = has_data andalso
      is_node ((snd o pairSyntax.dest_pair o #3 o dest_holfoot_ap_data_tree) ttt)

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt

   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
      (if has_data then 
          (if has_data_node then
             VAR_RES_FRAME_SPLIT___points_to___data_tree___NODE
          else VAR_RES_FRAME_SPLIT___points_to___data_tree)
       else VAR_RES_FRAME_SPLIT___points_to___tree)
      (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1

   (*undo resorting*)
   val thm3 = TRANS thm0 thm2


   (*simplify*)
   fun my_asl_exists_list_CONV b =  asl_exists_list_CONV (holfoot_term_to_string b) holfoot_term_to_string
   val exists_list_CONV = if not has_data orelse has_data_node then
         my_asl_exists_list_CONV e1
      else let
         val (_, _, data') = dest_holfoot_ap_data_tree ttt;
         val (_, data) = pairSyntax.dest_pair data';
      in
         QUANT_CONV (QUANT_CONV (my_asl_exists_list_CONV data)) THENC
         QUANT_CONV (my_asl_exists_list_CONV e1) THENC
         my_asl_exists_list_CONV e1
      end;

   val my_conv = exists_list_CONV THENC (computeLib.CBV_CONV simplify_cs)
   val thm4 =  CONV_RULE (RHS_CONV (RATOR_CONV (RAND_CONV (
                  VAR_RES_FRAME_SPLIT___imp_CONV my_conv)))) thm3
in
   thm4
end;

end;

(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (tagL,e1,data) = dest_holfoot_ap_data_tree ttt
          val (dtagL, _) = pairSyntax.dest_pair data;

          fun search_fun2 m tttt =
          let
             val (tagL',e1',data) = dest_holfoot_ap_data_tree tttt
             val (dtagL', _) = pairSyntax.dest_pair data;
          in
             if (aconv e1 e1') andalso (aconv tagL tagL') andalso
                (aconv dtagL dtagL') then
                SOME m
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
             SOME (n, valOf found_opt)
       end
in

fun VAR_RES_FRAME_SPLIT_INFERENCE___data_tree_frame___CONV tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, m) = valOf found_opt;

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt


   (*apply inference*)
   val thm1 = PART_MATCH (lhs o snd o dest_imp)
      VAR_RES_FRAME_SPLIT___data_tree___SAME_EXP___REMOVE
      (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1

   (*undo resorting*)
   val thm3 = TRANS thm0 thm2
in
   thm3
end;

end;




(* ---------------------------------------- *)
(* array / interval - same start and length *)
(* ---------------------------------------- *)

(*
   val context = []
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun sfs n ttt =
       let
          val (af, (e, ne, _)) = dest_holfoot_ap_data_array_interval ttt;
          fun search_fun2 m tttt =
          let
             val (af', (e', ne', _)) = dest_holfoot_ap_data_array_interval tttt
          in
             if (af' = af) andalso (aconv e e') andalso (aconv ne ne') then
                SOME (m, tttt)
             else NONE
          end;
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
          let
             val (m, tttt) = valOf found_opt;
          in
             SOME (n, ttt, m, tttt, not af)
          end           
       end

in

fun VAR_RES_FRAME_SPLIT_INFERENCE___data_array___same_start_length___CONV tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, sf1, m, sfb2, af) = valOf found_opt;

   (*resort*)
   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m])) tt


   (*apply inference*)
   val inf_thm = if af then 
                    VAR_RES_FRAME_SPLIT___data_array___data_array___SAME_EXP_LENGTH
                 else 
                    VAR_RES_FRAME_SPLIT___data_interval___data_interval___SAME_EXP_LENGTH		
   val thm1 = PART_MATCH (lhs o snd o dest_imp) inf_thm (rhs (concl thm0))
   val thm2 = var_res_precondition_prove thm1

   (*undo resorting*)
   val thm3 = TRANS thm0 thm2
in
   thm3
end;

end;



(* ---------------------------------------- *)
(* array / interval - split if necessary    *)
(* ---------------------------------------- *)

(*
   REPEAT STRIP_TAC
   val context = map ASSUME (fst (top_goal()))
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   val array_compset = computeLib.bool_compset ()
   val _ = computeLib.add_thms [pairTheory.SND, pairTheory.FST, MAP] array_compset

   fun try_split context i1 i2 (ec1,nc1) (ec2,nc2,data2) =
   let
       val (guard_opt, inf_thm) = 
          if (ec1 = ec2) then (
             if i2 then 
                (if i1 then (SOME (mk_eq (nc1, nc2)), ISPECL [ec2, nc2, nc1]
                            holfoot_ap_data_array_interval___same_start___SPLIT___ii) else
                            (NONE, ISPECL [ec2, nc2, nc1]
                            holfoot_ap_data_array_interval___same_start___SPLIT___ia))
             else
                (if i1 then (NONE, ISPECL [ec2, nc2, nc1]
                            holfoot_ap_data_array_interval___same_start___SPLIT___ai) else
                            (SOME (mk_disj (mk_eq (nc1, nc2), mk_eq (nc1, numSyntax.zero_tm))), ISPECL [ec2, nc2, nc1]
                            holfoot_ap_data_array_interval___same_start___SPLIT___aa))            
          ) else (
             if i2 then (SOME (mk_disj (numSyntax.mk_less (nc2, ec1), mk_eq (ec2, ec1))), 
                ISPECL [ec2, nc2, ec1]
                holfoot_ap_data_interval___SPLIT___intro_same_start)
             else
                (SOME (mk_eq (ec1, numSyntax.mk_plus (ec2, nc2))), ISPECL [ec2, nc2, ec1] 
                  holfoot_ap_data_array___SPLIT___intro_same_start)
          );
       val pre = (fst o dest_imp o snd o strip_forall) (concl inf_thm);
       val pre_thm = array_bound_DECIDE context pre
       val guard_ok = if not (isSome guard_opt) then true else
                      not (can (array_bound_DECIDE context) (valOf guard_opt));
       val _ = if guard_ok then () else Feedback.fail ();

       val xthm1 = MATCH_MP inf_thm pre_thm;
       val xthm2 = CONV_RULE ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV)
             (holfoot_arith_simp_CONV context)) xthm1
       val xthm3 = CONV_RULE (REPEATC Unwind.UNWIND_FORALL_CONV) xthm2
       val xthm4 = SPEC data2 xthm3
       val xthm5 = CONV_RULE (RHS_CONV (computeLib.CBV_CONV array_compset)) xthm4
   in
      xthm5
   end;

   fun try_prove_eq_start ss context ec1 ec2 ttt = 
   let
      val _ = if (ec1 = ec2) then Feedback.fail() else ();
      val eq_t = mk_eq (ec1, ec2);
      val eq_thm = array_bound_DECIDE context eq_t;
      val xthm0 = ISPECL [eq_t, ttt] asl_trivial_cond___INTRO;
      val xthm1 = MP xthm0 eq_thm
      val xthm2 = CONV_RULE ((RHS_CONV o RAND_CONV o RATOR_CONV o RATOR_CONV o
             RAND_CONV o RAND_CONV) (K eq_thm)) xthm1
      val xthm3 = CONV_RULE (VAR_RES_PROP_REWRITE_CONV ss context) xthm2
   in
      xthm3
   end;

   fun try_prove_eq_end ss context i1 i2 ec1 ec2 nc1 nc2 ttt = 
   let
      val _ = if (i1 = i2) andalso (ec1 = ec2) andalso not (nc1 = nc2) then () else Feedback.fail();
      val eq_t = mk_eq (nc1, nc2);
      val eq_thm = array_bound_DECIDE context eq_t;
      val xthm0 = ISPECL [eq_t, ttt] asl_trivial_cond___INTRO;
      val xthm1 = MP xthm0 eq_thm
      val xthm2 = CONV_RULE ((RHS_CONV o RAND_CONV o RATOR_CONV o
             RAND_CONV o RAND_CONV) (K eq_thm)) xthm1
      val xthm3 = CONV_RULE (VAR_RES_PROP_REWRITE_CONV ss context) xthm2
   in
      xthm3
   end;

   fun search_fun ss context sfs n ttt =
       let
          val (i1, (e, ne, data1)) = dest_holfoot_ap_data_array_interval ttt;          
          val nc1 = dest_var_res_exp_const ne
          val ec1 = dest_var_res_exp_const e
          fun search_fun2 m tttt =
          let
             val (i2, (e', ne', data2)) = dest_holfoot_ap_data_array_interval tttt
             val ec2 = dest_var_res_exp_const e'
             val nc2 = dest_var_res_exp_const ne'
             val (in_split, split_thm) = 
                 (true,  try_prove_eq_start ss context ec1 ec2 ttt) handle HOL_ERR _ =>
                 (true,  try_prove_eq_end ss context i1 i2 ec1 ec2 nc1 nc2 ttt) handle HOL_ERR _ =>
                 (false, try_split context i1 i2 (ec1,nc1) (ec2, nc2, data2)) handle HOL_ERR _ =>
                 (true,  try_split context i2 i1 (ec2,nc2) (ec1, nc1, data1))
          in
             SOME (m, tttt, in_split, split_thm)
          end
          val found_opt = if (is_var_res_exp_const ne) then 
              first_opt search_fun2 sfs else NONE
       in
          if not (isSome found_opt) then NONE else
          let
             val (m, tttt, in_split, split_thm) = valOf found_opt;
          in
             SOME (n, m, ttt, tttt, in_split, split_thm)
          end           
       end handle HOL_ERR _ => NONE;

in

fun VAR_RES_FRAME_SPLIT_INFERENCE___data_array_interval___SPLIT___CONV ss context tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun ss context imp_sfs) split_sfs;
   val _ = if isSome found_opt then () else raise UNCHANGED;
   val (n, m, sf1, sf2, in_split, split_thm) = valOf found_opt;


   (*resort and apply*)
   val array_split_conv = (if in_split then VAR_RES_FRAME_SPLIT___split_CONV else
                          VAR_RES_FRAME_SPLIT___imp_CONV) (RATOR_CONV (RAND_CONV (K split_thm)))

   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m]) THENC
               array_split_conv) tt
in
   thm0
end;

end;




(* ---------------------------------------- *)
(* Converts points-to to an array           *)
(* ---------------------------------------- *)

(*
val tt =
   ``holfoot_ap_points_to (var_res_exp_var t)
    (FEMPTY |+ (holfoot_tag "dta",var_res_exp_const tdate) |+
     (holfoot_tag "tl",var_res_exp_const n))``
*)
local
   open stringTheory stringLib
   val my_compset = listLib.list_compset ()
   val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
   val my_compset = listLib.list_compset ()
   val _ = computeLib.add_conv (ord_tm, 1, ORD_CHR_CONV) my_compset
   val _ = computeLib.add_thms char_eq_thms my_compset
   val _ = computeLib.add_thms [holfoot_tag_11, LIST_TO_FMAP_THM, 
          asl_trivial_cond_TF, pairTheory.SND, listTheory.LENGTH,
          pairTheory.FST] my_compset
in

fun holfoot_ap_points_to_TO_array___CONV tt =
let
   val (e, L) = dest_holfoot_ap_points_to tt;
   val (_, upL) = if (finite_mapSyntax.is_fempty L) then (T, []) else
                     (finite_mapSyntax.strip_fupdate L)

   val upL' = map (fn ttt =>
      let
         val (tag, v) = pairSyntax.dest_pair ttt;
         val c = dest_var_res_exp_const v;
         val vl = listSyntax.mk_list ([c], numLib.num);
      in
         pairSyntax.mk_pair (tag, vl)
      end) upL;
   val data = listSyntax.mk_list (rev upL', pairSyntax.mk_prod (
         holfoot_tag_ty, listSyntax.mk_list_type numLib.num))

   val thm0 = SPECL [e, data] (GSYM holfoot_ap_data_array_1);
   val thm1 = var_res_precondition_prove thm0

   val missing_eq = mk_eq (tt, lhs (concl thm1));

   val missing_eq_thm = EQT_ELIM (computeLib.CBV_CONV my_compset missing_eq)

   val thm2 = TRANS missing_eq_thm thm1
in
   thm2
end handle HOL_ERR _ => raise UNCHANGED;

end



(*
   val tt = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
local 
   fun search_fun context sfs n ttt =
       let
          val (e, _) = dest_holfoot_ap_points_to ttt;          
          val ec1 = dest_var_res_exp_const e

          fun search_fun2 m tttt =
          (let
             val (e', ne', _) = dest_holfoot_ap_data_array tttt
             val nc2 = dest_var_res_exp_const ne'
             val ec2 = dest_var_res_exp_const e'
             val thm = prove_in_array_bound context ec1 (ec2, nc2);
          in
             SOME (m, tttt)
          end handle HOL_ERR _ => NONE)
          val found_opt = first_opt search_fun2 sfs
       in
          if not (isSome found_opt) then NONE else
          let
             val (m, tttt) = valOf found_opt;
          in
             SOME (n, m, ttt, tttt)
          end           
       end handle HOL_ERR _ => NONE;
in

fun VAR_RES_FRAME_SPLIT_INFERENCE___data_array___points_to_elim___CONV context tt =
let
   val (f, _, _, _, _, split_sfb, imp_sfb, _) =  dest_VAR_RES_FRAME_SPLIT tt;

   val (split_sfs,_) = bagSyntax.dest_bag split_sfb;
   val (imp_sfs,_) = bagSyntax.dest_bag imp_sfb;

   (*search lists*)
   val found_opt = first_opt (search_fun context imp_sfs) split_sfs;
   val (turn, found_opt) = if (isSome found_opt) then (false, found_opt) 
                           else (true, first_opt (search_fun context split_sfs) imp_sfs);
   val _ = if isSome found_opt then () else raise UNCHANGED;

   val (n, m, sf1, sf2) = valOf found_opt;
   val (n, m) = if turn then (m, n) else (n, m);

   val points_thm = holfoot_ap_points_to_TO_array___CONV sf1

   (*resort and apply*)
   val points_conv = (if not turn then VAR_RES_FRAME_SPLIT___split_CONV else
                          VAR_RES_FRAME_SPLIT___imp_CONV) (RATOR_CONV (RAND_CONV (K points_thm)))

   val thm0 = (VAR_RES_FRAME_SPLIT___split_CONV (BAG_RESORT_CONV [n]) THENC
               VAR_RES_FRAME_SPLIT___imp_CONV (BAG_RESORT_CONV [m]) THENC
               points_conv) tt
in
   thm0
end;

end;



(******************************************************************************)
(* Case split heuritiscs                                                      *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun CASE_SPLIT_HEURISTIC___VAR_RES_COND_HOARE_TRIPLE_lseg tt =
let
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;

   val e = (#2 (dest_holfoot_prog_field_lookup p1)) handle HOL_ERR _ =>
           (#1 (dest_holfoot_prog_field_assign p1))
   val c = dest_var_res_exp_const e

   val (_, _, _, _, sfs) = dest_var_res_prop___propL pre


   fun search_fun _ ttt =
      let
         val (_, e1, _, e2) = dest_holfoot_ap_data_list_seg ttt;
         val c1 = dest_var_res_exp_const e1;
         val _ = if aconv c1 c then () else Feedback.fail(); 
         val c2 = dest_var_res_exp_const e2;
      in SOME c2 end
        
   (* find a proposition that occurs in both *)
   val c2_opt =  first_opt search_fun sfs
   val _ = if isSome c2_opt then () else Feedback.fail();
in
   mk_eq (valOf c2_opt, c)
end;


type var_res_inference = bool -> simpLib.ssfrag -> thm list -> ConseqConv.directed_conseq_conv

structure holfoot_param = 
struct
   open Abbrev
   val exp_to_string = holfoot_base_param.exp_to_string;
   val combinator_thmL = holfoot_base_param.combinator_thmL
   val combinator_terms = (holfoot_separation_combinator_term, holfoot_disjoint_fmap_union_term,
          rhs (concl holfoot_separation_combinator_def))
   val prover_extra = holfoot_base_param.prover_extra;
   val varlist_rwts = holfoot_base_param.varlist_rwts;

   fun LENGTH_EQ_conv tt =
   let
      val (l,r) = dest_eq tt
      val _ = if (listSyntax.is_length r) andalso not (listSyntax.is_length l) then ()
              else raise UNCHANGED
   in
      ISPECL [l,r] EQ_SYM_EQ
   end handle HOL_ERR _ => raise UNCHANGED;

   val LENGTH_EQ_norm_ss =
            simpLib.conv_ss {conv = K (K LENGTH_EQ_conv),
                 key = NONE, name = "LENGTH_EQ_norm", 
                 trace = 2}

   val predicate_ssfrag0 = simpLib.rewrites[]
   val predicate_ssfrag1 = simpLib.merge_ss [predicate_ssfrag0,
      listSimps.LIST_ss ,
      stringSimps.STRING_ss ,
      listLib.LIST_EQ_ss,
      LENGTH_EQ_norm_ss,
      simpLib.rewrites [
        LENGTH_NIL, LENGTH_NIL_SYM,
        LIST_TO_FMAP_THM,
        holfoot_ap_data_list_seg___NOT_EMPTY_DATA___0,
        holfoot_ap_data_list_seg___SAME_START_END,
        holfoot_tag_11,
        holfoot_var_11,
        holfoot_ap_points_to___null,
        holfoot_ap_list_def,
        holfoot_ap_data_list_def,
        holfoot_ap_list_seg_def,
        holfoot_ap_data_list_seg___null,
        holfoot_ap_data_list_seg_num___null,
        holfoot_ap_bintree_def,
        holfoot_ap_tree___null,
        holfoot_ap_data_tree___null,
        holfoot_ap_data_tree___leaf,
        holfoot_ap_data_array___SIMP_THMS,
        holfoot_ap_data_queue___startExp_null,
        holfoot_ap_data_queue___endExp_null,
        tree_11, GSYM tree_distinct, tree_distinct,
        IS_LEAF_REWRITE,

        BUTFIRSTN_LENGTH_NIL, BUTFIRSTN_LENGTH_APPEND,
        FIRSTN_LENGTH_APPEND, LAST_DROP_THM,
        FRONT_TAKE_THM, BUTLAST, LAST, NOT_NULL_SNOC,

        holfoot_var_res_map_REWRITES,
        holfoot_separation_combinator_def,
        REPLACE_ELEMENT_compute,
        LENGTH_REPLACE_ELEMENT, REPLACE_ELEMENT_DEF,
        EL_REPLACE_ELEMENT, HD_REPLACE_ELEMENT,
        LENGTH_FIRSTN_MIN, LENGTH_DROP,

        SUB1, arithmeticTheory.ADD1, arithmeticTheory.NOT_LESS,
        arithmeticTheory.NOT_LESS_EQUAL,
        arithmeticTheory.GREATER_DEF,
        arithmeticTheory.GREATER_EQ
     ]];
      
   val predicate_ssfrag2 = simpLib.merge_ss [predicate_ssfrag1,
      simpLib.rewrites [
        holfoot_ap_data_array___SIMP_THMS___PRECOND,
        TAKE_APPEND1, TAKE_APPEND2,
        BUTFIRSTN_APPEND1, BUTFIRSTN_APPEND2,
        FIRSTN_LENGTH_ID_EVAL, BUTFIRSTN_LENGTH_NIL_EVAL]];

   fun predicate_ssfrag_arith 0 = simpLib.rewrites []
     | predicate_ssfrag_arith 1 =
          numSimps.ARITH_DP_FILTER_ss (K false)
     | predicate_ssfrag_arith 2 =
          numSimps.ARITH_DP_FILTER_ss is_no_proper_diseq
     | predicate_ssfrag_arith _ =
          numSimps.ARITH_DP_FILTER_ss (K true)


   fun predicate_ssfrag 0 = predicate_ssfrag0
     | predicate_ssfrag 1 = simpLib.merge_ss [predicate_ssfrag1, predicate_ssfrag_arith 1]
     | predicate_ssfrag 2 = simpLib.merge_ss [predicate_ssfrag1, predicate_ssfrag_arith 2]
     | predicate_ssfrag 3 = simpLib.merge_ss [predicate_ssfrag2, predicate_ssfrag_arith 2]
     | predicate_ssfrag _ = simpLib.merge_ss [predicate_ssfrag2, predicate_ssfrag_arith 3];

   fun final_decision_procedure context t =
       if (!holfoot_use_yices mod 2 = 1) then
         array_bound_DECIDE___YICES context t
       else Feedback.fail ();


   val resource_proccall_free_thmL = 
       [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_REWRITES];
   val inital_prop_rewrite_thmL = [holfoot_ap_data_list_def,
       holfoot_separation_combinator_def]

   val abstrL = [];

   val comments_step_convL = [];

   val quantifier_heuristicsL  = [rewrite_qp[tree_11,IS_LEAF_REWRITE,IS_NODE_REWRITE]]

   val var_res_prop_implies___GENERATE = [
       holfoot___var_res_prop_implies___GENERATE];

   val VAR_RES_IS_PURE_PROPOSITION___provers = [];

   val hoare_triple_case_splitL = [CASE_SPLIT_HEURISTIC___VAR_RES_COND_HOARE_TRIPLE_lseg]
   val frame_split_case_splitL  = []

   val INFERENCES_LIST___simulate_command =
      [("field_lookup",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_lookup___CONV),
       ("field_assign",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_assign___CONV),
       ("dispose",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___dispose___CONV),
       ("new",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___prog_new___CONSEQ_CONV)];

   val INFERENCES_LIST___simulate_minor_command =
      [("field_lookup_points_to_intro",
        simpset_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_lookup___points_to_intro___CONV),
       ("field_assign_points_to_intro",
        simpset_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_assign___points_to_intro___CONV),
       ("dispose_points_to_intro",
        simpset_strengthen_conseq_conv
        HOLFOOT_INFERENCE___dispose___points_to_intro___CONV),
       ("dispose_main",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___dispose___main___CONSEQ_CONV),
       ("field_lookup_main",
        context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_lookup___main___CONSEQ_CONV),
       ("field_assign_main",
        context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_assign___main___CONSEQ_CONV)];


   val INFERENCES_LIST___expensive_simplifications =
      [("field_lookup_const_intro",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_lookup___const_intro___CONV),
       ("field_assign_const_intro",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_assign___const_intro___CONV),
       ("dispose_const_intro",
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___dispose___const_intro___CONV)]

    val INFERENCES_LIST___entailment_steps = 
      [("holfoot_data_list_seg___same_start_end___frame",
        no_context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___list_seg_same_start_end___CONV),
       ("holfoot_points_to___points_to___frame",
        no_context_strengthen_conseq_conv 
        VAR_RES_FRAME_SPLIT_INFERENCE___points_to_points_to___CONV),
       ("holfoot_points_to___data_list_seg_start___frame",
        context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___points_to_list_seg___CONV),
       ("holfoot_data_list_seg___same_start___frame",
        context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___list_seg_same_start___CONV),
       ("holfoot_points_to___tree___points_to___frame",
        no_context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___points_to_tree___CONV),
       ("holfoot_points_to___data_tree___data_tree___frame",
        no_context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___data_tree_frame___CONV),
       ("holfoot_data_array___same_start_length__frame",
        no_context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___data_array___same_start_length___CONV),
       ("holfoot_data_array___split",
        simpset_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___data_array_interval___SPLIT___CONV),
       ("holfoot_data_array___points_to_TO_array",
        context_strengthen_conseq_conv
        VAR_RES_FRAME_SPLIT_INFERENCE___data_array___points_to_elim___CONV)]


   structure var_res_base = holfoot_base;
end
structure var_res_param = holfoot_param

structure holtactics = vars_as_resourceFunctor (var_res_param)
open holtactics




val HF_GEN_STEP_CONSEQ_CONV  = VAR_RES_GEN_STEP_CONSEQ_CONV;
val HF_GEN_STEP_TAC          = VAR_RES_GEN_STEP_TAC;
val xHF_GEN_STEP_CONSEQ_CONV = xVAR_RES_GEN_STEP_CONSEQ_CONV;
val xHF_GEN_STEP_TAC         = xVAR_RES_GEN_STEP_TAC;

fun xHF_STEP_TAC_n optL n m = xHF_GEN_STEP_TAC optL m n
fun xHF_STEP_TAC optL m = xHF_STEP_TAC_n optL m (SOME 1);
fun xHF_SOLVE_TAC optL = xHF_STEP_TAC_n optL 1 NONE;

val HF_STEP_TAC_n = xHF_STEP_TAC_n [];
val HF_STEP_TAC = xHF_STEP_TAC []
val HF_SOLVE_TAC = xHF_SOLVE_TAC []

fun xHF_CONTINUE_TAC optL = xHF_SOLVE_TAC (careful::optL);
val HF_CONTINUE_TAC = xHF_CONTINUE_TAC [];
val HF_VC_SOLVE_TAC = xHF_SOLVE_TAC [generate_vcs_flag true];
val HF_SPECIFICATION_TAC = VAR_RES_SPECIFICATION_TAC;
val HF_SPECIFICATION_CONSEQ_CONV = VAR_RES_SPECIFICATION___CONSEQ_CONV;

val HF_ELIM_COMMENTS_TAC = VAR_RES_ELIM_COMMENTS_TAC;
val HF_PURE_VC_TAC = VAR_RES_PURE_VC_TAC;
val HF_VC_TAC = VAR_RES_VC_TAC;

fun xHF_SIMPLIFY_TAC optL = xHF_STEP_TAC_n optL 3 (SOME 0);
val HF_SIMPLIFY_TAC = xHF_SIMPLIFY_TAC [];


fun HF_INIT_TAC (asm, t) = 
  (if (is_FASL_SPECIFICATION t) then VAR_RES_SPECIFICATION_TAC else
  VAR_RES_ENTAILMENT_INIT_TAC) (asm, t)


fun print s = Portable.output(Portable.std_out, s)

fun holfoot_set_goal file =
     proofManagerLib.set_goal([], parse_holfoot_file file);

fun holfoot_set_goal_preprocess file =
   ((proofManagerLib.set_goal([], parse_holfoot_file file));
    (proofManagerLib.e (HF_INIT_TAC));
    (proofManagerLib.forget_history());
    (proofManagerLib.status()));

fun holfoot_set_goal_procedures file fL =
   ((proofManagerLib.set_goal ([], parse_holfoot_file_restrict fL file));
   (proofManagerLib.e (HF_INIT_TAC THEN REPEAT CONJ_TAC));
   (proofManagerLib.forget_history());
   (proofManagerLib.status ()));

val holfoot_set_goal_specs = holfoot_set_goal_procedures;



fun print_space n = if n > 0 then (print " ";print_space (n-1)) else ()

fun print_width left i s =
   (if not left then (print_space (i - size s)) else ();
    print s;
    if left then (print_space (i - size s)) else ());

val print_file = ref true
val _ = Feedback.register_btrace ("holfoot print file", print_file);


fun CONJ_ASSUME [] = TRUTH
  | CONJ_ASSUME [t] = ASSUME t
  | CONJ_ASSUME (t::tL) =
      CONJ (ASSUME t) (CONJ_ASSUME tL)

fun ASSUME_CONJ [] = [TRUTH]
  | ASSUME_CONJ tmL =
      let
         val ct = list_mk_conj tmL         
         val thm0 = ASSUME ct
         val thmL = let
             val (thmL', lthm) =
                foldr (fn (_, (thmL, thm)) =>
                  ((CONJUNCT1 thm)::thmL, CONJUNCT2 thm)) ([], thm0) (tl tmL)
             in
                rev (lthm::thmL')
             end;
      in
         thmL
      end;

fun DISCH_ALL_CONJ thm =
let
   val (trueL, hL) = partition (same_const T) (hyp thm)
   val thmL = ASSUME_CONJ (rev hL)
   val thmL' = if null trueL then thmL else TRUTH::thmL

   val thm' = foldr (fn (thm_asm, thm) =>
                MP (DISCH (concl thm_asm) thm) thm_asm) thm thmL'
in 
   DISCH_ALL thm'
end;


fun holfoot_verify_spec_internal verbose print_remaining (file, defaultConseqConv_opt, tacL) =
  let
     open PPBackEnd;
     val timer = ref (Time.now())
     fun start_timer () = timer := Time.now();
     fun print_timer false ok = ()
       | print_timer true (ok,skipped) =
     let
        val d_time = Time.- (Time.now(), !timer);
        val _ = print_width false 8 (Time.toString d_time);
        val _ = print " s - ";
        val _ = if skipped then print_with_style [FG Yellow] "skipped\n" else
                if ok then print_with_style [FG Green] "OK\n" else print_with_style [FG OrangeRed] "failed\n";
     in
        ()
     end

     val t_start = Time.now();

     val _ = start_timer ();
     val _ = print (if !print_file then 
                         (if verbose then ("\nparsing file \""^file^"\" ... ") else
                                          ("\n"^file^" ... ")) else
                         ("\nparsing ... "))

     val t = parse_holfoot_file file;    
     val is_spec = is_FASL_SPECIFICATION t

     val _ = if verbose then (print_timer true (true,false); print "\n\n"; print_backend_term t; print "\n\n")
                        else (print "\n");

     val procedure_names =
     if (is_spec) then
     let
        val tL = (fst o listSyntax.dest_list o rand) t;
        val ntL = map (el 2 o pairSyntax.strip_pair) tL;
        val nL = map stringLib.fromHOLstring ntL
     in
        nL
     end else 
     let
        val tL = strip_conj t
        val e = el 1 tL
        fun get_comment e =
           let
              val (_, rfc, _, _, _, _, _, _) = dest_VAR_RES_FRAME_SPLIT e;
              val s = (fst o dest_var o rand o rator o rand o rand) rfc
           in s end;
        val nL = map get_comment tL
     in
        nL
     end

     val max_width = foldl (fn (a,b:int) => if a > b then a else b) 23 (map (fn s => size s + 5) procedure_names)
     fun print_dots false s = ()
       | print_dots true  s = (print_width true max_width s;print " ... ";Portable.flush_out Portable.std_out);

     val _ = start_timer ();
     val _ = print_dots verbose "preprocessing";   
     val thm_spec = if is_spec then HF_SPECIFICATION_CONSEQ_CONV t else
                    VAR_RES_ENTAILMENT_INIT___CONSEQ_CONV t;
     val _ = print_timer verbose (true, false)

     val _ = if (verbose) then (print_dots true (if is_spec then "verifying specification" else "verifying entailments");print "\n") else ();
     val procedure_conds = zip procedure_names
            ((strip_conj o fst o dest_imp o concl) thm_spec)
     fun verify_proc (p_name, pc) = let
        val my_TAC_opt = SOME (Lib.assoc p_name tacL) handle HOL_ERR _ => NONE
        val _ = print_dots verbose ("   * "^p_name);
        val _ = start_timer();
        val (p_thm_ok, skipped, p_thm) = (if isSome my_TAC_opt then
            (true, false, prove (pc, valOf my_TAC_opt)) else
            (if isSome defaultConseqConv_opt then 
               let
                  val p_thm =  (valOf defaultConseqConv_opt) pc;
                  val p_thm_precond = (fst o dest_imp o concl) p_thm
                  val p_thm_ok = aconv T p_thm_precond
                  val p_thm' = if p_thm_ok then MP p_thm TRUTH else UNDISCH p_thm
               in
                  (p_thm_ok, false, p_thm')
               end else (false, true, ASSUME pc))) handle HOL_ERR _ =>
               (false, false, ASSUME pc);

        val _ = print_timer verbose (p_thm_ok, skipped);
        val _ = if p_thm_ok orelse (not verbose) orelse (not print_remaining) then () else let
                  val _ = print "   remaining proof obligations:\n"
                  val _ = foldl (fn (t, _) => (print_backend_term t;print "\n\n")) () 
                             (hyp p_thm)
                in () end;
     in
        (p_thm, if p_thm_ok then NONE else SOME (hyp p_thm))
     end;
     val procedure_proofs = map verify_proc procedure_conds
     val preconds = flatten (map valOf (filter isSome (map snd procedure_proofs)));


     val d_time = Time.- (Time.now(), t_start);

     val _ = if verbose then () else
                (print_width false 8 (Time.toString d_time);
                 print " s - ");
     val _ = if null preconds then print_with_style [FG Green] "done\n" else print_with_style [FG OrangeRed] "failed\n";

     val _ = if verbose then
                   (print ("time needed: "); print (Time.toString d_time); print " s\n")
             else ();

     (*build final theorem*)
     val thm0 = MP thm_spec (LIST_CONJ (map fst procedure_proofs))
     val thm1 = DISCH_ALL_CONJ thm0
  in
     (thm1, null preconds)
  end;



fun holfoot_set_remaining_goal thm_imp =
let
   val (a,p) = dest_imp (concl thm_imp);
   val _ = proofManagerLib.set_goal ([], p)
   val _ = (Lib.with_flag (proofManagerLib.chatting, false)
       proofManagerLib.expand) (fn _ => ([([],a)], fn thmL => (MP thm_imp (hd thmL))))
   val _ = proofManagerLib.forget_history ();
in
   proofManagerLib.status ()
end;

fun holfoot_prove_remaining (thm_imp,tac) =
let
   val (a,p) = dest_imp (concl thm_imp);
   val a_thm = prove (a, tac);
in
   MP thm_imp a_thm
end;

fun holfoot_interactive_verify_spec verbose print_err file optL_opt tacL =
let
   val (thm, ok) = holfoot_verify_spec_internal verbose print_err (file, 
      (if isSome optL_opt then         
         SOME (xHF_GEN_STEP_CONSEQ_CONV (valOf optL_opt) NONE 1)
       else NONE), tacL);
   val _ = if ok then () else (holfoot_set_remaining_goal thm; ())
in
   thm
end;

fun holfoot_verify_spec file optL =
  holfoot_interactive_verify_spec true false file (SOME optL) []

fun holfoot_tac_verify_spec file optL_opt tacL =
  holfoot_interactive_verify_spec true false file optL_opt tacL

fun holfoot_auto_verify_spec file =
  holfoot_interactive_verify_spec true true file (SOME [generate_vcs]) []

				  
(*
val examplesDir = concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot/EXAMPLES"]
(* 27.5 s *) val file = concat [examplesDir, "/automatic/append.dsf"];
(* 27.5 s *) val file = concat [examplesDir, "/interactive/array.dsf"];


holfoot_set_goal file
holfoot_verify_spec file []

holfoot_set_goal_procedures file ["array_dispose_complicated"] 


holfoot_set_goal_procedures file ["array_frame_3"] 

holfoot_set_goal_procedures file ["array_frame_5"] 
holfoot_set_goal_procedures file ["array_frame_7"] 
holfoot_set_goal_procedures file ["array_lookup_1"] 
holfoot_set_goal_procedures file ["array_assign_1"] 

set_trace "use holfoot_pp" 1
holfoot_interactive_verify_spec true (true,true,true) ([],[],[]) file
HF_SOLVE_TAC THEN

HF_STEP_TAC 10
set_trace "use holfoot_pp" 0
REPEAT STRIP_TAC THEN
Cases_on `n_const = LENGTH data1` THEN
HF_CONTINUE_TAC

HF_STEP_TAC 10

REPEAT STRIP_TAC
CONTINUE_TAC ([],[],[])
STEP_TAC ([],[],[]) 
SIMP_TAC std_ss []
add_holfoot_pp()
xHF_STEP_TAC [careful] 100
FULL_SIMP_TAC list_ss []
REPEAT STRIP_TAC
Cases_on `data1 = []`
val thm = it
val thm_imp = it
SIMP_TAC std_ss [GSYM EL]


holfoot_set_remaining_goal thm_imp

val _ = Feedback.set_trace "PPBackEnd use annotations" 0
val _ = Feedback.set_trace "Unicode" 0

val t = parse_holfoot_file file
SIMP_TAC std_ss [tree_11]
REPEAT STRIP_TAC
STEP_TAC ([],[],[]) 100
SOLVE_TAC ([arithmeticTheory.MIN_DEF],[],[])
open holfootTheory
ASM_SIMP_TAC list_ss [holfoot_ap_data_tree___null]
*)


end;
