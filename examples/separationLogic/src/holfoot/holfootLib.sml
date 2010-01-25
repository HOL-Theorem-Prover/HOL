structure holfootLib :> holfootLib =
struct

(*
quietdec := true;
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
   else term_to_string t

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
   val LENGTH_NIL_GSYM = CONV_RULE ((QUANT_CONV o LHS_CONV) SYM_CONV) LENGTH_NIL

   val predicate_simpset = (list_ss ++ stringSimps.STRING_ss ++
      ListConv1.list_eq_simp_ss ++
      simpLib.rewrites [
        LENGTH_NIL, LENGTH_NIL_GSYM,
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
        tree_11, GSYM tree_distinct, tree_distinct,
        IS_LEAF_REWRITE, 
        TAKE_APPEND1, TAKE_APPEND2,
        BUTFIRSTN_APPEND1, BUTFIRSTN_APPEND2,
        BUTFIRSTN_LENGTH_NIL, BUTFIRSTN_LENGTH_APPEND,
        TAKE_LENGTH_ID,
        FRONT_CONS_EQ_NULL,
        LENGTH_FRONT_CONS,
        LAST_DROP_THM,
        FRONT_TAKE_THM
     ])

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
   val BAG_IN_TRIVIAL_THM = prove (``!e:'a b. BAG_IN e (BAG_INSERT e b)``,
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
          SOME (EQT_ELIM (numLib.ARITH_CONV (mk_neg (mk_eq (c1, c2)))))
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






fun holfoot_implies_in_heap_GENERATE___points_to context sfb tt =
let
   val (e,L) = dest_holfoot_ap_points_to tt;
   val thm0 = ISPECL [sfb, e, L] holfoot_ap_points_to___implies_in_heap___COMPUTE    
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []

fun holfoot_implies_in_heap_GENERATE___data_list_seg context sfb tt =
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


fun holfoot_implies_in_heap_GENERATE___tree context sfb tt =
let
   val (tagL,e1) = dest_holfoot_ap_tree tt;
   val thm0 = ISPECL [e1, tagL, sfb]
           holfoot_ap_tree___implies_in_heap_or_null___COMPUTE
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE___data_tree context sfb tt =
let
   val (tagL,e1,data) = dest_holfoot_ap_data_tree tt;
   val thm0 = ISPECL [e1, tagL, data, sfb]
           holfoot_ap_data_tree___implies_in_heap_or_null___COMPUTE
   val thm1 = var_res_precondition_prove thm0
in
   [thm1]
end handle HOL_ERR _ => []
         | UNCHANGED => []


fun holfoot_implies_in_heap_GENERATE context sfb tt =
   flatten
   (map (fn f => (f context sfb tt) handle Interrupt => raise Interrupt
                                         | e => []) [
       holfoot_implies_in_heap_GENERATE___points_to,
       holfoot_implies_in_heap_GENERATE___data_list_seg,
       holfoot_implies_in_heap_GENERATE___tree,
       holfoot_implies_in_heap_GENERATE___data_tree])


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
      flatten (map (holfoot_implies_in_heap_GENERATE context sfb') sfs);


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


fun holfoot___var_res_prop_implies___GENERATE context 
    (f, wpb, rpb, sfb) =
let
   val sfb_thm = bagLib.SIMPLE_BAG_NORMALISE_CONV sfb handle UNCHANGED => REFL sfb
   val sfb' = rhs (concl sfb_thm)
   val sfs = fst (dest_bag sfb');

   val implies_in_heapL =
      flatten (map (holfoot_implies_in_heap_GENERATE context sfb') sfs);
   val implies_in_heap_pairL = mk_in_heap_pair [] implies_in_heapL

   val res1_L1 = mapfilter (mk_unequal_null context) implies_in_heapL;
   val res1_L2 = mapfilter (mk_unequal___in_heap___in_heap context) implies_in_heap_pairL

   val res1L_0 = flatten [res1_L1, res1_L2]
   val res1L_1 = map var_res_implies_unequal___normalise res1L_0
   val res1L_2 = var_res_implies_unequal___remove_duplicates [] res1L_1
   val res1L = map (var_res_implies_unequal___INTRO_PROP_IMPLIES wpb rpb) res1L_2

   val res2L = mapfilter (mk_equal___in_heap_or_null___in_heap_or_null wpb rpb) implies_in_heap_pairL

   val res = flatten [res1L, res2L]

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
         QUANT_CONV (my_asl_exists_list_CONV e) THENC
         my_asl_exists_list_CONV e
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

in

fun HOLFOOT_INFERENCE___bring_points_to_to_front e tag_t tt =
let
   val (_,pre,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE tt;   
   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre
   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   val _ = if isSome found_opt then () else raise UNCHANGED;               

   (*resort points to to front and insert tag if necessary*)
   val (pos,L_t) = valOf found_opt;
   val thm0a = VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [pos] tt
   val in_thm_term = pred_setSyntax.mk_in (tag_t, finite_mapSyntax.mk_fdom L_t);
   val in_thm0 = computeLib.CBV_CONV in_compset in_thm_term;

   val (in_thm, need_intro) = if aconv (rhs (concl in_thm0)) T then
          (EQT_ELIM in_thm0, false) else
        if aconv (rhs (concl in_thm0)) F then
          (EQF_ELIM in_thm0, true) else
          raise UNCHANGED

   val thm0 = if not need_intro then thm0a else
        let
           val xthm0 = PART_MATCH (lhs o snd o dest_imp o snd o dest_imp) 
                         (ISPEC tag_t HOLFOOT_COND_INFERENCE___points_to___ADD_TAG)
                        (rhs (concl thm0a))
           val xthm1 = MP xthm0 in_thm
           val xthm2 = var_res_precondition_prove xthm1;

           (*give new constant a nice name*)
           val c_const_name = get_const_name_for_exp 
                          ("_"^(holfoot_term_to_string tag_t)) e
           val xthm3 = CONV_RULE 
                   (RHS_CONV
                    (RENAME_VARS_CONV [c_const_name])) xthm2

           val xthm4 = TRANS thm0a xthm3
        in
           xthm4
        end;
in
   (thm0, need_intro)
end;

end;

(******************************************************************************)
(* Inference for field lookup                                                 *)
(******************************************************************************)

(*
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


fun HOLFOOT_INFERENCE___field_lookup___main___CONSEQ_CONV tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (v, e, tag_t) = dest_holfoot_prog_field_lookup p1

   val (thm0, intro) =
      HOLFOOT_INFERENCE___bring_points_to_to_front e tag_t tt
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
   val thm2a = PART_MATCH (snd o dest_imp o snd o dest_imp)
      HOLFOOT_COND_INFERENCE___prog_field_lookup body_t
   val thm2b = var_res_precondition_prove thm2a 

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
   val _ = if is_var_res_exp_const e1 then raise UNCHANGED else ();

   val (intro, _, thm0) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e1 NONE tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   val thm1 = PART_MATCH (lhs o snd o dest_imp)
       HOLFOOT_COND_INFERENCE___prog_field_assign___exp_rewrite body_t
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


local
   open stringTheory stringLib
   val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
   val apply_compset = listLib.list_compset ()
   val _ = computeLib.add_conv (ord_tm, 1, ORD_CHR_CONV) apply_compset
   val _ = computeLib.add_thms char_eq_thms apply_compset
   val _ = computeLib.add_thms [FAPPLY_FUPDATE_THM, holfoot_tag_11] apply_compset
in


fun HOLFOOT_INFERENCE___field_assign___main___CONSEQ_CONV tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (e1, tag_t, e2) = dest_holfoot_prog_field_assign p1

   val (thm0, intro) =
      HOLFOOT_INFERENCE___bring_points_to_to_front e1 tag_t tt
   val body_t = if intro then 
        ((snd o dest_forall o rhs o concl) thm0) else
        ((rhs o concl) thm0)

   (*instantiate main theorem*)
   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
      HOLFOOT_COND_INFERENCE___prog_field_assign body_t
   val thm1b = var_res_precondition_prove thm1a 

   val thm1c = CONV_RULE ((RATOR_CONV o RAND_CONV o VAR_RES_COND_HOARE_TRIPLE___PRECOND_CONV o
                           RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV)
                           finite_mapLib.fupdate_NORMALISE_CONV) thm1b

  
   val thm1 = if intro then
      GEN_IMP ((fst o dest_forall o rhs o concl) thm0) thm1c else thm1c


   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1
in
   thm2
end;

end;


fun HOLFOOT_INFERENCE___field_assign___CONV tt =
let
   val (p1,_,_,_,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val (_, p1') = dest_fasl_comment_location p1;
   val _ = dest_holfoot_prog_field_assign p1'
in
   VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt
end


(******************************************************************************)
(* Inference for dispose                                                      *)
(******************************************************************************)

(*
   val tt = find_term is_VAR_RES_COND_HOARE_TRIPLE (snd (top_goal ()))
*)
fun HOLFOOT_INFERENCE___dispose___const_intro___CONV tt =
let
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val e1 = dest_holfoot_prog_dispose p1
   val _ = if is_var_res_exp_const e1 then raise UNCHANGED else ();

   val (intro, _, thm0) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV e1 NONE tt

   val (body_t, body_conv) = if intro then 
        ((snd o dest_forall o rhs o concl) thm0, QUANT_CONV) else
        ((rhs o concl) thm0, I)

   val thm1 = PART_MATCH (lhs o snd o dest_imp)
       HOLFOOT_COND_INFERENCE___prog_dispose___exp_rewrite body_t
   val thm2 = var_res_precondition_prove thm1
   val thm3 = CONV_RULE ((RHS_CONV o body_conv) (K thm2)) thm0
in
   thm3
end;

fun HOLFOOT_INFERENCE___dispose___points_to_intro___CONV ss context tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val e = dest_holfoot_prog_dispose p1

   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre

   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e) sfs
   val _ = if isSome found_opt then Feedback.fail() else ()
in
    HOLFOOT_INFERENCE___points_to_intro ss context e tt   
end;


fun HOLFOOT_INFERENCE___dispose___main___CONSEQ_CONV tt =
let
   (*destruct and search for points to*)
   val (p1,_,_,pre,_) = dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt;
   val e1 = dest_holfoot_prog_dispose p1

   (*resort points to to front*)
   val (_,_,_,_,sfs) = dest_var_res_prop___propL pre
   val found_opt = first_opt (is_holfoot_ap_points_to___found_opt_pred e1) sfs
   val _ = if isSome found_opt then () else raise UNCHANGED;               

   val (pos,_) = valOf found_opt;
   val thm0 = VAR_RES_COND_HOARE_TRIPLE___RESORT_PRECOND_CONV [pos] tt

   (*instantiate main theorem*)
   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
      HOLFOOT_COND_INFERENCE___prog_dispose (rhs (concl thm0))
   val thm1 = var_res_precondition_prove thm1a 
 
   val thm2 = CONV_RULE (RAND_CONV (K (GSYM thm0))) thm1
in
   thm2
end;

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
   val v = dest_holfoot_prog_new p1
   val ve = mk_var_res_exp_var v (Type `:holfoot_a_expression`)

   (* intro var *)
   val thm0a = thm0_fun ()
   val (intro, c, thm0b) = VAR_RES_COND_INFERENCE___CONST_INTRO___CONV  ve NONE (rhs (concl thm0a));
   val thm0 = TRANS thm0a thm0b
   val t' = let val ttt = rhs (concl thm0) in
               if intro then (snd (dest_forall ttt)) else ttt end


   val thm1a = PART_MATCH (snd o dest_imp o snd o dest_imp)
                 HOLFOOT_COND_INFERENCE___prog_new t'
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
in
   thm5
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
   val combinator_thmL = holfoot_base_param.combinator_thmL
   val combinator_terms = (holfoot_separation_combinator_term, holfoot_disjoint_fmap_union_term,
          rhs (concl holfoot_separation_combinator_def))
   val prover_extra = holfoot_base_param.prover_extra;
   val varlist_rwts = holfoot_base_param.varlist_rwts;
   val predicate_simpset = holfoot_base_param.predicate_simpset

   val resource_proccall_free_thmL = 
       [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___HOLFOOT_REWRITES];
   val inital_prop_rewrite_thmL = [holfoot_ap_data_list_def,
       holfoot_separation_combinator_def]

   val abstrL = [];

   val comments_step_convL = [];

   val quantifier_heuristicsL  = [list_qp, rewrite_qp[tree_11,IS_LEAF_REWRITE,IS_NODE_REWRITE]]

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
        no_context_strengthen_conseq_conv
        HOLFOOT_INFERENCE___field_lookup___main___CONSEQ_CONV),
       ("field_assign_main",
        no_context_strengthen_conseq_conv 
        HOLFOOT_INFERENCE___field_assign___main___CONSEQ_CONV)]


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
        VAR_RES_FRAME_SPLIT_INFERENCE___data_tree_frame___CONV)]


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


fun print s = Portable.output(Portable.std_out, s)

fun holfoot_set_goal file =
     proofManagerLib.set_goal([], parse_holfoot_file file);

fun holfoot_set_goal_preprocess file =
   ((proofManagerLib.set_goal([], parse_holfoot_file file));
    (e (HF_SPECIFICATION_TAC));
    (proofManagerLib.forget_history());
    (proofManagerLib.status()));

fun holfoot_set_goal_procedures file fL =
   ((proofManagerLib.set_goal ([], parse_holfoot_file_restrict fL file));
   (e (HF_SPECIFICATION_TAC THEN REPEAT CONJ_TAC));
   (proofManagerLib.forget_history());
   (proofManagerLib.status ()));

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

     val _ = if verbose then (print_timer true (true,false); print "\n\n"; print_backend_term t; print "\n\n")
                        else (print "\n");

     val procedure_names =
     let
        val tL = (fst o listSyntax.dest_list o rand) t;
        val ntL = map (el 2 o pairSyntax.strip_pair) tL;
        val nL = map stringLib.fromHOLstring ntL
     in
        nL
     end;

     val max_width = foldl (fn (a,b:int) => if a > b then a else b) 23 (map (fn s => size s + 5) procedure_names)
     fun print_dots false s = ()
       | print_dots true  s = (print_width true max_width s;print " ... ";Portable.flush_out Portable.std_out);

     val _ = start_timer ();
     val _ = print_dots verbose "preprocessing";   
     val thm_spec = HF_SPECIFICATION_CONSEQ_CONV t;
     val _ = print_timer verbose (true, false)

     val _ = if (verbose) then (print_dots true "verifying specification";print "\n") else ();
     val procedure_conds = (strip_conj o fst o dest_imp o concl) thm_spec
     val pc = hd procedure_conds
     fun verify_proc pc = let
        val p_name = (fst o dest_var o rand o rator o rand o rator) (find_term is_fasl_comment_location pc)
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


fun holfoot_interactive_verify_spec (verbose,print_err) file optL_opt tacL =
let
   val (thm, ok) = holfoot_verify_spec_internal verbose false (file, 
      (if isSome optL_opt then         
         SOME (xHF_GEN_STEP_CONSEQ_CONV (valOf optL_opt) NONE 1)
       else NONE), tacL);
   val _ = if ok then () else (
      proofManagerLib.set_goal ([],(fst o dest_imp o concl) thm);());
in
   thm
end;

fun holfoot_interactive_verify_spec verbose print_err file optL_opt tacL =
let
   val (thm, ok) = holfoot_verify_spec_internal verbose print_err (file, 
      (if isSome optL_opt then         
         SOME (xHF_GEN_STEP_CONSEQ_CONV (valOf optL_opt) NONE 1)
       else NONE), tacL);
   val _ = if ok then () else (
      proofManagerLib.set_goal ([],(fst o dest_imp o concl) thm);());
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
val examplesDir = concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot/EXAMPLES/"]
(* 27.5 s *) val file = concat [examplesDir, "automatic/mergesort.sf"];

(*just parsing the file as a start*)
(* 27.5 s *) val file = concat [examplesDir, "automatic/list_length.sf"];
(* 27.5 s *) val file = concat [examplesDir, "working/business1.sf"];
(* 27.5 s *) val file = concat [examplesDir, "working/parallel_mergesort.sf"];

(* 27.5 s *) val file = concat [examplesDir, "interactive/bst.dsf"];
holfoot_set_goal file
holfoot_auto_verify_spec true file
val t = parse_holfoot_file_restrict ["search_tree_lookup"] file


holfoot_interactive_verify_spec true (true,true,true) ([],[],[]) file

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
