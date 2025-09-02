structure lambdaStateDecompilerLib =
struct

open HolKernel boolLib bossLib;

local open itreeTauTheory lambdaStateTheory in

(* -------------------------------------------------------------------------- *)
(* Decompilation stages:                                                      *)
(*   1. unfold the itree once, and save its definition into the memory        *)
(*   2. extract the sub-trees in the defintion                                *)
(*   3. for each sub-tree:                                                    *)
(*        a. if it is already in the memory then do nothing                   *)
(*        b. else this is a new tree, recursive back to step 1 with it        *)
(*      until no more new tree found, the memory has enough tree to represent *)
(*      the whole program                                                     *)
(*   4. however, the above one has a lot of intermediate (one-step) trees,    *)
(*      remove them by traverse the memory and delete non-called sub-trees    *)
(* -------------------------------------------------------------------------- *)
(* Tactic strategy:                                                           *)
(*   1. rewrite the itree semantics into unfold functions                     *)
(*   2. perform the following checks and rewrites                             *)
(*        a. if the LHS or the RHS is unfolded deeper, then unfold the other  *)
(*           one once                                                         *)
(*        b. if there is a bind of two trees, split them into two sub-goals   *)
(*           and "recursively" invoke the tactic for those                    *)
(* -------------------------------------------------------------------------- *)
(* Proof-producing decompilation:                                             *)
(*   Store the main trees and sub-trees definitions, then use the tactic to   *)
(*   prove them. Finally, return the theorems                                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Constant definitions                                                       *)
(* -------------------------------------------------------------------------- *)

val skip_const = “Skip”;
val flip_const = “FlipCoin”;
val call_const = “Call”;
val while_const = “While”;
val seq_const = “Seq”;

val itree_unfold_const = “itree_unfold”;
val bind_const = “($>>=):((bool, unit, unit) itree -> (unit -> (bool, unit, unit) itree) -> (bool, unit, unit) itree)”;

val ret_const = “Ret:unit -> (bool, unit, unit) itree”
val tau_const = “Tau:((bool, unit, unit) itree -> (bool, unit, unit) itree)”
val vis_const = “Vis:(unit -> (bool -> (bool, unit, unit) itree) -> (bool, unit, unit) itree)”

val equal_const = “($=):(((bool, unit, unit) itree) -> ((bool, unit, unit) itree) -> bool)”

(* -------------------------------------------------------------------------- *)
(* Various helper functions                                                   *)
(* -------------------------------------------------------------------------- *)

fun union_def_list list1 list2 =
  case list2 of
    (hd::list2') =>
      (case exists (term_eq (fst hd)) (map fst list1) of
         true => union_def_list list1 list2'
       | false => union_def_list (hd::list1) list2')
  | _ => list1

fun union_term list1 list2 =
  case list2 of
    (hd::list2') =>
      (case exists (term_eq (hd)) list1 of
         true => union_term list1 list2'
       | false => union_term (hd::list1) list2')
  | _ => list1


fun find_tree_def tree_def_list tree =
  case tree_def_list of
    tree_def::tree_defs =>
      (if term_eq (fst tree_def) tree then
         snd tree_def
       else
         find_tree_def tree_defs tree
      )
  | _ => raise Domain

fun mk_raw_flip itree_rator [prog1, prog2] =
  let val itree1 = mk_monop itree_rator prog1;
      val itree2 = mk_monop itree_rator prog2;
  in
    (flip_const, [itree1, itree2])
  end

fun mk_raw_call itree_rator [prog_num] =
  let val env = itree_rator |> rand;
      val callee_prog = concl (EVAL (mk_monop env prog_num)) |> rand;
      val inner_tree = mk_monop itree_rator callee_prog;
  in
    (call_const, [inner_tree])
  end

fun mk_raw_while itree_rator [prog] =
  let val inner_while = mk_monop while_const prog;
      val inner_seq = mk_binop seq_const (prog, inner_while);
      val inner_tree = mk_monop itree_rator inner_seq;
  in
    (while_const, [inner_tree])
  end

fun mk_raw_seq itree_rator [prog1, prog2] =
  let val itree1 = mk_monop itree_rator prog1;
      val itree2 = mk_monop itree_rator prog2;
  in
    (seq_const, [itree1, itree2])
  end

fun mk_flip_from_tree [itree1, itree2] =
  let val if_exp = mk_cond  (“x:bool”, itree1, itree2);
      val lambda_exp = mk_abs (“x:bool”, if_exp);
  in
    mk_binop vis_const (“():unit”, lambda_exp)
  end

fun mk_call_from_tree [inner_tree] =
   mk_monop tau_const inner_tree

fun mk_while_from_tree [inner_tree] =
   mk_monop tau_const inner_tree

fun mk_seq_from_tree [itree1, itree2] =
  let val tau_tree2 = mk_monop tau_const itree2;
      val abs_tree2 = mk_abs (“x:unit”, tau_tree2);
      val ret_tree = mk_monop ret_const “():unit”;
      val inner_tree = mk_binop bind_const (itree1, abs_tree2);
  in
    if term_eq ret_tree itree1 then
      tau_tree2
    else
      inner_tree
  end

(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 1, 2, 3                                            *)
(* -------------------------------------------------------------------------- *)

fun itree_raw_unfold_once exp =
  let val prog_const = exp |> rand |> strip_comb |> fst;
      val prog_args = exp |> rand |> strip_comb |> snd;
      val itree_rator = exp |> rator;
  in
    if term_eq prog_const skip_const then
      (skip_const, [])
    else if term_eq prog_const flip_const then
      mk_raw_flip itree_rator prog_args
    else if term_eq prog_const call_const then
      mk_raw_call itree_rator prog_args
    else if term_eq prog_const while_const then
      mk_raw_while itree_rator prog_args
    else if term_eq prog_const seq_const then
      mk_raw_seq itree_rator prog_args
    else
      raise Domain
  end

fun mutual_raw_gen itree_defs itree =
  let fun mutual_raw_list itree_defs itrees =
      case itrees of
        tree1::trees' => mutual_raw_list (mutual_raw_gen itree_defs tree1) trees'
      | _ => itree_defs;
  in
    if (exists (term_eq itree) (map fst itree_defs)) then
      itree_defs
    else
      let val (tree_def, inner_trees) = itree_raw_unfold_once itree;
      in
        mutual_raw_list (union_def_list itree_defs [(itree, (tree_def, inner_trees))]) inner_trees
      end
   end

fun decompile_raw itree = mutual_raw_gen [] itree;

(* -------------------------------------------------------------------------- *)
(* Implementation of STAGE 4, 5                                               *)
(* -------------------------------------------------------------------------- *)


fun construct_min_shallow tree_defs used_tree original_tree tree =
  let val new_used_tree = union_term used_tree [tree]
      val tree_def = find_tree_def tree_defs tree;
      val first_level = tree_def |> fst;
      val inner_trees = tree_def |> snd;
      fun list_construct_loop inners =
         case inners of
           (t::ts) =>
             (if exists (term_eq t) new_used_tree then
                let val (remaining_list, remaining_final_trees) = list_construct_loop ts;
                in
                  if term_eq original_tree t then
                    (t::remaining_list, remaining_final_trees)
                  else
                    (t::remaining_list, union_term [t] remaining_final_trees)
                end
              else
                let val (inner_tree, final_trees) = construct_min_shallow tree_defs new_used_tree original_tree t;
                    val (remaining_list, remaining_final_trees) = list_construct_loop ts
                in
                  if exists (term_eq t) final_trees then
                    (t::remaining_list, union_term final_trees remaining_final_trees)
                  else
                    (inner_tree::remaining_list, union_term final_trees remaining_final_trees)
                end
             )
         |  _ => ([], []);
      val (explored_trees, final_trees) = list_construct_loop inner_trees;
  in
    if term_eq first_level skip_const then
      (mk_monop ret_const “():unit”, final_trees)
    else if term_eq first_level flip_const then
      (mk_flip_from_tree explored_trees, final_trees)
    else if term_eq first_level call_const then
      (mk_call_from_tree explored_trees, final_trees)
    else if term_eq first_level while_const then
      (mk_while_from_tree explored_trees, final_trees)
    else if term_eq first_level seq_const then
      (mk_seq_from_tree explored_trees, final_trees)
    else
      raise Domain
  end

fun list_decompile tree_defs used_tree trees =
  case trees of
    (t::ts) => (t, fst (construct_min_shallow tree_defs used_tree t t))::list_decompile tree_defs used_tree ts
  | _ => []

fun decompile itree =
  let val tree_defs = decompile_raw itree;
      val (itree_def, sub_trees) = construct_min_shallow tree_defs [] itree itree;
      val all_used_tree = union_term sub_trees [itree];
  in
    ((itree, itree_def), list_decompile tree_defs all_used_tree sub_trees)
  end

(* -------------------------------------------------------------------------- *)
(* Implementation of decompilation-proof tactic                               *)
(* -------------------------------------------------------------------------- *)

fun binding_exp exp = bind_const IN (all_atoms exp);

fun decompiler_eqn (assms, concl) =
  let val lhs = concl |> rator |> rand;
      val rhs = concl |> rand;
      val lhs_func = lhs |> strip_comb |> fst;
      val rhs_func = rhs |> strip_comb |> fst;
      val l_unfold = same_const lhs_func itree_unfold_const;
      val r_unfold = same_const rhs_func itree_unfold_const;
      val l_bind = same_const lhs_func bind_const;
      val r_bind = same_const rhs_func bind_const;
      val bind_inl = binding_exp lhs;
      val bind_inr = binding_exp rhs;
  in
    if ((same_const “$o” lhs_func) orelse (same_const “$o” rhs_func)) then
      rw[FUN_EQ_THM] >> BasicProvers.FULL_CASE_TAC
    else if (l_unfold andalso r_bind andalso (not bind_inl)) then
      let val [step_lenv, lprog] = lhs |> strip_comb |> snd;
          val (lprog_const, [lprog1, lprog2]) = lprog |> strip_comb;
          val [rtree1, abs_tau_rtree2] = rhs |> strip_comb |> snd;
          val rtree1_func = rtree1 |> strip_comb |> fst;
      in
        if same_const rtree1_func itree_unfold_const then
          let val [_, rprog1] = rtree1 |> strip_comb |> snd;
              val (_, tau_rtree2) = strip_abs abs_tau_rtree2;
              val (_, [rtree2]) = strip_comb tau_rtree2;
              val subgoal = mk_binop equal_const (rtree2, (mk_binop itree_unfold_const (step_lenv, lprog2)));
              val subgoal_quote = [QUOTE (term_to_string subgoal)];
          in
            if term_eq lprog1 rprog1 andalso term_eq lprog_const seq_const then
              subgoal_quote by (rpt decompiler_eqn) >>
              rw[] >>
              PURE_REWRITE_TAC[GSYM seq_bind_unfold_funs] >>
              rw[]
            else
              raise (mk_HOL_ERR "Feedback" "inside1" "try")
          end
        else
          let val ltree1 = mk_binop itree_unfold_const (step_lenv, lprog1);
              val psubgoal = mk_binop equal_const (rtree1, ltree1);
              val psubgoal_quote = [QUOTE (term_to_string psubgoal)];
              val (_, tau_rtree2) = strip_abs abs_tau_rtree2;
              val (_, [rtree2]) = strip_comb tau_rtree2;
              val subgoal = mk_binop equal_const (rtree2, (mk_binop itree_unfold_const (step_lenv, lprog2)));
              val subgoal_quote = [QUOTE (term_to_string subgoal)];
          in
            psubgoal_quote by (rpt decompiler_eqn) >>
            subgoal_quote by (rpt decompiler_eqn) >>
            rw[] >>
            PURE_REWRITE_TAC[GSYM seq_bind_unfold_funs] >>
            rw[]
          end
      end
    else if (r_unfold andalso l_bind andalso (not bind_inr)) then
      irule EQ_SYM
    else if (l_unfold andalso (not r_unfold)) then
      rw[Once itree_unfold, itree_step]
    else if (r_unfold andalso (not l_unfold)) then
      irule EQ_SYM
    else if (l_unfold andalso r_unfold) then
      let val [_, lprog] = lhs |> strip_comb |> snd;
          val [_, rprog] = rhs |> strip_comb |> snd;
      in
        if term_eq lprog rprog then
          rw[]
        else
          raise (mk_HOL_ERR "Feedback" "inside2" "try")
      end
    else
      raise Domain
  end (assms, concl)

val decompiler_tactic = PURE_REWRITE_TAC[itree_semantics] >> rpt decompiler_eqn

(* -------------------------------------------------------------------------- *)
(* Implementation of the proof-producing decompiler                           *)
(* -------------------------------------------------------------------------- *)

fun mk_itree_def name itree =
  let val ((_, itree_def), _) = decompile itree;
  in
    Define $ single $ ANTIQUOTE $ mk_eq(mk_var(name, “:(bool, unit, unit) itree”), itree_def)
  end

fun itree_eqn_main_proof name itree itree_def =
  let val tree_name = concat [name, "_main"];
      val name_thm = Define $ single $ ANTIQUOTE $ mk_eq(mk_var(tree_name, “:(bool, unit, unit) itree”), itree)
      val goal = mk_binop equal_const (name_thm |> concl |> rator |> rand, itree_def);
      val goal_quote = [QUOTE (term_to_string goal)];
      val tree_thm = Q.store_thm(concat [tree_name, "_thm"], goal_quote, PURE_REWRITE_TAC [name_thm] \\ decompiler_tactic)
  in
    (name_thm, tree_thm)
  end

fun itree_eqn_proof name type_name num itree itree_def =
  let val tree_name = concat [name, "_", type_name, "_", int_to_string num];
      val name_thm = Define $ single $ ANTIQUOTE $ mk_eq(mk_var(tree_name, “:(bool, unit, unit) itree”), itree)
      val goal = mk_binop equal_const (name_thm |> concl |> rator |> rand, itree_def);
      val goal_quote = [QUOTE (term_to_string goal)];
      val tree_thm = Q.store_thm(concat [tree_name, "_thm"], goal_quote, PURE_REWRITE_TAC [name_thm] \\ decompiler_tactic)
  in
    (name_thm, tree_thm)
  end

fun itree_eqn_proof_list name type_name num trees =
  case trees of
    (t::ts) =>
      let val (name_thms, tree_thms) =  (itree_eqn_proof_list name type_name (num + 1) ts);
          val (name_thm, tree_thm) = itree_eqn_proof name type_name num (fst t) (snd t);
      in
        (name_thm::name_thms, tree_thm::tree_thms)
      end
  | _ => ([], [])


fun proof_dec name itree =
  let val ((_, itree_def), sub_trees) = decompile itree;
      val env_thm  =  Define $ single $ ANTIQUOTE $ mk_eq(mk_var(concat [name, "_env"], “:(num -> prog)”), itree |> rator |> rand);
      val (name_thm, tree_thm) = itree_eqn_main_proof name itree itree_def;
      val (name_thms, tree_thms) = itree_eqn_proof_list name "sub" 0 sub_trees;
  in
    (LIST_CONJ (map (PURE_REWRITE_RULE (map GSYM (name_thm::name_thms))) (tree_thm::tree_thms)),
     LIST_CONJ (map (PURE_REWRITE_RULE [GSYM env_thm]) (name_thm::name_thms)), env_thm)
  end

end

end
