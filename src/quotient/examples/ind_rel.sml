(* Subject: Mutually recursive rule induction *)
(* Author: Myra Van Inwegen *)
(* Part of the author's doctoral dissertation *)

(* Summary:
      check_inductive_relations :
         term list ->      (* patterns *)
         term ->           (* term giving rules *)
         term list         (* each term corresponds to a quantified rule *)
      define_inductive_relations :
         term list ->      (* patterns *)
         term ->           (* term giving rules *)
         thm * thm         (* rules_satisfied theorem, induction theorem *)
      prove_inversion_theorems :
         thm ->            (* rules_satisfied theorem *)
         thm ->            (* induction theorem *)
         thm list          (* inversion theorems *)
      prove_strong_induction :
         thm ->            (* rules_satisfied theorem *)
         thm ->            (* induction theorem *)
         thm               (* strong induction theorem *)
      rule_induct :
         thm ->            (* induction theorem (strong or regular) *)
         tactic            (* sets up induction *)      *)

(* For interactive session, do the following:
load "utilsLib";
*)

structure ind_rel :> ind_rel =
struct

open HolKernel Parse boolLib;

val nth = List.nth;

fun QCONV c tm = c tm handle _ => REFL tm;


(*
   SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A,t] t1    [A] t
*)

local
    val bool = (==`:bool`==)
in
    fun SUPPOSE_TAC new_claim current_goal =
        if type_of new_claim = bool
            then
                ([(new_claim::(fst current_goal),snd current_goal),
                  (fst current_goal, new_claim)],
                 fn [goalthm,claimthm] =>
                   MP (DISCH new_claim goalthm) claimthm
                  | _ => raise mk_HOL_ERR "define_inductive_relations" "SUPPOSE_TAC"
                           "invalid application")
        else raise mk_HOL_ERR "define_inductive_relations" "SUPPOSE_TAC"
               "The claim doesn't have type :bool"
end


(*
  ADD_STRIP_ASSUMS_THEN : {new_assumptions:term list, tactic:tactic} -> tactic

  Like ADD_ASSUMS_THEN except it strips the new assumptions before
  adding them to the assumptions.
*)

fun ADD_STRIP_ASSUMS_THEN {new_assumptions = [], tactic} (asms,goal) =
      tactic (asms,goal)
  | ADD_STRIP_ASSUMS_THEN {new_assumptions = (claim::rest), tactic}
                          (asms,goal) =
      if exists (aconv claim) asms
          then ADD_STRIP_ASSUMS_THEN
                {new_assumptions = rest,
                 tactic = tactic}
                (asms,goal)
      else (SUPPOSE_TAC claim THENL
            [((POP_ASSUM STRIP_ASSUME_TAC) THEN
              (ADD_STRIP_ASSUMS_THEN {new_assumptions=rest,tactic=tactic})),
             ALL_TAC])
           (asms,goal)

(*
   use_thm : {theorem:thm, thm_tactic:(thm -> tactic)} -> tactic

  For adding the hypotheses of a theorem to the assumptions of a goal
  before applying the tactic resulting from applying thm_tactic to
  the given theorem.
*)

fun use_thm {theorem, thm_tactic} =
    ADD_STRIP_ASSUMS_THEN{new_assumptions = hyp theorem,
                          tactic = thm_tactic theorem}


(*
from utilsLib.MP_IMP_TAC:

   MP_IMP_TAC : thm -> tactic  ( thm = [A1] |- t2 ==> t1 )

      [A] t1
    ==========
      [A] t2
*)

fun MP_IMP_TAC imp_thm (thisgoal as (asms,goal)) =
    if is_imp (concl imp_thm)
        then
            if aconv (snd (dest_imp (concl imp_thm))) goal
                then
                    use_thm
                      {theorem = imp_thm,
                       thm_tactic =
                         fn imp_thm => fn (asms,goal) =>
                           ([(asms,fst(dest_imp(concl imp_thm)))],
                            fn [thm] => MP imp_thm thm
                             | _ => raise mk_HOL_ERR "define_inductive_relations" "MP_IMP_TAC"
                                      "invalid application")}
                      thisgoal
            else raise mk_HOL_ERR "define_inductive_relations" "MP_IMP_TAC"
                   "theorem doesn't imply goal"
    else raise mk_HOL_ERR "define_inductive_relations" "MP_IMP_TAC"
           "theorem is not an implication"


(* This function takes in the rules, checks them, quantifies them, and
   returns the quantified term to the user to look over and make sure
   it makes sense. Error messages are printed out if there are
   problems.  Errors are reported according to rule number, where the
   first rule is rule 0. In other words, if there's a message
   complaining about an error in rule n, then that bad rule is nth
   (strip_conj rules_term, n). *)

fun check_inductive_relations patterns rules_term =

let

(* if neither A_list nor B_list have any duplicates, but possibly
   A_list and B_list have some common elements, then the result will
   be a list with no common elements *)
fun append_no_dup (A_list, B_list) =
    let fun helper (A::As) B_list As_to_add =
            if tmem A B_list then helper As B_list As_to_add
            else helper As B_list (A::As_to_add)
          | helper [] B_list As_to_add = (rev As_to_add)@B_list
    in
        helper A_list B_list []
    end

(* val nth = Sml_system.List.nth *)

(* if ftn_type is a1_ty -> a2_ty ->  ... -> an_ty, this function returns
   the "argument" types, [a1_ty, a2_ty, ... a(n-1)_ty] *)
fun get_arg_types ftn_type =
    let fun helper the_type arg_types =
        let val (tyop, args) = dest_type the_type
        in
            if (tyop = "fun") andalso (args <> []) then
                helper (nth (args, 1)) ((hd args)::arg_types)
            else
                rev arg_types
        end
    in helper ftn_type []
    end

(* This makes sure that a list of variables are different from some set
   of variables to avoid, as well as each other. Send in the list of vars
   you want to have distinct names as (var::vars), [] as new_vars, and
   the variables to avoid as vars_to_avoid *)
fun ensure_vars_different (var::vars) new_vars vars_to_avoid =
    let val new_var = Term.variant vars_to_avoid var
    in
        ensure_vars_different vars (new_var::new_vars)
        (new_var::vars_to_avoid)
    end
  | ensure_vars_different [] new_vars _ = rev new_vars

fun foldr ftn base (b::bs) = ftn (b, (foldr ftn base bs))
  | foldr ftn base [] = base

(* takes all existential variables in goal, and instantiates
   them to the same variable *)
fun multi_var_exists (asm, gl) =
    let val (vars, tm) = strip_exists gl
    in
        foldr
        (fn (var, tac) => (EXISTS_TAC var) THEN tac)
        ALL_TAC
        vars
        (asm, gl)
    end;

(* first goal -- break down the term and check it *)
val (relations, vars_list) = foldr
    (fn (tm, (rels, vars)) => let val (rel, more_vars) = strip_comb tm
     in (rel::rels, (ensure_vars_different more_vars [] [])::vars) end)
    ([], []) patterns

val orig_rules = strip_conj rules_term
val all_variables = all_vars rules_term

(* relations are variables at this point *)
fun relations_in_tm tm =
    if is_var tm then tmem tm relations else
    if is_const tm then false else
    if is_abs tm then relations_in_tm (body tm) else
    (* must be comb *)
        let val (t1, t2) = dest_comb tm in
            relations_in_tm t1 orelse relations_in_tm t2
        end

(* this function makess sure that the rules are of the form needed *)
fun check_rule rule_num rule =
    let fun check_hyp (hyp1::hyps) =
            let val (rator, rands) = strip_comb hyp1 in
                if tmem rator relations then
                    (* check that the relations don't occur in rands *)
                    if (foldr (fn (tm, acc) => relations_in_tm tm orelse acc)
                        false rands) then
                        raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                          ("found relation being defined"^
                             " in arg to "^(fst(dest_var rator))^
                             " in hypothesis ofrule number "^
                             (Lib.int_to_string rule_num))
                    else check_hyp hyps
                else if relations_in_tm hyp1 then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("found relation being defined"^
                     " in side condition in rule number "^
                     (Lib.int_to_string rule_num))
                else check_hyp hyps
            end |
            check_hyp [] = true
        fun check_concl tm =
            let val (rator, rands) = strip_comb tm in
                if not (tmem rator relations) then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("must have relation as operator in "^
                     "conclusion of rule "^(Lib.int_to_string rule_num))
                else if
                  foldr (fn (tm, acc) => relations_in_tm tm orelse acc) false rands
                then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("found relation being defined"^
                     " in arg to "^(fst(dest_var rator))^
                     " in conclusion of rule number "^
                     (Lib.int_to_string rule_num))
                else true
            end
    in
        if is_imp rule then
            let val (hyp1, conc) = dest_imp rule in
                check_hyp (strip_conj hyp1) andalso
                check_concl conc
            end
        else
            check_concl rule
    end

fun check_rules rule_num (rule::rules) =
    check_rule rule_num rule andalso check_rules (rule_num + 1) rules |
    check_rules _ [] = true

val _ = check_rules 0 orig_rules

(* now sort the rules according to the relation that they are for *)
fun rule_defines_relation rule relation =
    if is_imp rule then
      relation ~~ fst (strip_comb (snd (dest_imp rule)))
    else
      relation ~~ fst (strip_comb rule)

val sorted_rules = map
    (fn rel => (filter (fn x => rule_defines_relation x rel) orig_rules))
    relations

(* put the rules back together into one list *)
val rules = foldr (fn (l1, l2) => l1@l2) [] sorted_rules

(* now quantify the rules -- that is, universally quantify vars in
   conclusion and existentially those in the hypothesis *)
fun quantify_rule rule =
    if is_imp rule then
        let val (t1, t2) = dest_imp rule
            val vars_in_t2 = filter (fn v => not (tmem v relations))
                                    (free_vars t2)
            val total_vars = vars_in_t2@relations
            val vars_in_t1 = filter
                               (fn v => not (tmem v total_vars)) (free_vars t1)
            val new_t1 = list_mk_exists (rev vars_in_t1, t1)
            val new_imp = mk_imp (new_t1, t2)
        in
            list_mk_forall (rev vars_in_t2, new_imp)
        end
    else
        let val vars_in_rule = filter
            (fn v => not (tmem v relations)) (free_vars rule)
        in
            list_mk_forall (rev vars_in_rule, rule)
        end

val new_rules = map quantify_rule rules

in
    new_rules
end



(* Function define_inductive_relations patterns rules_term:
   term list -> term -> (thm * thm)

   Input:

   The patterns give, for each relation, a term of the form
   rel vars
   The purpose of this is twofold -- to give the order in which the
   user prefers to see the relations listed, and to give some nice
   variable names to use in the theorems.

   The goal is that rules_term specifies all the rules for defining
   relations rel_1 ... rel_n.

   The form of rules_term was chosen to be a compromise between being
   not too offensive for a user to type in, and being readable. So we
   do not require that the variables be quantified in the rules, since
   it clutters the specification. (However, this means that between
   the rules, the same variables must have the same types.) We also
   put all the rules together in one term to avoid having the users
   having to supply too much type information (the bigger the term,
   the more HOL type inference has to work with).

   Thus the form is:

   rule_0 /\ rule_1 /\ ... /\ rule_m

   Each rule_i (there is no particular order that the rules have to be
   in, but the theorem proved will have the rules sorted according to
   the relation they are defining) must be a rule for one of the
   relations, say rel_k, and must have either of the two following
   forms:

   (rel_k <args>)
        (an axiom) or
   ((hyp_1 /\ hyp_2 /\ ... /\ hyp_ni) ==> rel_k <args>)
        (rule with hypotheses)

   where each hyp_j has the form

   rel_m <args>           or
   side_condition (an arbitrary boolean, does not involve rel_1 ... rel_n)

   Each rule_i actually represents:

   (!<non-relation vars free in args>. rel_k <args>)        or
   (!<non-relation vars free in args>.
      (?<vars'>. hyp_1 /\ hyp_2 /\ ... /\ hyp_ni) ==> rel_k <args>)

   where <vars'> = non-relation vars free in hyp_1, hyp_2, ... hyp_ni
   that are not free in the conclusion.

   ------------

   Output:

   Two theorems are returned as a pair, (thm1, thm2). The first is a
   conjunction, where each conjunct says that the new relations
   satisfy one rule. The second is the induction theorem for the new
   relations. I made an attempt to give pretty good error messages.
   Errors are reported according to rule number, where the first rule
   is rule 0. In other words, if there's a message complaining about
   an error in rule n, then that bad rule is
   nth (strip_conj rules_term, n).

*)

fun define_inductive_relations patterns rules_term =

let

(* if neither A_list nor B_list have any duplicates, but possibly
   A_list and B_list have some common elements, then the result will
   be a list with no common elements *)
fun append_no_dup (A_list, B_list) =
    let fun helper (A::As) B_list As_to_add =
            if tmem A B_list then helper As B_list As_to_add
            else helper As B_list (A::As_to_add)
          | helper [] B_list As_to_add = (rev As_to_add)@B_list
    in
        helper A_list B_list []
    end

(* val nth = Sml_system.List.nth *)

(* if ftn_type is a1_ty -> a2_ty ->  ... -> an_ty, this function returns
   the "argument" types, [a1_ty, a2_ty, ... a(n-1)_ty] *)
fun get_arg_types ftn_type =
    let fun helper the_type arg_types =
        let val (tyop, args) = dest_type the_type
        in
            if (tyop = "fun") andalso (args <> []) then
                helper (nth (args, 1)) ((hd args)::arg_types)
            else
                rev arg_types
        end
    in helper ftn_type []
    end

(* This makes sure that a list of variables are different from some set
   of variables to avoid, as well as each other. Send in the list of vars
   you want to have distinct names as (var::vars), [] as new_vars, and
   the variables to avoid as vars_to_avoid *)
fun ensure_vars_different (var::vars) new_vars vars_to_avoid =
    let val new_var = Term.variant vars_to_avoid var
    in
        ensure_vars_different vars (new_var::new_vars)
        (new_var::vars_to_avoid)
    end
  | ensure_vars_different [] new_vars _ = rev new_vars

fun foldr ftn base (b::bs) = ftn (b, (foldr ftn base bs))
  | foldr ftn base [] = base

(* takes all existential variables in goal, and instantiates
   them to the same variable *)
fun multi_var_exists (asm, gl) =
    let val (vars, tm) = strip_exists gl
    in
        foldr
        (fn (var, tac) => (EXISTS_TAC var) THEN tac)
        ALL_TAC
        vars
        (asm, gl)
    end;

(* first goal -- break down the term and check it *)
val (relations, vars_list) = foldr
    (fn (tm, (rels, vars)) => let val (rel, more_vars) = strip_comb tm
     in (rel::rels, (ensure_vars_different more_vars [] [])::vars) end)
     ([], []) patterns

val orig_rules = strip_conj rules_term
val all_variables = all_vars rules_term

(* relations are variables at this point *)
fun relations_in_tm tm =
    if is_var tm then tmem tm relations else
    if is_const tm then false else
    if is_abs tm then relations_in_tm (body tm) else
    (* must be comb *)
        let val (t1, t2) = dest_comb tm in
            relations_in_tm t1 orelse relations_in_tm t2
        end

(* this function makess sure that the rules are of the form needed *)
fun check_rule rule_num rule =
    let fun check_hyp (hyp1::hyps) =
            let val (rator, rands) = strip_comb hyp1 in
                if tmem rator relations then
                    (* check that the relations don't occur in rands *)
                    if (foldr (fn (tm, acc) => relations_in_tm tm orelse acc)
                        false rands) then
                      raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                        ("found relation being defined"^
                          " in arg to "^(fst(dest_var rator))^
                          " in hypothesis ofrule number "^
                          (Lib.int_to_string rule_num))
                    else check_hyp hyps
                else if relations_in_tm hyp1 then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("found relation being defined"^
                     " in side condition in rule number "^
                     (Lib.int_to_string rule_num))
                else check_hyp hyps
            end
          | check_hyp [] = true
        fun check_concl tm =
            let val (rator, rands) = strip_comb tm in
                if not (tmem rator relations) then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("must have relation as operator in "^
                     "conclusion of rule "^(Lib.int_to_string rule_num))
                else if
                  foldr (fn (tm, acc) => relations_in_tm tm orelse acc) false rands
                then
                  raise mk_HOL_ERR "define_inductive_relations" "check_rule"
                    ("found relation being defined"^
                     " in arg to "^(fst(dest_var rator))^
                     " in conclusion of rule number "^
                     (Lib.int_to_string rule_num))
                else true
            end
    in
        if is_imp rule then
            let val (hyp1, conc) = dest_imp rule in
                check_hyp (strip_conj hyp1) andalso
                check_concl conc
            end
        else
            check_concl rule
    end

fun check_rules rule_num (rule::rules) =
    check_rule rule_num rule andalso check_rules (rule_num + 1) rules |
    check_rules _ [] = true

val _ = check_rules 0 orig_rules

(* now sort the rules according to the relation that they are for *)
fun rule_defines_relation rule relation =
    if is_imp rule then
      relation ~~ fst (strip_comb (snd (dest_imp rule)))
    else
      relation ~~ fst (strip_comb rule)

val sorted_rules = map
    (fn rel => (filter (fn x => rule_defines_relation x rel) orig_rules))
    relations

(* put the rules back together into one list *)
val rules = foldr (fn (l1, l2) => l1@l2) [] sorted_rules

(* now quantify the rules -- that is, universally quantify vars in
   conclusion and existentially those in the hypothesis *)
fun quantify_rule rule =
    if is_imp rule then
        let val (t1, t2) = dest_imp rule
            val vars_in_t2 = filter (fn v => not (tmem v relations))
                (free_vars t2)
            val total_vars = vars_in_t2@relations
            val vars_in_t1 = filter
                (fn v => not (tmem v total_vars)) (free_vars t1)
            val new_t1 = list_mk_exists (rev vars_in_t1, t1)
            val new_imp = mk_imp (new_t1, t2)
        in
            list_mk_forall (rev vars_in_t2, new_imp)
        end
    else
        let val vars_in_rule = filter
            (fn v => not (tmem v relations)) (free_vars rule)
        in
            list_mk_forall (rev vars_in_rule, rule)
        end

val new_rules = map quantify_rule rules
val num_rules = length new_rules

(* now put together the terms that we need to define the relations *)

val predicate = list_mk_abs (relations, list_mk_conj new_rules)

fun add_poss var =
    let val (n, t) = dest_var var in
        mk_var ("poss_"^n, t)
    end

val poss_relations = ensure_vars_different (map add_poss relations) []
    all_variables

val applied_pred = list_mk_comb (predicate, poss_relations)
val vars_to_avoid = poss_relations@all_variables

fun define_relations (vars::more_vars) (reltn::more_reltns)
    (poss_rel::more_poss) =
    let val applied_poss = list_mk_comb (poss_rel, vars)
        val impli = mk_imp (applied_pred, applied_poss)
        val quant = list_mk_forall (poss_relations, impli)
        val applied_reltn = list_mk_comb (reltn, vars)
        val def = mk_eq (applied_reltn, quant)
    in
        (new_definition ((fst (dest_var reltn))^"_DEF", def))::
        (define_relations more_vars more_reltns more_poss)
    end
  | define_relations _ _ _ = []

(* define all the relations *)
val the_definitions = define_relations vars_list relations poss_relations

(* the next goal is to prove that relations we've defined satisfy
   the rules *)

(* these are the constants we've defined *)
val relatn_consts = map (mk_const o dest_var) relations

(* The idea with the following three functions is that I use
   information in the rule corresponding to this goal to tell me how I
   ought to solve the goal. The count parameters keeps track of what
   rule we're currently operating on, so I can just grab the
   appropriate assumption and ASSUME it rather than using FIRST_ASSUM
   to find it for me. This idea is that it ought to go somewhat faster
   that way. *)

fun mk_more_tactics num_hyps count (hyp1::hyps) =
    let val (rator, rands) = strip_comb hyp1
        fun mk_still_more_tactics count =
            if count < num_rules + num_hyps then
                (fn (asms, gl) =>
                 let val rule_thm = ASSUME (nth (rev asms, count))
                 in
                     (ACCEPT_TAC rule_thm) (asms, gl)
                 end)::mk_still_more_tactics (count + 1)
            else []
        (* new_rules have vars for relations *)
        val is_sentence = tmem rator relations
        val yet_more_tactics =
            if is_sentence then mk_still_more_tactics num_hyps
            else []
    in
        fn (asms, gl) =>
        let val rule_thm = ASSUME (nth (rev asms, count))
        in
            if is_sentence then
                (MP_IMP_TAC (SPEC_ALL rule_thm) THEN
                 REPEAT CONJ_TAC THENL yet_more_tactics) (asms, gl)
            else
                (ACCEPT_TAC rule_thm) (asms, gl)
        end
    end::mk_more_tactics num_hyps (count + 1) hyps
  | mk_more_tactics _ _ [] = []

fun mk_tactics count (rule::rules) =
    let val (forall_vars, body_tm) = strip_forall rule
        val is_an_imp = is_imp body_tm
        val hyp1 = if is_an_imp then fst (dest_imp body_tm) else “T”
        val (exists_vars, hyp2) = if is_an_imp then strip_exists hyp1
                                  else ([], “T”)
        val hyps = if is_an_imp then strip_conj hyp2 else []
        val hyp_count = length hyps
        val more_tactics =
            if is_an_imp then
                mk_more_tactics hyp_count 0 hyps
            else []
    in
        if not is_an_imp andalso null forall_vars then
          (mk_tactics (count + 1) rules)
        else
            (fn (asms, gl) =>
             let val rule_thm = ASSUME (nth (rev asms, hyp_count + count))
             in
                 if is_an_imp then
                     (MP_IMP_TAC (SPEC_ALL rule_thm) THEN
                      multi_var_exists THEN
                      REPEAT CONJ_TAC THENL more_tactics) (asms, gl)
                 else
                     ACCEPT_TAC (SPEC_ALL rule_thm) (asms, gl)
             end)::(mk_tactics (count + 1) rules)
    end
  | mk_tactics _ [] = []

val tactics = mk_tactics 0 new_rules

(* do the proof that the relations so defined do
   indeed satisfy the rules *)
val first_rules_sat = TAC_PROOF
    (([], list_mk_comb (predicate, relatn_consts)),
     BETA_TAC THEN REPEAT CONJ_TAC THEN
     PURE_REWRITE_TAC the_definitions THEN BETA_TAC THEN
     REPEAT STRIP_TAC THENL tactics)

val rules_sat = BETA_RULE first_rules_sat

(* the next goal is to define and prove the induction theorem *)

fun mk_prop_vars count (rel::rels) =
    mk_var ("P_"^(Lib.int_to_string count),
            snd (dest_var rel)) :: mk_prop_vars (count + 1) rels
  | mk_prop_vars _ [] = []

val all_arg_vars = foldr
    (fn (vars, more_vars) => append_no_dup (vars, more_vars)) [] vars_list

val prop_vars = ensure_vars_different
    (mk_prop_vars 0 relations) [] all_arg_vars

fun mk_conjuncts (vars::more_vars) (con::more_cons)
    (prop_var::more_props) =
    let val impl = mk_imp (list_mk_comb (con, vars),
                           list_mk_comb (prop_var, vars))
        val quantified = list_mk_forall (vars, impl)
    in
        quantified::(mk_conjuncts more_vars more_cons more_props)
    end
  | mk_conjuncts _  _ _ = []

val conjuncts = list_mk_conj
    (mk_conjuncts vars_list relatn_consts prop_vars)

val applied_pred2 = list_mk_comb (predicate, prop_vars)

val induction_thm_term = list_mk_forall
    (prop_vars, mk_imp (applied_pred2, conjuncts))

fun finish_tac (asms, gl) =
    let val thm1 = SPECL prop_vars (ASSUME (hd asms))
        val thm2 = ASSUME (nth (asms, 1))
    in
        (MP_IMP_TAC thm1 THEN ACCEPT_TAC thm2) (asms, gl)
    end

val ind_thm1 = TAC_PROOF
    (([], induction_thm_term),
     BETA_TAC THEN PURE_REWRITE_TAC the_definitions THEN BETA_TAC THEN
     REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
     REPEAT GEN_TAC THEN DISCH_TAC THEN finish_tac)

val ind_thm2 = BETA_RULE ind_thm1

in
    (rules_sat, ind_thm2)
end





(* prove_inversion_theorems proves the "case analysis" or "inversion"
   theorems for a given set of rules defining mutually recursive inductive
   relations. Basically, given the two theorems returned by
   define_inductive_relations (that is, the theorems stating that the
   relations satisfy the rules and the induction theorem, in that order),
   it returns a list of theorems, one for each relation. These theorems have
   the form:
             |- !<argvars>. rel <args> = <big disjunction>
   where in the big disjunction, there is one disjunct for each rule
   pertaining to the relation rel. The form of each disjunct is
             ?evars. (var1 = term1) /\ ... /\ (varn = termn) /\ hyp
   where each vari is one of the argvars, and each termi consists of
   constants and vars from evars, and hyp is the hypothesis of the rule.
   Well, actually, the hypothesis of the rule actually has the form
             (? vars. t1 /\ ... /\ tk)
   In the disjunct, the vars will be among the evars, and hyp will be
   just t1 /\ ... /\ tk. *)

fun prove_inversion_theorems rules_sat ind_thm =

let

(* Based strongly on Tom Melham's package, as translated by Konrad Slind.
   The complicated-looking comments are grabbed verbatim from that code. *)

(* --------------------------------------------------------------------- *)
(*  |- ~~P                                                               *)
(* --------  NOT_NOT                                                     *)
(*   |- P                                                                *)
(* --------------------------------------------------------------------- *)
fun NOT_NOT th =
    CCONTR (dest_neg(dest_neg (concl th))) (UNDISCH th);

fun LIST_EXISTS_THEN f th =
   let val (vs,body) = strip_exists(concl th)
       val th1 = DISCH body (f (ASSUME body))
   in MP (itlist EXISTS_IMP vs th1) th
   end;

fun RULE thm1 thm2 =
   let val (xs,imp) = strip_exists (concl thm1)
       val thm =  SPECL xs thm2
       val impth = MP (ASSUME imp) thm
       val iimp = DISCH imp impth
   in MATCH_MP (itlist EXISTS_IMP xs iimp) thm1
   end;

(* --------------------------------------------------------------------- *)
(* EXISTS_IMP2 : existentially quantify the antecedent and conclusion    *)
(* of an implication.                                                    *)
(*                                                                       *)
(*        A |- P ==> Q                                                   *)
(* -------------------------- EXISTS_IMP "x"                             *)
(*   A |- (?x.P) ==> (?x.Q)                                              *)
(*                                                                       *)
(* LIKE built-in, but doesn't quantify in Q if not free there.           *)
(* Actually, used only in context where x not free in Q.                 *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)
fun EXISTS_IMP2 x th =
   let val (ant,conseq) = dest_imp(concl th)
   in if (free_in x conseq)
   then let val th1 = EXISTS (mk_exists(x,conseq),x) (UNDISCH th)
            val asm = mk_exists(x,ant)
        in DISCH asm (CHOOSE (x,ASSUME asm) th1)
        end
   else let val asm = mk_exists(x,ant)
        in DISCH asm (CHOOSE (x,ASSUME asm) (UNDISCH th))
        end
   end;

fun efn v th =
    if (free_in v (concl th))
    then EXISTS(mk_exists(v,concl th),v) th
    else th;

fun mk_new_subst L2 L1 =
   map2 (fn rdx => fn rsd => {redex=rdx,residue=rsd}) L1 L2;

fun RULE2 vs thm1 thm2 =
   let val (xs,P) = strip_exists(concl thm1)
       val (ys,Q) = strip_exists(concl thm2)
       fun itfn v vs =  let val v' = Term.variant (vs @ xs) v
                        in (v'::vs)
                        end
       val ys' = itlist itfn ys []
       val Q' = subst(mk_new_subst ys' ys) Q
       val asm = CONJ (ASSUME P) (ASSUME Q)
       val cs = LIST_CONJ (CONJUNCTS asm)
       val vs = filter (C free_in (concl cs)) (xs @ ys')
       val eth = MP (itlist EXISTS_IMP2 xs (DISCH P (itlist efn vs cs))) thm1
       val ethh = MP (itlist EXISTS_IMP2 ys' (DISCH Q' eth)) thm2
   in  ethh
   end;

(* ---------------------------------------------------------------------*)
(* INTERNAL FUNCTION : LIST_NOT_FORALL                                  *)
(*                                                                      *)
(* If:                                                                  *)
(*             |- ~P                                                    *)
(*        --------------- f : thm->thm                                  *)
(*         |- Q  |- R                                                   *)
(*                                                                      *)
(* Then:                                                                *)
(*                                                                      *)
(*   |-  ~!x1 ... xi. P                                                 *)
(*  ----------------------------                                        *)
(*   |-  ?x1 ... xi. Q    |- R                                          *)
(* ---------------------------------------------------------------------*)
local
fun efn v th =  EXISTS(mk_exists(v,concl th),v) th
in
fun LIST_NOT_FORALL f th =
   let val (vs,body1) = strip_forall (dest_neg (concl th))
   in if (null vs)
      then f th
      else let val (Q,R) = f (ASSUME(mk_neg body1))
               val nott = itlist efn vs Q
               val thm = CCONTR body1 (MP (ASSUME (mk_neg (concl nott))) nott)
           in (CCONTR (concl nott) (MP th (GENL vs thm)), R)
           end
   end
end;

local
fun chfn v (a,th) =
   let val tm = mk_exists(v,a)
   in (tm,CHOOSE (v,ASSUME tm) th)
   end
in
fun simp_axiom sfn vs ax th =
   let (* imp has form ~~(rel args ==> eqtns) |- rel args ==> eqtns *)
       val imp = NOT_NOT th
       (* ant = rel args, conseq = eqtns *)
       val (ant,conseq) = dest_imp (concl imp)
       val eqs = strip_conj conseq
       (* avs = forall_vars, res = rel args *)
       val (avs,res) = strip_forall (concl ax)
       val this_rel = fst (strip_comb res)
       (* inst is |- rel <args as in th, not as in ax> *)
       val inst = INST (fst(match_term res ant)) (SPECL avs ax)
       (* ths is ~~(rel args ==> eqtns) |- eqtns *)
       val ths = MP imp inst
       (* thm is eqtns |- rel <args from lhs eqtns> *)
       val thm = sfn (ASSUME(concl ths)) this_rel inst
       (* rthm is |- (?<vs>. eqtns) ==> rel <args from lhs eqtns> *)
       val rth = (uncurry DISCH) (itlist chfn vs ((concl ths),thm))
   in (ths,rth)
   end
end;

(* relations are constants *)
fun rel_in_term rel tm =
    if is_var tm then false else
    if is_const tm then rel ~~ tm else
    if is_abs tm then rel_in_term rel (body tm) else
    (* must be comb *)
        let val (t1, t2) = dest_comb tm in
            (rel_in_term rel t1) orelse (rel_in_term rel t2)
        end

fun foldr ftn base (b::bs) = ftn (b, (foldr ftn base bs))
  | foldr ftn base [] = base

(* The form of tm is (?exists_vars. t1 /\ ... /\ tn), where some of the
   ti have the form ~(rel args ==> some_term). This function proves:
       (?exists_vars. t1 /\ ... /\ tn) |-
           (?exists_vars. t1' /\ ... /\ tn')
   where if ti has form ~(rel args ==> some_term), then ti' has
   form (rel args), OW ti' = ti *)
local
    fun mk_1_imp rel hyp =
        if not (rel_in_term rel hyp) then
            ASSUME hyp
        else
            CONJUNCT1 (PURE_REWRITE_RULE [NOT_IMP] (ASSUME hyp))
in
fun mk_implication rel tm =
    let
        val (term_exists_vars, tm2) = strip_exists tm
        val term_conjs = strip_conj tm2
        (* imp_thms says, for each i, ti |- ti' *)
        val imp_thms = map (mk_1_imp rel) term_conjs
        (* imp_thm has form [t1, ... , tn] |- t1' /\ ... /\ tn' *)
        val imp_thm = LIST_CONJ imp_thms
        (* need to get thm of form
           t1 /\ ... /\ tn |- t1' /\ ... /\ tn' -- this is imp_thm2 *)
        val imp_thm2 = foldr (fn (thm1, thm2) => PROVE_HYP thm1 thm2)
             imp_thm (CONJUNCTS (ASSUME tm2))
    in
        (* now existentially quantify over the variables in hyp and concl *)
        UNDISCH (foldr (fn (var, thm) => EXISTS_IMP var thm)
             (DISCH_ALL imp_thm2) term_exists_vars)
    end
end

local
  val rule = NOT_NOT o CONV_RULE(RAND_CONV LIST_BETA_CONV)
  fun chfn v (a,th) =
     let val tm = mk_exists(v,a)
     in (tm,CHOOSE (v,ASSUME tm) th)
     end
  and efn v th = EXISTS(mk_exists(v,concl th),v) th
in
fun simp_rule sfn set vs rul th =
   let (* c1 = antecedant of term, c2 = conseq of term where term is
          roughly the conclusion of th, is term corresponding with rul *)
       val (c1,c2) = CONJ_PAIR (CONV_RULE (REWR_CONV NOT_IMP) th)
       (* th1 is rel <args from term> ==> eqtns *)
       val th1 = NOT_NOT c2
       val imp = concl th1
       (* gvs is forall_vars in rule, cnc is rel <args from rule> *)
       val (gvs,cnc) = (I ## rand) (strip_forall(concl rul))
       (* th3 = <antecedent of rule> |- <concl of rule> *)
       val th3 = UNDISCH (SPECL gvs rul)
       (* pat is rel <args from term> *)
       val pat = fst(dest_imp imp)
       val this_rel = fst (strip_comb pat)
       (* change conjuncts of form ~(rel args ==> eqtns) to (rel args) *)
       val th2 = if (rel_in_term this_rel (concl c1)) then
           PROVE_HYP c1 (mk_implication this_rel (concl c1))
           else c1
       (* inst is substitution that replaces rule vars with vars from term *)
       val inst = fst(match_term (concl th3) pat)
       (* th_a is rule with vars from term instead of original vars *)
       val th_a = INST inst (DISCH_ALL th3)
       (* rins is term |- <concl of rule, with vars from term> *)
       (* The line below used to use MATCH_MP, not MP. I can't see how
          th_a could be universally quantified, and it caused a bug by
          MATCH_MP sticking primes on things where they didn't belong,
          so it's now just MP. If there's a problem here, this may need to
          be looked into more closely *)
       val rins = MP th_a th2
       (* erins is <ant of rule> |- <concl of rule, with vars from term> *)
       (* MP below used to be MATCH_MP, see note above *)
       val erins = MP th_a (ASSUME (concl th2))
       (* eqns is term |- eqtns *)
       val eqns = RULE th1 rins
       (* eths is eqtn terms *)
       val eths = strip_conj (concl eqns)
       (* thm is [eqtns, <hyp of rule>] |- rel <args from term> *)
       val thm = sfn (LIST_CONJ (map ASSUME eths)) this_rel erins
       (* vv is existential vars in hypothesis, cs = conjs in hypothesis *)
       val (vv,cs) = (I ## strip_conj) (strip_exists(concl th2))
       (* thx is same as thm, except with conjs in <hyp of rule> broken up *)
       val thx = PROVE_HYP (itlist efn vv (LIST_CONJ (map ASSUME cs))) thm
       (* simp_thm = term |- ?exists_vars. eqtns /\ hpy *)
       val simp_thm = RULE2 vs eqns th2
       (* nevs, cn are exists_vars, big_conj of simp_thm *)
       val (nevs,cn) = strip_exists(concl simp_thm)
       val hys = CONJUNCTS (ASSUME cn)
       val (hh,nthm) = itlist chfn nevs (cn,itlist PROVE_HYP hys thx)
       val res = (uncurry DISCH) (itlist chfn vs (hh,nthm))
   in (PROVE_HYP th simp_thm, res)
   end
end;

fun bad_error ftn_name =
  raise mk_HOL_ERR "prove_inversion_theorems" ftn_name
    "this case should never happen, real problem here!"

fun simp set sfn rul th =
   let val vs = fst(strip_forall (dest_neg (concl th)))
       val rule_body = snd (strip_forall (concl rul))
   in
       if is_imp rule_body then
           LIST_NOT_FORALL (simp_rule sfn set vs rul) th
       else
           LIST_NOT_FORALL (simp_axiom sfn vs rul) th
   end;

fun last [a] = a
  | last (_::rst) = last rst
  | last [] = bad_error "last"

fun butlast [_] = []
  | butlast (h::t) = h::(butlast t)
  | butlast [] = bad_error "butlast"

local
    val thms = CONJUNCTS (SPEC_ALL AND_CLAUSES)
in
    val T_and_clauses = GEN_ALL (CONJ (hd thms) (hd (tl thms)))
end

exception mymap2_ERR;
fun mymap2 ([],[]) = []
  | mymap2 ([],_)  = raise mymap2_ERR
  | mymap2 (_,[])  = raise mymap2_ERR
  | mymap2 ((h1::rst1),(h2::rst2)) =
    mk_eq(h1,h2)::mymap2(rst1,rst2);

fun divide_by_numbers (0::nums) elts partial_list full_lists =
    divide_by_numbers nums elts [] ((rev partial_list)::full_lists)
  | divide_by_numbers (num::nums) (elt::more_elts) partial_list full_lists =
    divide_by_numbers ((num-1)::nums) more_elts (elt::partial_list)
        full_lists
  | divide_by_numbers _ _ _ full_lists = rev full_lists

local
  val v1 = genvar(==`:bool`==)
  and v2 = genvar(==`:bool`==)
  val thm = fst(EQ_IMP_RULE(CONJUNCT1 (SPECL [v1,v2] DE_MORGAN_THM)))
  fun IDISJ th1 th2 =
     let val di = mk_disj(rand(rator(concl th1)),
                          rand(rator(concl th2)))
     in DISCH di (DISJ_CASES (ASSUME di) (UNDISCH th1) (UNDISCH th2))
     end
  fun ITDISJ th1 th2 =
     let val (hy1,cl1) = dest_thm th1
         and (hy2,cl2) = dest_thm th2
         val _ = if not(length hy1 = 1) then raise Match else ()
         val _ = if not(length hy2 = 1) then raise Match else ()
         val dth = UNDISCH (INST [{redex=v1,residue=rand (hd hy1)},
                                  {redex=v2,residue=rand (hd hy2)}] thm)
     in DISJ_CASES_UNION dth th1 th2
     end
in
fun LIST_DE_MORGAN f rules fthm  =
   let val conjs2 = strip_conj (dest_neg (concl fthm))
       val (ts1,ts2) = split (map2 (fn r => fn t => f r (ASSUME(mk_neg t)))
                                   rules conjs2)
   in
       (PROVE_HYP fthm (end_itlist ITDISJ ts1), end_itlist IDISJ ts2)
   end
end

(* val nth = List.nth *)

fun DISCH_nth n thm1 =
    let val asms = fst (dest_thm thm1) in
        DISCH (nth (asms, n)) thm1 end

fun elim_nth n (item::items) =
    if (n = 0) then items
    else item::(elim_nth (n - 1) items)
  | elim_nth n _ = []

(* the goal here is to prove |- tm = T. I have |- rule so the goal is to
   prove |- rule ==> tm, then get |- tm, then |- tm = T *)
fun process_rule rel tm rule =
    (* the form of tm is
       !forall_vars.
        (?exists_vars. hyp1 /\ ... /\ hypn) ==> some_rel args
       the form of rule is
       |- !forall_vars.
        (?exists_vars. hyp1' /\ ... /\ hypn') ==> some_rel args
       where for side conditions and hyps not involving rel, hypi = hypi',
       but for others, hypi = ~(rel argvars ==> (conjunction of equations))
       and hypi' = rel argvars. *)
    let val (forall_vars, term_body) = strip_forall tm
        val speced_rule = SPECL forall_vars rule
        val (term_ant, term_conseq) = dest_imp term_body
        (* imp_thm3 says (?exists_vars. hyp1 /\ ... /\ hypn) |-
                         (?exists_vars. hyp1' /\ ... /\ hypn') *)
        val imp_thm3 = mk_implication rel term_ant
        (* imp_thm4 says
           |- (?exists_vars. hyp1 /\ ... /\ hypn) ==> some_rel args *)
        val imp_thm4 = DISCH_ALL (MP speced_rule imp_thm3)
        (* now quantify over the forall_vars *)
        val proved_term = GENL forall_vars imp_thm4
        (* now introduce T to get |- tm = T *)
    in
        EQT_INTRO proved_term
    end

(* process_term is geven a term and a rule, and is expected to return a
   theorem saying |- tm = T *)
fun process_term rel tm rule =
    let val (forall_vars, rule_body) = strip_forall (concl rule)
    in
        if not (is_imp rule_body) orelse not (rel_in_term rel tm) then
            EQT_INTRO rule
        else
            process_rule rel tm rule
    end

(* assemble a list of props such that only the one referring to this
   relation is something other than the relation itslef *)
fun assemble_preds count (pred::more_preds) (rel::more_rels) =
    if count = 0 then
        pred::(assemble_preds (count - 1) more_preds more_rels)
    else
        rel::(assemble_preds (count - 1) more_preds more_rels)
  | assemble_preds count _ _ = []

fun subst_in_subst theta =
  map (fn {redex,residue} => {redex=redex, residue = subst theta residue});

(* --------------------------------------------------------------------- *)
(* INTERNAL FUNCTION : reduce                                           *)
(*                                                                      *)
(* A call to                                                            *)
(*                                                                      *)
(*   reduce [v1;...;vn] ths [] []                                       *)
(*                                                                      *)
(* reduces the list of theorems ths to an equivalent list by removing   *)
(* theorems of the form |- vi = ti where vi does not occur free in ti,   *)
(* first using this equation to substitute ti for vi in all the other   *)
(* theorems. The theorems in ths are processed sequentially, so for     *)
(* example:                                                             *)
(*                                                                      *)
(*   reduce [a;b] [|- a=1; |- b=a+2; |- c=a+b] [] []                    *)
(*                                                                      *)
(* is reduced in the following stages:                                  *)
(*                                                                      *)
(*   [|- a=1; |- b=a+2; |- c=a+b]                                       *)
(*                                                                      *)
(*   ===> [|- b=1+2; |- c=1+b]      (by the substitution [1/a])         *)
(*   ===> [|- c=1+(1+2)]            (by the substitution [1+2/b])       *)
(*                                                                      *)
(* The function returns the reduced list of theorems, paired with a list *)
(* of the substitutions that were made, in reverse order.  The result   *)
(* for the above example would be [|- c = 1+(1+2)],[("1+2",b);("1",a)]. *)
(* --------------------------------------------------------------------- *)
fun reduce vs ths res subf =
   if (null ths)
   then (rev res, subf)
   else let val (lhs,rhs) = dest_eq(concl(hd ths))
            val (sth,pai) = if tmem lhs vs
                            then (hd ths,{redex=lhs,residue=rhs})
                            else if tmem rhs vs
                                 then (SYM(hd ths),{redex=rhs,residue=lhs})
                                 else bad_error ("reduce")
        in if (free_in (#redex pai) (#residue pai))
           then bad_error ("reduce")
           else let val sfn = map (SUBS [sth])
                    val ssfn = subst_in_subst [pai]
                in reduce vs (sfn (tl ths)) (sfn res) (pai::ssfn subf)
                end
        end
        handle _ => reduce vs (tl ths) (hd ths::res) subf

fun subst_assoc tm =
   let fun assc [] = NONE
         | assc ({redex,residue}::rst) =
            if tm ~~ redex then (SOME residue)
            else assc rst
   in assc
   end;

(* --------------------------------------------------------------------- *)
(* REDUCE : simplify an existentially quantified conjuction by          *)
(* eliminating conjuncts of the form |- v=t, where v is among the       *)
(* quantified variables and v does not appear free in t. For example    *)
(* suppose:                                                             *)
(*                                                                      *)
(*   tm = "?vi. ?vs. C1 /\ ... /\ v = t /\ ... /\ Cn"                   *)
(*                                                                      *)
(* then the result is:                                                  *)
(*                                                                      *)
(*   |- (?vi. ?vs. C1 /\ ... /\ vi = ti /\ ... /\ Cn)                   *)
(*          =                                                           *)
(*      (?vs. C1[ti/vi] /\ ... /\ Cn[ti/vi])                            *)
(*                                                                      *)
(* The equations vi = ti can appear as ti = vi, and all eliminable      *)
(* equations are eliminated.  Fails unless there is at least one        *)
(* eliminable equation. Also flattens conjuncts. Reduces term to "T" if *)
(* all variables eliminable.                                            *)
(* ---------------------------------------------------------------------*)
local
fun chfn v (a,th) =
   let val tm = mk_exists(v,a)
       val th' = if (free_in v (concl th))
                 then EXISTS (mk_exists(v,concl th),v) th
                 else th
   in (tm,CHOOSE (v,ASSUME tm) th')
   end
fun efn ss v (pat,th) =
   let val wit = case (subst_assoc v ss)
                   of NONE => v
                    | (SOME residue) => residue
       val ex = mk_exists(v,pat)
       val epat = subst ss ex
   in (ex,EXISTS(epat,wit) th)
   end
fun prove ths cs =
   (uncurry CONJ ((prove ths ## prove ths) (dest_conj cs)))
   handle _
   => (Lib.first (fn t => concl t ~~ cs) ths)
   handle _
   => (REFL (rand cs))
in
fun REDUCE tm =
   let val (vs,cs) = strip_exists tm
       val (remn,ss) = reduce vs (CONJUNCTS (ASSUME cs)) [] []
   in if (null ss)
      then bad_error ("REDUCE")
      else let val th1 = LIST_CONJ remn handle _ => TRUTH
               val th2 = (uncurry DISCH) (itlist chfn vs (cs,th1))
               val (rvs,rcs) = strip_exists(rand(concl th2))
               val eqt = subst ss cs
               val th3 = prove (CONJUNCTS (ASSUME rcs)) eqt
               val (_,th4) = itlist (efn ss) vs (cs,th3)
               val th5 = (uncurry DISCH) (itlist chfn rvs (rcs,th4))
           in IMP_ANTISYM_RULE th2 th5
           end
   end
end;

(* Here the computations begin *)

val rule_thms = CONJUNCTS rules_sat

(* the first goal is to come up with terms representing the properties
   that we want. *)

(* props is variables for properties *)
val (props, tm1) = strip_forall (concl ind_thm)
(* ind_ant says properties satisfy rules, ind_conseq say that, for each
   relation, !<argvars>. rel <argvars> ==> P <argvars> *)
val (ind_ant, ind_conseq) = dest_imp tm1

(* collect together the argvars -- the vars the relations are applied to
   in the conclusion of the induction thm *)
val (argvars, imps) = foldr
    (fn (tm, (vars, imps)) => let val (more_vars, an_imp) = strip_forall tm in
     (more_vars::vars, an_imp::imps) end) ([], []) (strip_conj ind_conseq)

(* now name them differently, so we have no clashes among var names,
   also name them to be different from the existentially
   quantified vars in the rules *)
val exists_vars = foldr
    (fn (tm, vars) =>
     let val b1 = snd (strip_forall tm)
         val not_axiom = is_imp b1
         val more_vars =
             if not_axiom then
                 fst (strip_exists (fst (dest_imp b1)))
             else []
     in
         if not_axiom then more_vars@vars else vars
     end) [] (map concl rule_thms)
fun rename_vars (vars::more_vars) vars_to_avoid renamed_vars =
    let fun do_one_bunch_vars (var::more_var) used_vars new_vars =
            let
                val tmp_var = Term.variant used_vars var
            in do_one_bunch_vars more_var (tmp_var::used_vars)
                (tmp_var::new_vars)
            end
          | do_one_bunch_vars _ _ new_vars = rev new_vars
        val new_vars = do_one_bunch_vars vars vars_to_avoid []
    in
        rename_vars more_vars (new_vars@vars_to_avoid) (new_vars::renamed_vars)
    end
  | rename_vars [] _ renamed_vars = rev renamed_vars
val renamed_argvars = rename_vars argvars exists_vars []

(* replace the vars in imps with renamed vars
   each item in new_imps has form:   rel <argvars> = prop argvars *)
fun modify_imps (old_vars::more_old) (new_vars::more_new)
    (imp::more_imps) =
    (subst (mk_new_subst new_vars old_vars) imp)::
    modify_imps more_old more_new more_imps
  | modify_imps _ _ _ = []
val new_imps = modify_imps argvars renamed_argvars imps

(* info_list is an association list with, for each relation, the
   argvars and hypothesis (which is rel <argvars>) *)
val info_list = map2
    (fn vars => fn imp =>
     let val hyp = rand (rator imp)
         val rel = fst (strip_comb hyp) in
         (rel, (vars, hyp)) end)
    renamed_argvars new_imps
(* sfn is used to substitute vars used in rules for vars used in terms
   in conclusion of thm4 below *)
fun sfn eqs rel =
    let val (argvars, hyp) = tassoc rel info_list
    in
(* following line changed by PVH Feb 3, 2000 from {var=v, thm=th} *)
        SUBST(map2 (fn th => fn v => {redex=v, residue=th})
              (map SYM (CONJUNCTS eqs)) argvars) hyp
    end

(* list of relations *)
val set = map fst info_list

(* divide up the rules according to which relation it's for *)
fun has_this_rel rel thm1 =
    let val bdy = snd (strip_forall (concl thm1))
        val applied_rel =
            if is_imp bdy then
                snd (dest_imp bdy)
            else bdy
    in
        rel ~~ fst (strip_comb applied_rel)
    end
val divided_rules = map
    (fn rel => (filter (fn thm1 => has_this_rel rel thm1) rule_thms)) set

(* specialize ind_thm to prop vars *)
val tmp_thm1 = UNDISCH (SPECL props ind_thm)
(* imp_thms = theorems saying rel <argvars> ==> prop <argvars> *)
val imp_thms = map2 (fn vars => fn theorem => SPECL vars theorem)
    renamed_argvars (CONJUNCTS tmp_thm1)
(* speced_ind = induction with foralls for props and argvars removed *)
val speced_ind = DISCH_nth 0
    (foldr (fn (thm1, thm2) => CONJ thm1 thm2)
      (last imp_thms) (butlast imp_thms))

(* find number of rules for each relation *)
val rules_count = map length divided_rules

(* genvars contains, for each var in renamed_argvars, a
   corresponding genvar *)
val genvars = map (fn vars => map (genvar o type_of) vars)
    renamed_argvars

(* make the predicates. there is one for each relation, it looks like
   \<genvars>. ~(rel <genvars> ==>
                 (argvar_1 = genvar_1) /\ ... /\ (argvar_n = genvar_n)) *)
fun mk_preds (gen_vars::more_gens) (arg_vars::more_args)
    (thm1::more_thms) =
    let val eqtns = list_mk_conj (mymap2 (arg_vars, gen_vars))
        val theta = map2 (fn r1 => fn r2 => {redex=r1,residue=r2})
            arg_vars gen_vars
        val assum = subst theta (rator (concl thm1))
        val pred = list_mk_abs
            (gen_vars, mk_neg (mk_comb (assum, eqtns)))
    in
        pred::(mk_preds more_gens more_args more_thms)
    end
  | mk_preds _ _ _ = []

val preds = mk_preds genvars renamed_argvars imp_thms

val hyps = map (rand o rator) new_imps

fun mk_inversion_thms count all_rels (hyp::hyps) (vars::more_vars) =
    let val new_preds = assemble_preds count preds all_rels
        val rel = nth (all_rels, count)
        val theta = map2 (fn prop_var => fn pred =>
                          {redex = prop_var, residue = pred}) props new_preds
        (* replace P_0, P_1, etc, with the predicates *)
        val thm1 = INST theta speced_ind
        (* get the "preds satisfy rules" term *)
        val preds_sat_rules = fst (dest_imp (concl thm1))
        (* basically, eliminate unwanted conclusions, and put
           "preds satisfy rules" and "rel argvars" into hypotheses *)
        val thm2 = BETA_RULE
            (UNDISCH (nth (CONJUNCTS (UNDISCH thm1), count)))
        (* make the theorem that is contradictory to thm2 *)
        val contr = DISCH hyp (ADD_ASSUM hyp (LIST_CONJ (map REFL vars)))
        (* now do contradiction, getting ~"preds satisfy rules" in
           conclusion *)
        val thm3 = BETA_RULE (NOT_INTRO (DISCH preds_sat_rules
                                         (MP thm2 contr)))
        (* thm3 has form ~(conj1 /\ ... /\ conjn) where each conj
           corresponds to one rule -- need to eliminate conjs that correspond
           to rules that don't apply to this relation *)
        (* grab the conjuncts that don't correspond to this relation *)
        val divided_conjs = divide_by_numbers rules_count
            (strip_conj (dest_neg (concl thm3))) [] []
        (* these are the conjs that we need to get rid of, and the rules
           that correspond with them *)
        val conjs = flatten (elim_nth count divided_conjs)
        val rules = flatten (elim_nth count divided_rules)
        (* get the theorems that say |- conji = T *)
        val rewrites = map2 (process_term rel) conjs rules
        (* rewrite with the |- conji = T and get rid of T conjuncts,
           so now thm4 says ~(predicates satisfy rules), but the conjuncts
           corresponding to rules for other relations have been eliminated *)
        val thm4 = PURE_REWRITE_RULE (T_and_clauses::rewrites) thm3
        (* get the rules pertaining to this relation *)
        val relevant_rules = nth (divided_rules, count)
        (* now do Tom-like munging to get process info to get it in the
           correct form *)
        (* a_thm = assuming rel <argvars>, case disjunctions are true,
           b_thm = case disjunctions ==> rel <arsvars> *)
        val (a_thm, b_thm) = LIST_DE_MORGAN (simp set sfn) relevant_rules thm4
        (* thm5 = rel <argvars> = case disjunctions *)
        val thm5 = IMP_ANTISYM_RULE (DISCH_ALL a_thm) b_thm
        (* ds is a list of thms, each one says
         (disj for rule) = (simplified disj for rule) *)
        val ds = map (QCONV (TRY_CONV REDUCE)) (strip_disj(rand(concl thm5)))
        (* red has form (original distunctions) = (simplified disjunctions) *)
        val red = end_itlist (fn t1 => fn t2 =>
                              MK_COMB (AP_TERM “$\/” t1, t2)) ds
        (* the preceeding line changed from `\/` to `$\/` for Taupo-4
           by PVH, October 19, 2000 *)
        (* final result is that
         !<argvars>. rel <argvars> = (case disjunctions) *)
    in
        (GENL vars (TRANS thm5 red))::
        (mk_inversion_thms (count + 1) all_rels hyps more_vars)
    end
  | mk_inversion_thms _ _ _ _ = []

in

    mk_inversion_thms 0 set hyps renamed_argvars
(* fun mk_inversion_thms count all_rels (hyp::hyps) (vars::more_vars) = *)

end



(* The usual induction theorem states: to prove that
      !<args_1>. rel_1 <args_1> ==> P_1 <args_1> /\ ... **
      !<args_n>. rel_n <args_n> ==> P_n <args_n>
   you need to show that the properties P_0 thru P_n satisfy the
   rules. (Note that since the relations were defined as the smallest
   relations that satisfy the rules, this implies that if some tuple
   is in our relations, then it satisfies any other set of relations
   that satisfy the rules.)
   Each rule looks like this:
      !<vars>.
       (?<vars2>. hyp_1 /\ hyp_2 /\ ... /\ hyp_m) ==>
       rel_k [constants and <vars>]
   where each hyp_i can be either a side condition (not mentioning any
   of the relations) or a hypothesis involving one of the relations,
   that is, be something like
       rel_p [constants and <vars> and <vars2>]
   Let us say that a rule is:
      !<vars>.
       (?<vars2>. SC_1 /\ rel_1 <args_1> /\ rel_3 <args_2> /\ SC_2) ==>
       rel_2 <args_3>
   Thus to show **, you'll need to prove
      !<vars>.
       (?<vars2>. SC_1 /\ P_1 <args_1> /\ P_3 <args_2> /\ SC_2) ==>
       P_2 <args_3>
   The strong induction theorem says that to prove ** you can show
   that the relations satisfy the rules, with the additional
   hypotheses that the relations hold of the args. That is, for our
   hypothetical rule, you'll need to show that:
      !<vars>.
       (?<vars2>. SC_1 /\ P_1 <args_1> /\ rel_1 <args_1> /\
                  P_3 <args_2> rel_3 <args_2> /\ /\ SC_2) ==>
       P_2 <args_3>
   This is theoretically equivalent to the original induction
   principle, in fact it's easily proven from the original and the
   fact that the relations satisfy the rules. The strong induction
   theorem does, however, come in handy if you need some fact about
   the relation to show that the properties satisfy the rules. *)

fun prove_strong_induction rules_sat ind_thm =

let

val (prop_vars, ind_imp) = strip_forall (concl ind_thm)

val conseq_conjs = strip_conj (snd (dest_imp ind_imp))

val vars_relation_list = map
    (fn tm => let val (vars, tm2) = strip_forall tm in
     (vars, fst (strip_comb (fst (dest_imp tm2)))) end)
    conseq_conjs

val relations = map snd vars_relation_list

fun mk_new_prop prop_var (vars, reltn) =
    let val conj = mk_conj (list_mk_comb (prop_var, vars),
                            list_mk_comb (reltn, vars))
    in
        list_mk_abs (vars, conj)
    end

val new_props = map2 mk_new_prop prop_vars vars_relation_list

val new_thm = BETA_RULE (SPECL new_props ind_thm)

(* now we have: modified rules ==> modified concl. We need to eliminate
   unwanted conjuncts from the modified rules and modified concl.
   I'll do the latter first: a conjunct in the concl looks like:
   !<args>. reltn <args> ==> prop_var <args> /\ reltn <args>
   I want it to look like
   !<args>. reltn <args> ==> prop_var <args>
   I'll show that the second implies the first *)

val (mod_rules, mod_concl) = dest_imp (concl new_thm)

fun conjunct_n n th =
    if not (is_conj (concl th)) then th
    else if n = 0 then CONJUNCT1 th
    else conjunct_n (n - 1) (CONJUNCT2 th)

val and_thm = GEN_ALL (conjunct_n 4 (SPEC_ALL AND_CLAUSES))

fun do_one_conjunct tm =
    let val (vars, bod) = strip_forall tm
        val rel_tm = fst (dest_imp bod)
        val thm1 = CONJUNCT1 (UNDISCH (SPEC_ALL (ASSUME tm)))
    in
        DISCH_ALL (GENL vars (DISCH rel_tm thm1))
    end

fun prove_conj_imp (tm::tms) =
    if null tms then do_one_conjunct tm
    else
        let val thm1 = do_one_conjunct tm
            val thm2 = prove_conj_imp tms
        in
            IMP_CONJ thm1 thm2
        end
  | prove_conj_imp [] = REFL “T” (* so SML doesn't complain *)

val concl_thm = prove_conj_imp (strip_conj mod_concl)

(* now to remove unwanted conjuncts from the modified rules. A conjunct
    term here looks like:
   !<vars>. mod_hyp1 /\ mod_hyp2 /\ ... mod_hypn ==>
            prop_var <args> /\ reltn <args>
   where each mod_hypi is a side condition, or has form:
   prop_var <args> /\ reltn <args>
   what I want is to show that this conjunct term is implied by
   !<vars>. (flattened hypotheses) ==> prop_var <args>
   where by flattened hypotheses I mean that the () are removed from the
   mod_hypi's that are not side conditions. *)

(* delete the conjs that don't satisfy pred *)

local
val DISJ_IMP_THM  = GSYM IMP_DISJ_THM
val DISJ_IMP_THM1 = REWRITE_RULE[NOT_CLAUSES]
                     (GEN “A:bool”(SPEC “~(A:bool)” DISJ_IMP_THM))
fun delete_conjs1 pred conj_thm =
    let fun helper conj_thm so_far =
        if is_cond (concl conj_thm) then
            let val cd_thm = CONV_RULE (REWR_CONV COND_EXPAND) conj_thm
                val (disj1,disj2) = CONJ_PAIR cd_thm
                val imp1 = CONV_RULE (REWR_CONV DISJ_IMP_THM ) disj1
                val imp2 = CONV_RULE (REWR_CONV DISJ_IMP_THM1) disj2
                val body1 = UNDISCH imp1
                val body2 = UNDISCH imp2
                val res1 = delete_conjs1 pred body1
                val res2 = delete_conjs1 pred body2
                val rimp1 = DISCH (fst (dest_imp (concl imp1))) res1
                val rimp2 = DISCH (fst (dest_imp (concl imp2))) res2
                val rdisj1 = CONV_RULE (REWR_CONV IMP_DISJ_THM        ) rimp1
                val rdisj2 = CONV_RULE (REWR_CONV (GSYM DISJ_IMP_THM1)) rimp2
                val rcd = CONJ rdisj1 rdisj2
                val rconj_thm = CONV_RULE (REWR_CONV (GSYM COND_EXPAND)) rcd
            in
                rconj_thm::so_far
            end
        else
        if is_conj (concl conj_thm) then
            let val conj1 = CONJUNCT1 conj_thm in
                if is_cond (concl conj1) then
                    helper (CONJUNCT2 conj_thm) ((helper conj1 [])@so_far)
                else
                if pred (concl conj1) then
                    helper (CONJUNCT2 conj_thm) (conj1::so_far)
                else helper (CONJUNCT2 conj_thm) so_far
            end
        else
            if pred (concl conj_thm) then (conj_thm::so_far) else so_far
    in
        LIST_CONJ (rev (helper (REWRITE_RULE[GSYM CONJ_ASSOC] conj_thm) []))
    end
in
fun delete_conjs pred conj_thm =
    DISCH_ALL (delete_conjs1 pred conj_thm)
end

(* Myra's original version, does not handle COND's as conjuncts:

(* delete the conjs that don't satisfy pred *)
fun delete_conjs pred conj_thm =
    let fun helper conj_thm so_far =
        if is_conj (concl conj_thm) then
            let val conj1 = CONJUNCT1 conj_thm in
                if pred (concl conj1) then
                    helper (CONJUNCT2 conj_thm) (conj1::so_far)
                else helper (CONJUNCT2 conj_thm) so_far
            end
        else
            if pred (concl conj_thm) then (conj_thm::so_far) else so_far
    in
        DISCH_ALL (LIST_CONJ (rev (helper conj_thm [])))
    end
*)

fun props_in_tm tm =
    if is_var tm then tmem tm prop_vars else
    if is_const tm then false else
    if is_abs tm then props_in_tm (body tm) else
    (* must be comb *)
        let val (t1, t2) = dest_comb tm in
            props_in_tm t1 orelse props_in_tm t2
        end

fun foldr ftn base (b::bs) = ftn (b, (foldr ftn base bs))
  | foldr ftn base [] = base

fun do_one_conj2 rule tm =
    let val (vars, bod) = strip_forall tm
    in
        if is_imp bod then
            let val (ex_mod_hyps, prop_and_rel) = dest_imp bod
                val prop_tm = fst (dest_conj prop_and_rel)
                val (exists_vars, mod_hyps) = strip_exists ex_mod_hyps
                val mod_hyp_list = strip_conj mod_hyps
                val new_mod_hyps = list_mk_conj mod_hyp_list
                val ex_new_mod_hyps = list_mk_exists
                    (exists_vars, new_mod_hyps)
                val speced_rule = SPECL vars rule
                val thm1 = ASSUME
                    (list_mk_forall
                     (vars, mk_imp (ex_new_mod_hyps, prop_tm)))
                val thm2 = SPEC_ALL thm1
                fun pred tm = not (props_in_tm tm)
                val conj_imp = delete_conjs pred (ASSUME new_mod_hyps)
                val ex_conj_imp = foldr (fn (var, thm) => EXISTS_IMP var thm)
                    conj_imp exists_vars
                val conjs_imp_reltn = IMP_TRANS ex_conj_imp speced_rule
                val thm3 = PURE_ONCE_REWRITE_RULE [and_thm]
                    (IMP_CONJ thm2 conjs_imp_reltn)
                val thm4 = PURE_ONCE_REWRITE_RULE
                    [CONJUNCTS_AC (new_mod_hyps, mod_hyps)] thm3
            in
                DISCH_ALL (GENL vars thm4)
            end
        else
            let val (prop_tm, reltn_tm) = dest_conj bod
                val thm1 = ASSUME (list_mk_forall (vars, prop_tm))
                val thm2 = GENL vars
                    (CONJ (SPEC_ALL thm1) (SPECL vars rule))
            in
                DISCH_ALL thm2
            end
    end

(*
val ((rule, tm)::more_info) = more_info;
val thm1 = do_one_conj2 rule tm
*)

fun prove_conj_imp2 ((rule, tm)::more_info) =
    if null more_info then
        do_one_conj2 rule tm
    else
        let val thm1 = do_one_conj2 rule tm
            val thm2 = prove_conj_imp2 more_info
        in
            IMP_CONJ thm1 thm2
        end
  | prove_conj_imp2 [] = REFL “T” (* so SML doesn't complain *)

(*
fun prove_conj_imp2 (((rule, tm)::more_info) :(thm * term)list) =
    if more_info = ([]:(thm * term)list) then
        do_one_conj2 rule tm
    else
        let val thm1 = do_one_conj2 rule tm
            val thm2 = prove_conj_imp2 more_info
        in
            IMP_CONJ thm1 thm2
        end
  | prove_conj_imp2 [] = REFL “T” (* so SML doesn't complain *)
*)

(* The following was added by PVH on Feb. 25, 2000.
   It repairs strip_conj, which breaks apart elements of a conjunction
   which are themselves conjunctions; we wish to only do this at the
   top level. *)

fun careful_strip_conj tm =
    let val (h, t) = dest_conj tm
    in (h :: (careful_strip_conj t))
    end
    handle _ => [tm]

val rules_thm = prove_conj_imp2
    (zip (CONJUNCTS rules_sat) (careful_strip_conj mod_rules))

val almost_final_thm = IMP_TRANS (IMP_TRANS rules_thm new_thm) concl_thm

in
    GENL prop_vars almost_final_thm
end


(* When given a goal of the form:
   (!<arg_vars>. rel_0 <arg_vars> ==> prop_0[<arg_vars>]) /\
                 ...
   (!<arg_vars>. rel_n <arg_vars> ==> prop_n[<arg_vars>])
   where the rel_i are the relations mentioned in the conclusion of
   the induct_thm (they don't need to be in the same order),
   rule_induct sets up the induction for you. Works for strong
   induction thms as well as regular ones. *)

local
    fun get_reltn tm =
        fst (strip_comb (fst (dest_imp (snd (strip_forall tm)))))
    fun process_term tm =
        (fst (strip_comb (fst (dest_imp (snd (strip_forall tm))))), tm)
    fun get_correct_tm ((rel, tm)::more_info) rel2 =
        if rel ~~ rel2 then tm
        else get_correct_tm more_info rel2
      | get_correct_tm [] rel2 =
        raise mk_HOL_ERR "inductive_relations" "rule_induct"
          ("need term for relation "^(fst (dest_const rel2)))
in
    fun rule_induct induct_thm (asms, gl) =
        let val reltns_goals_list = map process_term (strip_conj gl)
            val concl_list = strip_conj
                (snd (dest_imp (snd (strip_forall (concl induct_thm)))))
            val reltns_in_ind = map get_reltn concl_list
            (* look thru' the list for the clause that corresponds to it *)
            val sorted_goals = map
                (get_correct_tm reltns_goals_list) reltns_in_ind
            val props_list = map
                (fn tm => let val (vars, t2) = strip_forall tm
                              val applied_prop = snd (dest_imp t2) in
                          list_mk_abs (vars, applied_prop) end) sorted_goals
            val speced_ind = BETA_RULE (SPECL props_list induct_thm)
        in
            MP_IMP_TAC speced_ind (asms, gl)
        end
end

end; (* ind_rel *)
