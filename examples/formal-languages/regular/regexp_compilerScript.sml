open HolKernel Parse boolLib bossLib lcsymtacs numLib;
open optionTheory pairTheory relationTheory arithmeticTheory
     pred_setTheory bagTheory containerTheory
     listTheory rich_listTheory stringTheory sortingTheory mergesortTheory
     comparisonTheory balanced_mapTheory eq_cmp_bmapTheory osetTheory
     finite_mapTheory vec_mapTheory charsetTheory regexpTheory
;

val _ = numLib.prefer_num();

fun pat_elim q = Q.PAT_X_ASSUM q (K ALL_TAC);

val SET_EQ_THM = Q.prove
(`!s1 s2. (s1 = s2) = !x. s1 x = s2 x`,
 METIS_TAC [EXTENSION,IN_DEF]);

val LENGTH_NIL_SYM =
   GEN_ALL (CONV_RULE (LHS_CONV SYM_CONV) (SPEC_ALL LENGTH_NIL));

val list_ss = list_ss ++ rewrites [LENGTH_NIL, LENGTH_NIL_SYM];

val set_ss = list_ss ++ pred_setLib.PRED_SET_ss ++ rewrites [SET_EQ_THM,IN_DEF]

val _ = new_theory "regexp_compiler";

val comparison_distinct = TypeBase.distinct_of ``:ordering``

val eq_cmp_regexp_compare = Q.prove
(`eq_cmp regexp_compare`,
 metis_tac [eq_cmp_def, regexp_compare_good,regexp_compare_eq]);

(*---------------------------------------------------------------------------*)
(* Output of the compiler is in term of vectors.                             *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype `vector = Vector of 'a list`;

val fromList_def = Define `fromList l = Vector l`;
val sub_def      = Define `sub (Vector l) n = EL n l`;
val length_def   = Define `length (Vector l) = LENGTH l`;

val fromList_Vector = save_thm
("fromList_Vector",
 SIMP_RULE list_ss [GSYM FUN_EQ_THM] fromList_def);

(*---------------------------------------------------------------------------*)
(* Manipulate the set of seen states                                         *)
(*---------------------------------------------------------------------------*)

val _ = Parse.type_abbrev("regexp_set", ``:(regexp,unit)balanced_map``);

val insert_regexp_def =
 Define
   `insert_regexp r seen = balanced_map$insert regexp_compare r () seen`;

val mem_regexp_def =
 Define
   `mem_regexp r seen = balanced_map$member regexp_compare r seen`;

(*---------------------------------------------------------------------------*)
(* Transitions out of a state (regexp).                                      *)
(*---------------------------------------------------------------------------*)

val transitions_def =
 Define
   `transitions r = MAP (\c. (c,smart_deriv c r)) ALPHABET`;

val extend_states_def =
 Define
   `(extend_states next_state state_map trans [] = (next_state,state_map,trans)) /\
    (extend_states next_state state_map trans ((c,r')::t) =
       case balanced_map$lookup regexp_compare r' state_map
        of SOME n => extend_states next_state state_map ((c,n)::trans) t
         | NONE   => extend_states (next_state + 1n)
                        (balanced_map$insert regexp_compare r' next_state state_map)
                        ((c,next_state)::trans)
                        t)`;

val extend_states_ind = fetch "-" "extend_states_ind";

val build_table_def =
 Define
   `build_table arcs r (next_state,state_map,table) =
     let (next_state,state_map,trans) = extend_states next_state state_map [] arcs
     in case balanced_map$lookup regexp_compare r state_map
         of SOME n => (next_state, state_map, (n,trans)::table)
          | NONE   => (next_state + 1n,
                       balanced_map$insert regexp_compare r next_state state_map,
                       (next_state,trans)::table)`;

(*---------------------------------------------------------------------------*)
(* The core regexp compiler. The seen argument holds the already-seen        *)
(* regexps, which map to states in the final DFA. The n argument is a        *)
(* step-index used to ensure that the function terminates.                   *)
(*---------------------------------------------------------------------------*)

val Brz_def =
 Define
  `Brz seen worklist acc n =
     if n <= 0n then NONE else
     case worklist of
        [] => SOME (seen,acc)
     | r::t =>
         if mem_regexp r seen then Brz seen t acc (n-1) else
         let arcs = transitions r
         in Brz (insert_regexp r seen)
                (remove_dups (MAP SND arcs) ++ t)
                (build_table arcs r acc)
                (n-1)`;

val MAXNUM_32_def = Define `MAXNUM_32:num = 2147483647`;

(*---------------------------------------------------------------------------*)
(* Build Greve-style Brz function                                            *)
(*---------------------------------------------------------------------------*)

val MAX_LE_THM = Q.prove
(`!m n. m <= MAX m n /\ n <= MAX m n`,
 RW_TAC arith_ss [MAX_DEF]);

val IS_SOME_EXISTS = Q.prove
(`!x. IS_SOME x = ?y. x = SOME y`,
 Cases THEN METIS_TAC [optionTheory.IS_SOME_DEF]);

(*---------------------------------------------------------------------------*)
(* Domain of the function.                                                   *)
(*---------------------------------------------------------------------------*)

val dom_Brz_def =
  Define
   `dom_Brz seen worklist acc = ?d. IS_SOME(Brz seen worklist acc d)`;

(*---------------------------------------------------------------------------*)
(* Create measure function rdepth. Uses following code copied from           *)
(*                                                                           *)
(*       HOLDIR/src/pfl/defchoose                                            *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*  MINCHOOSE (sname, cname,``!x1 ... xn. ?z. M[x1,...,xn,z]``)              *)
(*   returns                                                                 *)
(*                                                                           *)
(*    |- !x1...xn z. M[x1,...,xn,z] ==>                                      *)
(*                   M[x1,...,xn,cname x1...xn] /\                           *)
(*                   !m. M[x1,...,xn,m] ==> cname x1...xn <= m               *)
(*                                                                           *)
(* where cname in the theorem is a constant. This theorem is stored in the   *)
(* current theory under sname. Thus this rule is a form of the               *)
(* well-ordering property.                                                   *)
(*---------------------------------------------------------------------------*)

val WOP_THM = Q.prove
(`!P. (?n. P n) ==> ?min. P min /\ !k. P k ==> min <= k`,
 METIS_TAC [arithmeticTheory.WOP,DECIDE ``~(m<n) ==> n<=m``]);

fun MINCHOOSE (store_name,const_name,tm) =
 let val (V,body) = strip_forall tm
     val P = snd(dest_comb body)
     val wop_thm = BETA_RULE(SPEC P WOP_THM)
     val min_term = snd(dest_imp (concl wop_thm))
     val min_term_pred = snd(dest_comb min_term)
     val th1 = BETA_RULE(GSYM (ISPECL [body,min_term_pred] RIGHT_EXISTS_IMP_THM))
     val th2 = EQ_MP th1 wop_thm
     val th3 = GENL V th2
     val th4 = Ho_Rewrite.REWRITE_RULE[SKOLEM_THM] th3
     val th5 = Ho_Rewrite.REWRITE_RULE[GSYM LEFT_FORALL_IMP_THM] th4
 in
  new_specification(store_name, [const_name], th5)
 end
 handle e => raise wrap_exn "" "MINCHOOSE" e;

val rdepth_thm =
   MINCHOOSE ("rdepth_thm", "rdepth",
    ``!seen worklist acc. ?d. IS_SOME(Brz seen worklist acc d)``)

(*---------------------------------------------------------------------------*)
(* Define Brzozo                                                             *)
(*---------------------------------------------------------------------------*)

val Brzozo_def =
 Define
   `Brzozo seen worklist acc =
      THE (Brz seen worklist acc (rdepth seen worklist acc))`;


(*---------------------------------------------------------------------------*)
(* Lemmas about Brz and definedness                                          *)
(*---------------------------------------------------------------------------*)

val IS_SOME_Brz = Q.prove
(`!d seen worklist acc.
      IS_SOME (Brz seen worklist acc d)
         ==>
        d <> 0`,
 Cases >> rw[Once Brz_def])

val Brz_SOME = Q.prove
(`!d seen worklist acc res.
   (Brz seen worklist acc d = SOME res)
   ==> d <> 0`,
 METIS_TAC [IS_SOME_Brz,IS_SOME_EXISTS]);

val Brz_dlem = Q.prove
(`!d seen worklist acc.
  IS_SOME (Brz seen worklist acc d)
   ==>
  (Brz seen worklist acc d = Brz seen worklist acc (SUC d))`,
 Ho_Rewrite.REWRITE_TAC [IS_SOME_EXISTS,GSYM LEFT_FORALL_IMP_THM]
 >> Induct
    >- metis_tac [Brz_SOME]
    >- (rw[] >> rw[Once Brz_def,LET_THM]
         >> pop_assum mp_tac
         >> BasicProvers.EVERY_CASE_TAC
            >- rw [Brz_def]
            >- (rw [Once Brz_def] >> metis_tac [])
            >- (DISCH_THEN (mp_tac o SIMP_RULE list_ss [Once Brz_def])
                 >> rw[LET_THM]
                 >> metis_tac[]))
);

val Brz_monotone = Q.prove
(`!d1 d2 seen worklist acc.
      IS_SOME(Brz seen worklist acc d1) /\ d1 <= d2
       ==> (Brz seen worklist acc d1 = Brz seen worklist acc d2)`,
 RW_TAC arith_ss [LESS_EQ_EXISTS] THEN
 Induct_on `p` THEN METIS_TAC [ADD_CLAUSES,Brz_dlem]);

val Brz_norm = Q.prove
(`!d seen worklist acc.
   IS_SOME(Brz seen worklist acc d)
    ==>
   (Brz seen worklist acc d = Brz seen worklist acc (rdepth seen worklist acc))`,
  METIS_TAC [Brz_monotone,rdepth_thm]);

val Brz_determ = Q.store_thm("Brz_determ",
 `!d1 d2 seen worklist acc.
    IS_SOME(Brz seen worklist acc d1) /\ IS_SOME(Brz seen worklist acc d2)
       ==> (Brz seen worklist acc d1 = Brz seen worklist acc d2)`,
  METIS_TAC [Brz_norm]);

(*---------------------------------------------------------------------------*)
(* Derive eqns for dom_Brz                                                   *)
(*---------------------------------------------------------------------------*)

val lem = Q.prove
(`!seen worklist acc.
   (worklist = []) ==> IS_SOME (Brz seen worklist acc 1)`,
 RW_TAC arith_ss [Once Brz_def]);

val dom_base_case = Q.prove
(`!seen worklist acc.
   (worklist = []) ==> dom_Brz seen worklist acc`,
 METIS_TAC [dom_Brz_def, lem]);

val step2_lem1a = Q.prove
(`!seen worklist acc r t.
   (worklist = r::t) /\ mem_regexp r seen /\ dom_Brz seen worklist acc
    ==> dom_Brz seen t acc`,
 RW_TAC std_ss [dom_Brz_def] THEN
 `d<>0` by METIS_TAC [IS_SOME_Brz] THEN
 Q.EXISTS_TAC `d-1` THEN
 Q.PAT_X_ASSUM `IS_SOME arg` (MP_TAC o ONCE_REWRITE_RULE [Brz_def]) THEN
 CASE_TAC THEN RW_TAC arith_ss [LET_THM]
 THEN METIS_TAC[]);

val step2_lem1b = Q.prove
(`!seen worklist acc r t arcs.
   (worklist = r::t) /\ ~mem_regexp r seen /\
   (arcs = transitions r) /\  dom_Brz seen worklist acc
    ==> dom_Brz (insert_regexp r seen)
                (remove_dups (MAP SND arcs) ++ t)
                (build_table arcs r acc)`,
 RW_TAC std_ss [dom_Brz_def] THEN
 `d<>0` by METIS_TAC [IS_SOME_Brz] THEN
 Q.EXISTS_TAC `d-1` THEN
 Q.PAT_X_ASSUM `IS_SOME arg` (MP_TAC o ONCE_REWRITE_RULE [Brz_def]) THEN
 CASE_TAC THEN RW_TAC arith_ss [LET_THM]
 THEN METIS_TAC[]);

val step2_lem2a = Q.prove
(`!seen worklist acc r t.
  (worklist = r::t) /\ mem_regexp r seen /\ dom_Brz seen t acc
   ==> dom_Brz seen worklist acc`,
 rw_tac std_ss [dom_Brz_def]
   >> Q.EXISTS_TAC `SUC d`
   >> rw [Once Brz_def]);

val step2_lem2b = Q.prove
(`!seen worklist acc r t arcs.
  (worklist = r::t) /\ (arcs = transitions r) /\
  ~mem_regexp r seen /\
  dom_Brz (insert_regexp r seen)
          (remove_dups (MAP SND arcs) ++ t)
          (build_table arcs r acc)
   ==> dom_Brz seen worklist acc`,
 rw_tac std_ss [dom_Brz_def]
   >> Q.EXISTS_TAC `SUC d`
   >> rw [Once Brz_def,LET_THM]);

(*---------------------------------------------------------------------------*)
(* Equational characterization of dom.                                       *)
(*---------------------------------------------------------------------------*)

val dom_Brz_eqns = Q.store_thm
("dom_Brz_eqns",
 `(dom_Brz seen [] acc = T) /\
  (dom_Brz seen (r::t) acc =
    if mem_regexp r seen
       then dom_Brz seen t acc
       else let arcs = transitions r
            in dom_Brz (insert_regexp r seen)
                       (remove_dups (MAP SND arcs) ++ t)
                       (build_table arcs r acc))`,
 CONJ_TAC
  >- metis_tac [dom_base_case]
  >- metis_tac [step2_lem1a,step2_lem1b,step2_lem2a,step2_lem2b,LET_THM]);

(*---------------------------------------------------------------------------*)
(* Optimization: dom_Brz doesn't depend on its "acc" argument, so can be     *)
(* replaced by a version that doesn't have it.                               *)
(*---------------------------------------------------------------------------*)

val dom_Brz_alt_def =
 Define
  `dom_Brz_alt seen worklist = dom_Brz seen worklist ARB`;

val acc_irrelevant = Q.prove
(`!n seen worklist acc acc1.
     IS_SOME (Brz seen worklist acc n) ==>
     IS_SOME (Brz seen worklist acc1 n)`,
 Induct
   >- rw [Once Brz_def]
   >- (ONCE_REWRITE_TAC [Brz_def]
        >> rw_tac list_ss [LET_THM]
        >> BasicProvers.EVERY_CASE_TAC
           >- rw []
           >- metis_tac[]
           >- metis_tac[]));

val dom_Brz_alt_equal = Q.store_thm
("dom_Brz_alt_equal",
 `!seen worklist acc. dom_Brz seen worklist acc = dom_Brz_alt seen worklist`,
 rw [dom_Brz_def, dom_Brz_alt_def] >> metis_tac [acc_irrelevant]);


(*---------------------------------------------------------------------------*)
(*    |- dom_Brz_alt seen [] /\                                              *)
(*       (dom_Brz_alt seen (r::t) =                                          *)
(*         if mem_regexp r seen then                                         *)
(*            dom_Brz_alt seen t                                             *)
(*         else                                                              *)
(*            (let arcs = transitions r                                      *)
(*             in dom_Brz_alt (insert_regexp r seen)                         *)
(*                            (remove_dups (MAP SND arcs) ++ t)))            *)
(*---------------------------------------------------------------------------*)

val dom_Brz_alt_eqns = save_thm
("dom_Brz_alt_eqns",
 SIMP_RULE bool_ss [dom_Brz_alt_equal] dom_Brz_eqns);

(*---------------------------------------------------------------------------*)
(* Recursion equations for Brzozo                                            *)
(*---------------------------------------------------------------------------*)

val Brzozo_base = Q.prove
(`!seen worklist acc.
    dom_Brz seen worklist acc /\ (worklist = [])
    ==>
   (Brzozo seen worklist acc = (seen,acc))`,
 RW_TAC std_ss [Brzozo_def,dom_Brz_def]
  >> `rdepth seen [] acc <> 0`
       by METIS_TAC [IS_SOME_Brz,rdepth_thm]
  >> RW_TAC arith_ss [Once Brz_def]);

val Brzozo_rec1 = Q.prove
(`!seen worklist accr r t.
    (worklist = r::t) /\
    dom_Brz seen worklist acc /\
    mem_regexp r seen
    ==>
    (Brzozo seen worklist acc = Brzozo seen t acc)`,
 RW_TAC std_ss [Brzozo_def,dom_Brz_def]
  >> `d <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `Brz seen (r::t) acc d = Brz seen t acc (d-1)`
      by rw_tac list_ss [Once Brz_def]
  >> METIS_TAC [IS_SOME_EXISTS,NOT_SOME_NONE,THE_DEF,Brz_norm]);

val Brzozo_rec2 = Q.prove
(`!seen worklist accr r t.
    (worklist = r::t) /\
    dom_Brz seen worklist acc /\
    ~mem_regexp r seen
    ==>
    (Brzozo seen worklist acc =
       let arcs = transitions r
       in Brzozo (insert_regexp r seen)
                 (remove_dups (MAP SND arcs) ++ t)
                 (build_table arcs r acc))`,
 rw_tac std_ss [Brzozo_def,dom_Brz_def,LET_THM]
  >> `d <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `Brz seen (r::t) acc d =
      let arcs = transitions r
      in Brz (insert_regexp r seen)
          (remove_dups (MAP SND arcs) ++ t)
          (build_table arcs r acc) (d-1)`
      by rw_tac list_ss [Once Brz_def,LET_THM]
  >> METIS_TAC [IS_SOME_EXISTS,NOT_SOME_NONE,THE_DEF,Brz_norm,LET_THM]);

(*---------------------------------------------------------------------------*)
(* Equational characterization of Brzozo.                                    *)
(*---------------------------------------------------------------------------*)

val Brzozo_eqns = Q.prove
(`!seen worklist acc.
   dom_Brz seen worklist acc
  ==>
   (Brzozo seen worklist acc =
     case worklist of
        []  => (seen,acc)
     | r::t =>
        if mem_regexp r seen then
           Brzozo seen t acc
        else
          let arcs = transitions r
          in
           Brzozo (insert_regexp r seen)
                  (remove_dups (MAP SND arcs) ++ t)
                  (build_table arcs r acc))`,
 Cases_on `worklist` >> rpt gen_tac >> CASE_TAC >> rw[LET_THM]
  >- metis_tac [Brzozo_base]
  >- metis_tac [Brzozo_rec1]
  >- metis_tac [Brzozo_rec2]
);

(*---------------------------------------------------------------------------*)
(* Now prove induction theorem. This is based on using rdepth as a measure   *)
(* on the recursion. Thus we first have some lemmas about how rdepth         *)
(* decreases in recursive calls.                                             *)
(*---------------------------------------------------------------------------*)

val step3a_lt = Q.prove
(`!seen worklist acc r t.
    (worklist = r::t) /\ mem_regexp r seen /\
    dom_Brz seen worklist acc
    ==> rdepth seen t acc  < rdepth seen worklist acc`,
 rw_tac std_ss [dom_Brz_def] THEN IMP_RES_TAC rdepth_thm THEN
   `rdepth seen (r::t) acc <> 0` by METIS_TAC [IS_SOME_Brz] THEN
   `rdepth seen (r::t) acc - 1 < rdepth seen (r::t) acc` by DECIDE_TAC THEN
   `IS_SOME (Brz seen t acc (rdepth seen (r::t) acc - 1))`
     by (Q.PAT_X_ASSUM `IS_SOME (Brz seen (r::t) acc (rdepth seen (r::t) acc))`
          (mp_tac o SIMP_RULE arith_ss [Once Brz_def])
        >> CASE_TAC >> rw[LET_THM]
           >- metis_tac[]
           >- metis_tac[])
    >> `rdepth seen t acc <= rdepth seen (r::t) acc - 1`
        by metis_tac [rdepth_thm]
    >> decide_tac);

val step3b_lt = Q.prove
(`!seen worklist acc r t arcs.
    (worklist = r::t) /\ ~mem_regexp r seen /\
    (arcs = transitions r) /\ dom_Brz seen worklist acc
    ==> rdepth (insert_regexp r seen)
               (remove_dups (MAP SND arcs) ++ t)
               (build_table arcs r acc)  < rdepth seen worklist acc`,
 rw_tac std_ss [dom_Brz_def] THEN IMP_RES_TAC rdepth_thm
  >> `rdepth seen (r::t) acc <> 0` by METIS_TAC [IS_SOME_Brz]
  >> `rdepth seen (r::t) acc - 1 < rdepth seen (r::t) acc` by DECIDE_TAC
  >> `IS_SOME (Brz (insert_regexp r seen)
                   (remove_dups (MAP SND (transitions r)) ++ t)
                   (build_table (transitions r) r acc)
                   (rdepth seen (r::t) acc - 1))`
     by (Q.PAT_X_ASSUM `IS_SOME (Brz seen (r::t) acc (rdepth seen (r::t) acc))`
          (mp_tac o SIMP_RULE arith_ss [Once Brz_def])
        >> CASE_TAC >> rw[LET_THM]
           >- metis_tac[]
           >- metis_tac[])
    >> `rdepth (insert_regexp r seen)
               (remove_dups (MAP SND (transitions r)) ++ t)
               (build_table (transitions r) r acc) <= rdepth seen (r::t) acc - 1`
        by metis_tac [rdepth_thm]
    >> decide_tac);

(*---------------------------------------------------------------------------*)
(* Induction for Brzozo is obtained by instantiating the WF induction        *)
(* theorem with the rdepth measure and then simplifying.                     *)
(*---------------------------------------------------------------------------*)

val ind0 = MATCH_MP relationTheory.WF_INDUCTION_THM
                    (Q.ISPEC `\(seen,worklist,acc). rdepth seen worklist acc`
                             prim_recTheory.WF_measure);
val ind1 = SIMP_RULE std_ss [prim_recTheory.measure_thm] ind0;
val ind2 = SIMP_RULE std_ss [pairTheory.FORALL_PROD]
      (Q.ISPEC `\(seen,worklist,acc).
                    dom_Brz seen worklist acc ==> P seen worklist acc` ind1);
val ind3 = Q.prove
(`!P. (!seen worklist acc.
         (!a b c. rdepth a b c < rdepth seen worklist acc
                  ==> dom_Brz a b c
                  ==> P a b c)
         ==> dom_Brz seen worklist acc ==> P seen worklist acc)
  ==>
  !seen worklist acc. dom_Brz seen worklist acc ==> P seen worklist acc`,
rpt strip_tac
 >> pop_assum mp_tac
 >> Cases_on `acc`
 >> Cases_on `r`
 >> Q.SPEC_TAC (`r'`,`w`)
 >> Q.SPEC_TAC (`q'`,`v`)
 >> Q.SPEC_TAC (`q`,`u`)
 >> Q.ID_SPEC_TAC `worklist`
 >> Q.ID_SPEC_TAC `seen`
 >> match_mp_tac ind2
 >> fs [FORALL_PROD]);

val Brzozowski_ind = Q.store_thm
("Brzozowski_ind",
 `!P.
   (!seen worklist acc.
       dom_Brz seen worklist acc /\
       (!r t. (worklist = r::t) /\ mem_regexp r seen ==> P seen t acc) /\
       (!r t arcs. (arcs = transitions r) /\ (worklist = r::t) /\ ~mem_regexp r seen
                   ==> P (insert_regexp r seen)
                         (remove_dups (MAP SND arcs) ++ t)
                         (build_table arcs r acc))
         ==> P seen worklist acc)
  ==> !seen worklist acc. dom_Brz seen worklist acc ==> P seen worklist acc`,
  gen_tac >> strip_tac
  >> HO_MATCH_MP_TAC ind3
  >> rw[]
  >> metis_tac [step3a_lt,step3b_lt,dom_Brz_eqns]);

(*---------------------------------------------------------------------------*)
(* Efficient executable version of Brzozo                                    *)
(*---------------------------------------------------------------------------*)

val exec_Brz_def =
 Define
 `exec_Brz seen worklist acc d =
    if d=0n then
       (if dom_Brz seen worklist acc then Brzozo seen worklist acc else ARB)
    else
      case worklist
       of [] => (seen,acc)
       | r::t =>
         if mem_regexp r seen then
             exec_Brz seen t acc (d − 1)
           else
             let arcs = transitions r
             in exec_Brz (insert_regexp r seen)
                         (remove_dups (MAP SND arcs) ++ t)
                         (build_table arcs r acc) (d − 1)`;

val exec_Brz_equals_Brzozo = Q.prove
(`!d seen worklist acc.
    dom_Brz seen worklist acc
   ==>
    (exec_Brz seen worklist acc d = Brzozo seen worklist acc)`,
 Induct
  >> rw_tac std_ss [Once exec_Brz_def,LET_THM]
  >> pop_assum mp_tac
  >> CASE_TAC
    >- rw [Brzozo_eqns,dom_Brz_eqns]
    >- rw [Brzozo_eqns,dom_Brz_eqns,LET_THM]);

val Brzozowski_def =
 Define
   `Brzozowski seen worklist acc =
      if dom_Brz seen worklist acc then
         Brzozo seen worklist acc
      else
         exec_Brz seen worklist acc MAXNUM_32`;

(*---------------------------------------------------------------------------*)
(* Theorem showing that Brzozowski can be executed w.o. termination proof.   *)
(* In order to evaluate Brzozowski, we can dispatch to exec_Brz.             *)
(*---------------------------------------------------------------------------*)

val Brzozowski_exec_Brz = Q.store_thm
("Brzozowski_exec_Brz",
 `Brzozowski seen worklist acc = exec_Brz seen worklist acc MAXNUM_32`,
 rw_tac std_ss [Brzozowski_def,exec_Brz_equals_Brzozo]);

(*---------------------------------------------------------------------------*)
(* In order to reason about Brzozowski, we use the following theorem.        *)
(*---------------------------------------------------------------------------*)

val Brzozowski_eqns = Q.store_thm
("Brzozowski_eqns",
 `dom_Brz seen worklist acc ==>
   (Brzozowski seen worklist acc =
      case worklist
       of [] => (seen,acc)
       | r::t =>
         if mem_regexp r seen then
             Brzozowski seen t acc
           else
             let arcs = transitions r
             in Brzozowski (insert_regexp r seen)
                           (remove_dups (MAP SND arcs) ++ t)
                           (build_table arcs r acc))`,
 rw_tac std_ss [Brzozowski_def]
  >> CASE_TAC
     >- rw [Brzozo_eqns]
     >- (rw [Brzozo_eqns,LET_THM]
          >> metis_tac [exec_Brz_equals_Brzozo,dom_Brz_eqns]));


(*---------------------------------------------------------------------------*)
(* Return to definition of compiler                                          *)
(*---------------------------------------------------------------------------*)

val get_accepts_def =
 Define
  `get_accepts fmap =
     mergesort (\a b:num. a <= b)
       (balanced_map$foldrWithKey
         (\r (n:num) nlist. if nullable r then n::nlist else nlist)
         [] fmap)`;

val accepts_to_vector_def =
 Define
  `accepts_to_vector accept_states max_state =
     alist_to_vec (MAP (\x. (x,T)) accept_states) F max_state max_state`;

val table_to_vectors_def =
 Define
  `table_to_vectors table =
     MAP (\(k:num,table2).
             alist_to_vec (mergesort (inv_image (\a b:num. a <= b) FST)
                                 (MAP (\(c,n). (c, SOME n)) table2))
                          NONE alphabet_size alphabet_size)
         (mergesort (inv_image (\a b:num. a <= b) FST) table)`;

val compile_regexp_def =
 Define
   `compile_regexp r =
      let r' = normalize r in
      let (states,last_state,state_numbering,table)
         = Brzozowski balanced_map$empty [r']
                      (1n, balanced_map$singleton r' 0n, []) in
      let delta_vecs = table_to_vectors table in
      let accepts_vec = accepts_to_vector (get_accepts state_numbering) last_state
      in
         (state_numbering,
          delta_vecs,
          accepts_vec)`;

val exec_dfa_def =
 Define
  `exec_dfa finals table n s =
   case s of
    | "" => sub finals n
    | c::t =>
      case sub (sub table n) (ORD c) of
       | NONE => F
       | SOME k => exec_dfa finals table k t`;

val exec_dfa_thm = Q.prove
(`(exec_dfa finals table n [] = sub finals n) /\
  (exec_dfa finals table n (c::t) =
    case sub (sub table n) (ORD c) of
     | NONE => F
     | SOME k => exec_dfa finals table k t)`,
CONJ_TAC
 >- rw_tac list_ss [exec_dfa_def]
 >- rw_tac list_ss [SimpLHS, Once exec_dfa_def])

(*
val exec_dfa_def =
  Define
   `(exec_dfa finals table n [] = EL n finals) /\
    (exec_dfa finals table n (c::t) =
        case EL (ORD c) (EL n table) of
         | NONE => F
         | SOME k => exec_dfa finals table k t)`;
*)


(*---------------------------------------------------------------------------*)
(* Returns a function of type :string -> bool                                *)
(*---------------------------------------------------------------------------*)

val regexp_matcher_def =
 Define
  `regexp_matcher r =
    let (state_numbering,delta,accepts) = compile_regexp r in
    let start_state = THE (balanced_map$lookup regexp_compare
                               (normalize r) state_numbering) in
    let acceptsV = fromList accepts in
    let deltaV = fromList (MAP fromList delta)
    in
      exec_dfa acceptsV deltaV start_state`;

(*
val regexp_matcher_def =
 Define
  `regexp_matcher r =
    let (state_numbering,delta,accepts) = compile_regexp r in
    let start_state_opt = balanced_map$lookup regexp_compare (normalize r) state_numbering
    in
      exec_dfa accepts delta (THE start_state_opt)`;
*)

(*---------------------------------------------------------------------------*)
(* get_accepts properties                                                    *)
(*---------------------------------------------------------------------------*)

val sorted_get_accepts = Q.store_thm
("sorted_get_accepts",
 `!fmap. SORTED $<= (get_accepts fmap)`,
 RW_TAC set_ss [get_accepts_def] THEN
 CONV_TAC (DEPTH_CONV ETA_CONV) THEN
 MATCH_MP_TAC mergesort_sorted THEN
 RW_TAC arith_ss [transitive_def, total_def]);

val lookup_bin = Q.prove
(`!fmap fmap' n k v x.
      (lookup cmp r (Bin n k v fmap fmap') = SOME x)
      <=>
      ((cmp r k = Equal) /\ (v = x)) \/
      ((cmp r k = Less) /\ (lookup cmp r fmap = SOME x)) \/
      ((cmp r k = Greater) /\ (lookup cmp r fmap' = SOME x))`,
 RW_TAC list_ss [lookup_def] THEN BasicProvers.CASE_TAC);

val member_iff_lookup = Q.prove
(`!fmap cmp x. member cmp x fmap <=> ?y. lookup cmp x fmap = SOME y`,
 Induct
   >> rw_tac set_ss [member_def, lookup_def]
   >> BasicProvers.EVERY_CASE_TAC);

val member_bin = Q.prove
(`!fmap fmap' n k v.
     member cmp r (Bin n k v fmap fmap')
      <=>
      ((cmp r k = Equal) \/
      ((cmp r k = Less) /\ member cmp r fmap) \/
      ((cmp r k = Greater) /\ member cmp r fmap'))`,
 RW_TAC list_ss [member_def] THEN BasicProvers.CASE_TAC);

val key_less_lookup = Q.prove
(`!fmap cmp k1 k2 x.
     invariant cmp fmap /\ good_cmp cmp /\
     key_ordered cmp k1 fmap Less /\
     (lookup cmp k2 fmap = SOME x)
     ==>
     (cmp k1 k2 = Less)`,
Induct >> rw_tac list_ss [key_ordered_def, lookup_def, invariant_def]
       >> every_case_tac
          >- metis_tac []
          >- metis_tac [good_cmp_def,comparison_distinct]
          >- metis_tac []);

val key_greater_lookup = Q.prove
(`!fmap cmp k1 k2 x.
     invariant cmp fmap /\ good_cmp cmp /\
     key_ordered cmp k1 fmap Greater /\
     (lookup cmp k2 fmap = SOME x)
     ==>
     (cmp k2 k1 = Less)`,
Induct >> rw_tac list_ss [key_ordered_def, lookup_def, invariant_def]
       >> every_case_tac
          >- metis_tac []
          >- metis_tac [good_cmp_def,comparison_distinct]
          >- metis_tac []);

val lemma = Q.prove
(`!fmap x acc.
    balanced_map$invariant regexp_compare fmap /\
    MEM x (foldrWithKey
               (λr n nlist. if nullable r then n::nlist else nlist)
               acc fmap)
     ==>
    MEM x acc \/ ?r. nullable r /\ (lookup regexp_compare r fmap = SOME x)`,
 Induct THEN RW_TAC std_ss []
  >- full_simp_tac list_ss [foldrWithKey_def,lookup_def]
  >- (simp_tac list_ss [lookup_bin]
       >>
      `invariant regexp_compare fmap /\
       invariant regexp_compare fmap' /\
       key_ordered regexp_compare k fmap Greater /\
       key_ordered regexp_compare k fmap' Less`
           by metis_tac [invariant_def]
      >> qpat_x_assum `invariant cmp (Bin n k v fmap fmap')` (K ALL_TAC)
      >> fs []
      >> RULE_ASSUM_TAC (REWRITE_RULE [foldrWithKey_def])
      >> RES_THEN MP_TAC >> BETA_TAC >> rw[]
        >- metis_tac [regexp_compare_eq]
        >- metis_tac [key_less_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_greater_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_less_lookup,regexp_compare_good,good_cmp_thm]
        >- metis_tac [key_greater_lookup,regexp_compare_good,good_cmp_thm]));;

val mem_acc = Q.prove
(`!P fmap x acc.
    MEM x acc
     ==>
     MEM x (foldrWithKey
               (λr n nlist. if P r then n::nlist else nlist)
               acc fmap)`,
 gen_tac >> Induct >> RW_TAC std_ss [foldrWithKey_def] >> metis_tac [MEM]);

val lemma1 = Q.prove
(`!P fmap r x acc.
    P r /\ (lookup regexp_compare r fmap = SOME x)
     ==>
     MEM x (foldrWithKey (λr n nlist. if P r then n::nlist else nlist) acc fmap)`,
 gen_tac >> Induct
 >- rw_tac list_ss [lookup_def,foldrWithKey_def]
 >- (rw_tac list_ss [lookup_bin,regexp_compare_eq,foldrWithKey_def]
      >> metis_tac [mem_acc,MEM]));

val mem_get_accepts = Q.store_thm
("mem_get_accepts",
 `!bmap x.
    invariant regexp_compare bmap ==>
    (MEM x (get_accepts bmap)
       <=>
     ?r. nullable r /\ (lookup regexp_compare r bmap = SOME x))`,
 rw_tac list_ss [get_accepts_def,mergesort_mem] >> metis_tac [lemma,lemma1,MEM]);


(*---------------------------------------------------------------------------*)
(* Correctness of regexp compiler                                            *)
(*---------------------------------------------------------------------------*)

val fmap_inj_def =
 Define
  `fmap_inj cmp bmap =
     !x y. x IN fdom cmp bmap /\ (lookup cmp x bmap = lookup cmp y bmap)
            ==> (cmp x y = Equal)`;

val extend_states_inv_def =
 Define
  `extend_states_inv next_state state_map table =
     (invariant regexp_compare state_map /\
      fmap_inj regexp_compare state_map /\
      (frange regexp_compare state_map = count next_state) /\
      (!n. MEM n (MAP SND table) ⇒ n < next_state))`;

val extend_states_inv = Q.prove (
`!next_state state_map table states next_state' state_map' table'.
  (extend_states next_state state_map table states = (next_state',state_map',table')) ∧
  extend_states_inv next_state state_map table
  ⇒
  extend_states_inv next_state' state_map' table'`,
 ho_match_mp_tac extend_states_ind
  >> rw [extend_states_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> fs []
  >> FIRST_X_ASSUM match_mp_tac
  >> rw []
  >> fs [extend_states_inv_def, frange_def, MEM_MAP,EXTENSION,GSYM LEFT_FORALL_IMP_THM]
  >> `good_cmp regexp_compare /\ eq_cmp regexp_compare`
        by metis_tac [eq_cmp_regexp_compare,regexp_compare_good]
  >> rw_tac set_ss []
  >- metis_tac [insert_thm]
  >- (fs [fmap_inj_def,lookup_insert_thm]
       >> rw [regexp_compare_eq,fdom_insert]
       >> metis_tac [DECIDE ``x < (x:num) ==> F``,eq_cmp_def])
  >- (rw [lookup_insert_thm,regexp_compare_eq,EQ_IMP_THM]
       >- (pop_assum mp_tac >> rw_tac set_ss []
            >> metis_tac [DECIDE ``x < x + 1n``,LESS_TRANS])
       >- (`x < next_state \/ (x=next_state)` by DECIDE_TAC
             >> metis_tac [NOT_SOME_NONE]))
  >- rw_tac set_ss []
  >- metis_tac [LESS_TRANS,DECIDE ``x < x+1n``,IN_DEF]
  >- (rw_tac set_ss [] >> metis_tac[])
  >- metis_tac [LESS_TRANS,DECIDE ``x < x+1n``,IN_DEF])

val submap_def =
 Define
   `submap cmp t1 t2 =
         !x. x IN fdom cmp t1 ==> x IN fdom cmp t2 /\ (lookup cmp x t1 = lookup cmp x t2)`;

val submap_id = Q.prove
(`!t cmp. submap cmp t t`,
 rw [submap_def]);

val submap_trans = Q.prove
(`!t1 t2 t3 cmp. submap cmp t1 t2 /\ submap cmp t2 t3 ==> submap cmp t1 t3`,
 rw [submap_def]);

val submap_mono = Q.prove
(`!t1 t2 k v cmp.
    eq_cmp cmp /\ invariant cmp t2 /\ submap cmp t1 t2
    /\ k NOTIN fdom cmp t1
   ==>
   submap cmp t1 (insert cmp k v t2)`,
  rw [submap_def,fdom_insert]
  >> res_tac
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> rw [lookup_insert_thm]
  >> `k=x` by metis_tac [eq_cmp_def]
  >> rw []
  >> metis_tac[]);

val submap_insert = Q.prove
(`!bmap t cmp x v.
    eq_cmp cmp /\ invariant cmp bmap /\
    x NOTIN fdom cmp bmap /\
    submap cmp (insert cmp x v bmap) t
    ==> submap cmp bmap t`,
 rw_tac set_ss [submap_def]
  >> `invariant cmp (insert cmp x v bmap)` by metis_tac [insert_thm,eq_cmp_def]
  >- (qpat_x_assum `$! M` (mp_tac o Q.ID_SPEC) >> rw_tac set_ss [fdom_insert])
  >- (`~(x' = x)` by (fs [fdom_def] >> metis_tac[])
       >> `fdom cmp (insert cmp x v bmap) x'` by rw [fdom_insert,IN_DEF]
       >> `good_cmp cmp` by metis_tac [eq_cmp_def]
       >> `lookup cmp x' (insert cmp x v bmap) = lookup cmp x' t` by metis_tac[]
       >> pop_assum (SUBST_ALL_TAC o SYM)
       >> pat_elim `$!M`
       >> rw_tac set_ss [lookup_insert_thm]
       >> metis_tac [eq_cmp_def]));

val set_lem = Q.prove
(`!x s t. x IN s ==> (s UNION t = s UNION (x INSERT t))`,
 rw_tac set_ss [SET_EQ_THM] >> metis_tac []);

val fapply_def =
 Define
  `fapply cmp bmap x = THE (lookup cmp x bmap)`;

val extend_states_thm = Q.prove
(`!next_state state_map table states next_state' state_map' table'.
  (extend_states next_state state_map table states = (next_state',state_map',table'))
  /\ invariant regexp_compare state_map
   ⇒
  (fdom regexp_compare state_map' = (fdom regexp_compare state_map UNION set (MAP SND states))) ∧
  submap regexp_compare state_map state_map' ∧
  next_state ≤ next_state' ∧
  (table' = REVERSE (MAP (\(c,r). (c, fapply regexp_compare state_map' r)) states) ++ table) /\
  invariant regexp_compare state_map'`
 ,
 `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
  >> ho_match_mp_tac extend_states_ind
  >> rw [extend_states_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> `invariant regexp_compare (insert regexp_compare r' next_state state_map)`
       by metis_tac [insert_thm,eq_cmp_def]
  >> fs [submap_id]
  >> res_tac
  >- (rw_tac set_ss [fdom_insert] >> metis_tac[])
  >- (`r' IN fdom regexp_compare state_map` by rw [fdom_def]
       >> rw_tac set_ss [set_lem])
  >- (match_mp_tac submap_insert
      >> rw [fdom_def]
      >> metis_tac [NOT_SOME_NONE])
  >- decide_tac
  >- (pat_elim `$! M` >> rw[]
       >> qpat_x_assum `submap _ __ ___` mp_tac
      >> rw_tac set_ss [submap_def,fapply_def]
      >> pop_assum (mp_tac o Q.SPEC `r'`)
      >> rw [fdom_insert]
      >> pop_assum mp_tac
      >> `good_cmp regexp_compare` by metis_tac [regexp_compare_good]
      >> rw [lookup_insert_thm,regexp_compare_eq]
      >> metis_tac [THE_DEF])
  >- (pat_elim `$! M` >> rw[]
       >> qpat_x_assum `submap _ __ ___` mp_tac
      >> rw_tac set_ss [submap_def,fapply_def]
      >> pop_assum (mp_tac o Q.SPEC `r'`)
      >> rw [fdom_def]
      >> metis_tac [THE_DEF])
);

val good_table_def =
 Define
  `good_table state_map table =
    (ALL_DISTINCT (MAP FST table) ∧
    (!n table2.
       (ALOOKUP table n = SOME table2)
       ⇒
       (set (MAP FST table2) = set ALPHABET)) ∧
    (!n c n' table2.
       (ALOOKUP table n = SOME table2) ∧
       (ALOOKUP table2 c = SOME n')
       ⇒
       MEM c ALPHABET ∧
       ?r r'.
         (lookup regexp_compare r state_map = SOME n) ∧
         (lookup regexp_compare r' state_map = SOME n') ∧
         (r' = smart_deriv c r)))`;

val invar_def = Define `invar = invariant regexp_compare`;
val dom_def   = Define `dom = fdom regexp_compare`;
val range_def = Define `range = frange regexp_compare`;
val union_def = Define `union = ounion regexp_compare`;
val set_def   = Define `set = oset regexp_compare`;
val image_def = Define `image = oimage regexp_compare`;
val apply_def = Define `apply = fapply regexp_compare`;

val Brz_invariant_def =
 Define
  `Brz_invariant seen todo (next_state,state_map,table) ⇔
    invar state_map /\ invar seen /\
    EVERY is_normalized todo ∧
    (!r. mem_regexp r seen ⇒ is_normalized r) ∧
    (!r. r ∈ dom state_map ⇒ is_normalized r) ∧
    (dom (union seen (set todo)) = dom state_map) ∧
    (range state_map = count next_state) ∧
    (set (MAP FST table) = fdom num_cmp (oimage num_cmp (apply state_map) seen)) ∧
    fmap_inj regexp_compare state_map ∧
    good_table state_map table`;

val lem = Q.prove (
`!b c d e f. Brz_invariant b c (d,e,f) ⇒ EVERY is_normalized c`,
 rw [Brz_invariant_def]);

val fdom_ounion = Q.prove
(`!a b. good_cmp cmp /\ invariant cmp a /\ invariant cmp b
     ==> (fdom cmp (ounion cmp a b) = (fdom cmp a) UNION (fdom cmp b))`,
 rw[fdom_def,ounion_def,SET_EQ_THM]
  >> metis_tac [regexp_compare_good,good_oset_def,
       SIMP_RULE std_ss [oin_def,ounion_def,
                         member_iff_lookup,oneTheory.one] oin_ounion]);

val dom_union = Q.prove
(`!a b. invariant regexp_compare a /\ invariant regexp_compare b
        ==> (dom (union a b) = (dom a) UNION (dom b))`,
 metis_tac [regexp_compare_good,fdom_ounion,dom_def,union_def])

val invariant_oset = Q.store_thm
("invariant_oset",
 `!l. good_cmp cmp ==> invariant cmp (oset cmp l)`,
 simp_tac std_ss [oset_def]
   >> Induct
   >> fs [oempty_def,empty_def,oinsert_def]
   >- metis_tac [invariant_def]
   >- metis_tac [insert_thm]);

val in_dom_oset = Q.store_thm
("in_dom_oset",
 `!l x. eq_cmp cmp ==> (x IN fdom cmp (oset cmp l) <=> MEM x l)`,
 Induct >> rw []
  >- rw [oempty_def,empty_def,fdom_def,lookup_def]
  >- (`good_cmp cmp` by metis_tac [eq_cmp_def]
       >> imp_res_tac invariant_oset >> pop_assum (assume_tac o Q.SPEC `l`)
       >> rw [oset_def]
       >> rw [GSYM oset_def]
       >> rw [oinsert_def]
       >> rw_tac set_ss [fdom_insert]));

val dom_set_append = Q.store_thm
("dom_set_append",
 `!l1 l2. dom (set (l1++l2)) = dom (set l1) UNION dom (set l2)`,
 rw[dom_def,set_def,EXTENSION] >>
 `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare] >>
 rw [in_dom_oset]);

val member_insert = Q.store_thm
("member_insert",
 `!bmap x y v.
    eq_cmp cmp /\ invariant cmp bmap ==>
    (member cmp x (insert cmp y v bmap) <=> (x=y) \/ member cmp x bmap)`,
 rw [member_iff_lookup,GSYM (SIMP_RULE set_ss [SET_EQ_THM] fdom_def)] >>
 rw [fdom_insert] >> metis_tac [IN_DEF]);

val triv_lem = Q.prove(`!s1 s2. (s1 = s2) ==> ((s1 UNION s) = (s2 UNION s))`,rw[]);

val dom_oset_lem = Q.prove
(`!l. eq_cmp cmp ==> (fdom cmp (oset cmp l) = LIST_TO_SET l)`,
 rw [EXTENSION,in_dom_oset,eq_cmp_regexp_compare]);

val mem_foldrWithKey = Q.prove
(`!(bset:'a oset) acc a. eq_cmp cmp /\ invariant cmp bset ==>
     (MEM (a,()) (foldrWithKey (\k x xs. (k,())::xs) acc bset)
            <=>
      (a IN fdom cmp bset) \/ MEM (a,()) acc)`,
simp_tac set_ss [fdom_def]
 >> Induct >> rw [foldrWithKey_def,invariant_def] >> fs []
 >- rw [lookup_def]
 >- (`good_cmp cmp` by metis_tac [eq_cmp_def]
      >> rw [lookup_bin,EQ_IMP_THM]
      >> metis_tac [key_greater_lookup,key_less_lookup,good_cmp_thm,eq_cmp_def]));

val mem_foldrWithKey_lem =
    mem_foldrWithKey
      |> Q.SPEC `bset`
      |> Q.SPEC `[]`
      |> SIMP_RULE list_ss []

val left_to_right = Q.prove
(`eq_cmp cmp ==>
   !list bmap k v. invariant cmp bmap /\
        (lookup cmp k (FOLDR (λ(k,v) t. insert cmp k v t) bmap list) = SOME v)
            ==>
           (MEM (k,v) list \/ (lookup cmp k bmap = SOME v))`,
 strip_tac
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> Induct
     >- rw []
     >- (Cases_on `h` >> rw []
          >> pop_assum mp_tac
          >> `invariant cmp (FOLDR (λ(k,v) t. insert cmp k v t) bmap list)`
               by (Q.SPEC_TAC (`list`,`L`)
                     >> Induct >> rw [invariant_def]
                     >> Cases_on `h` >> rw [] >> metis_tac [insert_thm])
          >> rw [lookup_insert_thm]
          >> metis_tac [eq_cmp_def]));

val invariant_ffoldr = Q.prove
(`!list aset f.
   good_cmp cmp /\ invariant cmp aset
   ==>
   invariant cmp (FOLDR (λ(k,v) t. insert cmp (f k) v t) aset list)`,
  Induct >> rw [invariant_def]
         >> Cases_on `h` >> rw [] >> metis_tac [insert_thm]);

val invariant_ffoldr_inst =
    invariant_ffoldr
      |> INST_TYPE [beta |-> ``:unit``, gamma |-> beta]

val left_to_right_alt = Q.prove
(`eq_cmp (cmp:'b->'b->ordering)
   ==>
   !(list :('a # unit) list) (bset :'b oset) x f.
      invariant cmp bset /\
      (lookup cmp x (FOLDR (λ(k,v:unit) t. insert cmp (f k) () t) bset list) = SOME ())
            ==>
           (?a. MEM (a,()) list /\ (x = f a))
           \/
           ((!a. MEM (a,()) list ==> (x <> f a)) /\ (lookup cmp x bset = SOME ()))`,
 strip_tac
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> Induct
     >- rw []
     >- (Cases_on `h` >> rw [] >> fs []
          >> pop_assum mp_tac
          >> `invariant cmp (FOLDR (λ(k,v:unit) t. insert cmp (f k) () t) bset list)`
               by (Q.SPEC_TAC (`list`,`L`)
                     >> Induct >> rw [invariant_def]
                     >> Cases_on `h` >> rw [] >> metis_tac [insert_thm])
          >> rw [lookup_insert_thm]
          >> metis_tac [eq_cmp_def]));

val left_to_right_lem =
    left_to_right_alt
      |> Q.GEN `cmp`
      |> Q.SPEC `cmp2`
      |> UNDISCH
      |> Q.SPEC `foldrWithKey (λ(k:'a) (x:unit) xs. (k,())::xs) [] aset`
      |> Q.SPEC `Tip`
      |> Q.SPEC `x`
      |> Q.SPEC `f`
      |> DISCH_ALL;

val oin_fdom = Q.prove
(`!aset x. oin cmp x aset <=> x IN fdom cmp aset`,
 rw [fdom_def, oin_def, member_iff_lookup]);

val mem_oin = Q.prove
(`!list x aset.
     eq_cmp cmp /\ invariant cmp aset /\
     MEM (x,()) list
      ==>
     oin cmp (f x) (FOLDR (\(k,u) s. insert cmp (f k) () s) aset list)`,
 Induct >> rw [oin_fdom]
  >> `good_cmp cmp` by metis_tac [eq_cmp_def]
  >> mp_tac (SPEC_ALL invariant_ffoldr_inst)
  >| [all_tac, Cases_on `h`]
  >> rw[fdom_insert]
  >> metis_tac [oin_fdom,IN_DEF]);

val mem_oin_inst =
   mem_oin
   |> SPEC_ALL
   |> Q.INST [`cmp` |-> `cmp2`, `aset` |-> `Tip`, `x` |-> `x'`]
   |> Q.GEN `list`

val fdom_oimage = Q.store_thm
("fdom_image",
 `!aset:'a oset.
     eq_cmp (cmp1:'a->'a->ordering) /\
     eq_cmp (cmp2:'b->'b->ordering) /\ invariant cmp1 aset
    ==> (fdom cmp2 (oimage cmp2 f aset) = {f x | oin cmp1 x aset})`,
simp_tac set_ss
   [oimage_def,map_keys_def,balanced_mapTheory.fromList_def,fdom_def,
    toAscList_def,empty_def,
    rich_listTheory.FOLDR_MAP,LAMBDA_PROD,oneTheory.one]
 >> rw [EQ_IMP_THM]
    >- (mp_tac left_to_right_lem >> rw[invariant_def]
        >- (qexists_tac `a` >> rw[]
             >> pat_elim `lookup _ __ ___ = SOME ()`
             >> pat_elim `eq_cmp cmp2`
             >> `a IN fdom cmp1 aset` by metis_tac [mem_foldrWithKey_lem]
             >> pop_assum mp_tac
             >> rw[oin_def,member_iff_lookup,fdom_def])
        >- fs [lookup_def])
    >- (`MEM (x',()) (foldrWithKey (λk x xs. (k,())::xs) [] aset)`
          by metis_tac [oin_fdom,IN_DEF, mem_foldrWithKey_lem]
         >> mp_tac mem_oin_inst >> rw [invariant_def]
         >> res_tac
         >> fs [oin_def,member_iff_lookup,oneTheory.one])
);

val fdom_oimage_rw =
 fdom_oimage
   |> SIMP_RULE set_ss [GSPECIFICATION_applied];

val fdom_oimage_insert = Q.prove
(`!bset a f cmp1 cmp2.
    eq_cmp (cmp1:'a->'a->ordering) /\
     eq_cmp (cmp2:'b->'b->ordering) /\ invariant cmp1 bset
         ==> (fdom cmp2 (oimage cmp2 f (oinsert cmp1 a bset))
               =
              ((f a) INSERT fdom cmp2 (oimage cmp2 f bset)))`,
rpt strip_tac
 >> `invariant cmp1 (oinsert cmp1 a bset)` by metis_tac [insert_thm, eq_cmp_def,oinsert_def]
 >> mp_tac fdom_oimage_rw >> asm_simp_tac bool_ss[]
 >> rw_tac set_ss []
 >> `good_cmp cmp1 /\ good_cmp cmp2` by metis_tac [eq_cmp_def]
 >> rw [oin_def, member_iff_lookup, oinsert_def]
 >> fs [eq_cmp_def,lookup_insert_thm]
 >> metis_tac[]);


val fdom_oimage_inst =
   fdom_oimage
   |> INST_TYPE [alpha |-> ``:regexp``, beta |-> ``:num``]
   |> Q.INST [`cmp1` |-> `regexp_compare`, `cmp2` |-> `num_cmp`]
   |> SIMP_RULE std_ss [eq_cmp_regexp_compare,num_cmp_good,num_cmp_antisym,eq_cmp_def]

val Brz_inv_pres = Q.prove (
`!todo1 todos seen next_state state_map table.
  Brz_invariant seen (todo1::todos) (next_state,state_map,table) ∧
  ~mem_regexp todo1 seen
 ⇒
  Brz_invariant (insert_regexp todo1 seen)
                (MAP SND (transitions todo1) ++ todos)
                (build_table (transitions todo1)
                             todo1 (next_state,state_map,table))`,
 rw_tac list_ss [good_table_def,insert_regexp_def, invar_def,
                 Brz_invariant_def, build_table_def, transitions_def,set_def] >>
 imp_res_tac extend_states_thm >>
 `todo1 IN dom state_map`
   by (qpat_x_assum `dom (union a b) = dom state_map` (mp_tac o SYM) >> rw [] >>
       `invariant regexp_compare
         (oset regexp_compare (todo1::todos))` by metis_tac [invariant_oset,regexp_compare_good]
       >> rw [dom_union]
       >> disj2_tac
       >> `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
       >> rw [dom_def,in_dom_oset])
   >>
 `todo1 IN dom state_map'` by metis_tac [submap_def,dom_def]
 >>
 pop_assum (strip_assume_tac o SIMP_RULE set_ss [dom_def, fdom_def]) >> rw [] >>
  rw [Brz_invariant_def, good_table_def,invar_def]
  >- metis_tac [insert_thm,regexp_compare_good]
  >- (rw [EVERY_MAP] >> Q.SPEC_TAC (`ALPHABET`,`alphabet`)
       >> Induct >> rw [smart_deriv_normalized])
  >- metis_tac [member_insert,mem_regexp_def,eq_cmp_regexp_compare,insert_thm,eq_cmp_def]
  >- (`r IN fdom regexp_compare state_map \/
       r IN set (MAP SND (MAP (λc. (c,smart_deriv c todo1)) ALPHABET))`
       by metis_tac [EXTENSION,dom_def,IN_UNION]
       >- metis_tac [dom_def]
       >- (fs [MAP_MAP_o,MEM_MAP] >> metis_tac [smart_deriv_normalized, dom_def]))
  >- (fs [GSYM dom_def] >> qpat_x_assum `dom _ = dom __` (assume_tac o SYM)
       >> rw [GSYM set_def]
       >> `invariant regexp_compare (insert regexp_compare todo1 () seen)`
            by metis_tac [insert_thm,regexp_compare_good]
       >> `invariant regexp_compare
             (set (MAP SND (MAP (λc. (c,smart_deriv c todo1)) ALPHABET) ++ todos))`
           by metis_tac [invariant_oset, set_def,regexp_compare_good]
       >> `invariant regexp_compare (set (todo1::todos))`
          by metis_tac [invariant_oset, set_def, regexp_compare_good]
       >> rw [dom_union]
       >> rw_tac bool_ss [Once CONS_APPEND,dom_set_append]
       >> `dom (insert regexp_compare todo1 () seen) =
           dom (set [todo1]) UNION dom seen`
            by (rw [dom_def,fdom_insert,eq_cmp_regexp_compare,Once INSERT_SING_UNION]
                >> match_mp_tac triv_lem
                >> rw_tac bool_ss [EXTENSION,set_def]
               >> rw [in_dom_oset,eq_cmp_regexp_compare])
       >> rw []
       >> rw [AC UNION_COMM UNION_ASSOC]
       >> metis_tac [dom_oset_lem,eq_cmp_regexp_compare,dom_def,set_def])
  >- (`extend_states_inv next_state state_map ([]:(num,num) alist)`
               by (rw [extend_states_inv_def] >> metis_tac [range_def])
       >> imp_res_tac extend_states_inv
       >> fs [extend_states_inv_def, count_def, EXTENSION, range_def])
  >- (`todo1 IN dom state_map'` by (fs[submap_def] >> metis_tac[dom_def])
      >> `eq_cmp num_cmp /\ eq_cmp regexp_compare`
            by metis_tac[eq_cmp_regexp_compare,num_cmp_good,num_cmp_antisym,eq_cmp_def]
      >> rw [GSYM oinsert_def,fdom_oimage_insert]
      >> `apply state_map' todo1 = x` by rw [apply_def,fapply_def]
      >> pop_assum SUBST_ALL_TAC
      >> AP_TERM_TAC
      >> `dom seen SUBSET dom state_map` by
           (qpat_x_assum `dom _ = dom state_map` (SUBST_ALL_TAC o SYM)
             >> metis_tac [invariant_oset, eq_cmp_def,dom_union,SUBSET_UNION])
      >> rw[fdom_oimage_inst,SET_EQ_THM,EQ_IMP_THM,oin_fdom]
      >> Q.EXISTS_TAC `x''` >> rw[]
      >> `x'' IN dom state_map` by metis_tac [SUBSET_DEF,dom_def]
      >> `(x'' IN dom state_map') /\
          (lookup regexp_compare x'' state_map = lookup regexp_compare x'' state_map')`
           by metis_tac [submap_def,dom_def]
      >> rw [apply_def,fapply_def])
  >- (`extend_states_inv next_state state_map ([]:(num,num) alist)`
               by (rw [extend_states_inv_def] >> metis_tac [range_def])
       >> imp_res_tac extend_states_inv
       >> pop_assum mp_tac
       >> rw [extend_states_inv_def])
  >- (rw_tac set_ss [fdom_oimage_inst,GSYM IMP_DISJ_THM,oneTheory.one,
                     oin_fdom,fdom_def,apply_def,fapply_def]
       >> strip_tac
       >> `fmap_inj regexp_compare state_map'`
           by (`extend_states_inv next_state state_map ([]:(num,num) alist)`
                 by (rw [extend_states_inv_def] >> metis_tac [range_def])
               >> imp_res_tac extend_states_inv
               >> pop_assum mp_tac
               >> rw [extend_states_inv_def])
       >> `dom seen SUBSET dom state_map` by
           (`eq_cmp num_cmp /\ eq_cmp regexp_compare`
                by metis_tac[eq_cmp_regexp_compare,
                             num_cmp_good,num_cmp_antisym,eq_cmp_def]
             >> qpat_x_assum `dom _ = dom state_map` (SUBST_ALL_TAC o SYM)
             >> metis_tac [invariant_oset, eq_cmp_def,dom_union,SUBSET_UNION])
       >> pop_assum mp_tac
       >> rw_tac set_ss [dom_def, fdom_def, member_iff_lookup,SUBSET_DEF,oneTheory.one]
       >> Q.EXISTS_TAC `x'` >> rw[]
       >> strip_tac
       >> `x' IN fdom regexp_compare state_map` by fs [SUBSET_DEF,dom_def, fdom_def]
       >> `(x' IN fdom regexp_compare state_map') /\
           (lookup regexp_compare x' state_map = lookup regexp_compare x' state_map')`
             by (fs [submap_def,fdom_def, member_iff_lookup] >> metis_tac [])
       >> fs []
       >> `x' <> todo1` by (fs[mem_regexp_def,member_iff_lookup] >> metis_tac[])
       >> metis_tac [fmap_inj_def,eq_cmp_regexp_compare, eq_cmp_def])
  >- (pop_assum mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
        >> fs[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF]
        >> metis_tac[])
  >- (qpat_x_assum `(if _ then __ else ___) = ____` mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
             >- (imp_res_tac alistTheory.ALOOKUP_MEM
                  >> fs [MEM_REVERSE,MEM_MAP])
             >- metis_tac[])
  >- (qpat_x_assum `(if _ then __ else ___) = ____` mp_tac
        >> rw[MAP_MAP_o,combinTheory.o_DEF]
           >- (qexists_tac `todo1` >> rw[]
                  >> imp_res_tac alistTheory.ALOOKUP_MEM
                  >> pop_assum mp_tac
                  >> rw_tac set_ss [MEM_REVERSE,MEM_MAP,fapply_def]
                  >> `smart_deriv c todo1 IN fdom regexp_compare state_map'`
                      by (rw [MAP_MAP_o,combinTheory.o_DEF,MEM_MAP]
                           >> disj2_tac
                           >> qexists_tac `c` >> rw[]
                           >> metis_tac [IN_DEF])
                  >> fs [fdom_def, member_iff_lookup])
           >- (fs[submap_def, fdom_def, member_iff_lookup] >> metis_tac[]))
);


val Brz_invariant_alt = Q.prove
(`!seen worklist worklist' acc.
   (LIST_TO_SET worklist = LIST_TO_SET worklist')
   ==>
   (Brz_invariant seen worklist acc = Brz_invariant seen worklist' acc)`,
rpt strip_tac >> PairCases_on `acc`
 >> rw[Brz_invariant_def,EQ_IMP_THM]
 >> ((qpat_x_assum `EVERY _ __` mp_tac >>
        qpat_x_assum `LIST_TO_SET _ = LIST_TO_SET __` mp_tac
         >> rw [EVERY_MEM]
         >> NO_TAC)
    ORELSE
     (qpat_x_assum `dom _ = dom __` (SUBST_ALL_TAC o SYM)
         >> fs [invar_def]
         >> `invariant regexp_compare (set worklist') /\
             invariant regexp_compare (set worklist)`
              by metis_tac [invariant_oset,set_def, regexp_compare_good]
          >> rw [dom_union,EXTENSION]
          >> `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
          >> rw [in_dom_oset,dom_def,set_def])));

val Brz_inv_thm = Q.prove
(`!seen worklist acc.
   dom_Brz seen worklist acc
   ==>
    !seen' acc'.
      Brz_invariant seen worklist acc ∧
      (Brzozowski seen worklist acc = (seen',acc'))
      ==>
       Brz_invariant seen' [] acc'`,
 ho_match_mp_tac Brzozowski_ind
   >> rw []
   >> qpat_x_assum `Brzozowski _ __ ___ = _4` mp_tac
   >> rw [Brzozowski_eqns]
   >> pop_assum mp_tac
   >> CASE_TAC
   >> rw[]
      >- metis_tac[]
      >- (rfs []
          >> first_assum match_mp_tac
          >> qpat_x_assum `Brz_invariant seen (h::t) args` mp_tac
          >> PairCases_on `acc`
          >> rw [Brz_invariant_def]
          >> qpat_x_assum `dom _ = dom __` (SUBST_ALL_TAC o SYM)
          >> fs [invar_def]
          >> `invariant regexp_compare (set t) /\
              invariant regexp_compare (set (h::t))`
              by metis_tac [invariant_oset,set_def, regexp_compare_good]
          >> rw [dom_union,EXTENSION]
          >> `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
          >> rw [in_dom_oset,dom_def,set_def]
          >> fs [mem_regexp_def, member_iff_lookup]
          >> rw [fdom_def]
          >> metis_tac[])
      >- (rfs [LET_THM]
          >> rw[]
          >> pat_elim `_ = __`
          >> PairCases_on `acc`
          >> imp_res_tac Brz_inv_pres
          >> `LIST_TO_SET (remove_dups (MAP SND (transitions h)) ++ t) =
              LIST_TO_SET (MAP SND (transitions h) ++ t)`
                    by rw [EXTENSION,remove_dups_mem]
          >> metis_tac [Brz_invariant_alt]))

val Brz_mono = Q.prove
(`!seen worklist acc.
  dom_Brz seen worklist acc
 ==>
 !seen' acc'.
    Brz_invariant seen worklist acc /\
    (Brzozowski seen worklist acc = (seen',acc'))
  ==>
    submap regexp_compare (FST (SND acc)) (FST(SND acc'))`,
 ho_match_mp_tac Brzozowski_ind
 >> Cases_on `worklist`
    >- (rw []
         >> qpat_x_assum `Brzozowski _ __ ___ = _4` mp_tac
         >> rw [Brzozowski_eqns,submap_id])
    >- (rw []
         >> qpat_x_assum `Brzozowski _ __ ___ = _4` mp_tac
         >> rw [Brzozowski_eqns]
         >> fs[LET_THM]
            >- (first_assum match_mp_tac
                >> qpat_x_assum `Brz_invariant seen (h::t) acc` mp_tac
                >> PairCases_on `acc`
                >> rw [Brz_invariant_def]
                >> qpat_x_assum `dom _ = dom __` (SUBST_ALL_TAC o SYM)
                >> fs [invar_def]
                >> `invariant regexp_compare (set t) /\
                    invariant regexp_compare (set (h::t))`
                      by metis_tac [invariant_oset,set_def, regexp_compare_good]
                >> rw [dom_union,EXTENSION]
                >> `eq_cmp regexp_compare` by metis_tac [eq_cmp_regexp_compare]
                >> rw [in_dom_oset,dom_def,set_def]
                >> fs [mem_regexp_def, member_iff_lookup]
                >> rw [fdom_def]
                >> metis_tac[])
            >- (rw[]
                >> pat_elim `_ = __`
                >> PairCases_on `acc`
                >> imp_res_tac Brz_inv_pres
                >> `LIST_TO_SET (remove_dups (MAP SND (transitions h)) ++ t) =
                    LIST_TO_SET (MAP SND (transitions h) ++ t)`
                        by rw [EXTENSION,remove_dups_mem]
                >> imp_res_tac Brz_invariant_alt
                >> fs[]
                >> NTAC 3 (pop_assum (K ALL_TAC))
                >> match_mp_tac submap_trans
                >> qexists_tac `FST (SND (build_table (transitions h) h (acc0,acc1,acc2)))`
                >> rw[build_table_def,LET_THM]
                >> `?x state_map'' z. extend_states acc0 acc1 [] (transitions h) = (x,state_map'',z)`
                       by metis_tac [pair_CASES]
                >> fs[]
                >> `invariant regexp_compare acc1`
                     by metis_tac [Brz_invariant_def, invar_def]
                >> imp_res_tac extend_states_thm
                >> rw []
                >> CASE_TAC
                >> fs []
                >> match_mp_tac submap_mono
                >> rw[eq_cmp_regexp_compare]
                >> qpat_x_assum `submap _ __ ___` mp_tac
                >> rw [submap_def]
                >> strip_tac
                >> res_tac
                >> fs [fdom_def]
                >> metis_tac [NOT_SOME_NONE])));

(*---------------------------------------------------------------------------*)
(* table_lang                                                                *)
(*---------------------------------------------------------------------------*)

val table_lang_def =
 Define
  `(table_lang final_states table n [] = MEM n final_states) /\
   (table_lang final_states table n (c::t) =
     case ALOOKUP table n of
       | NONE => F
       | SOME table2 =>
           case ALOOKUP table2 c of
             | NONE => F
             | SOME n' => table_lang final_states table n' t)`;

val table_lang_correct = Q.prove
(`!finals table state_map.
  fmap_inj regexp_compare state_map ∧
  good_table state_map table ∧
  (set (MAP FST table) = frange regexp_compare state_map) ∧
  (!n r. (lookup regexp_compare r state_map = SOME n) ⇒ (MEM n finals ⇔ nullable r))
  ⇒
  !n r s.
    (!c. MEM c s ⇒ MEM c ALPHABET) ∧
    (lookup regexp_compare r state_map = SOME n)
    ⇒
    (table_lang finals table n s ⇔ smart_deriv_matches r (MAP CHR s))`,
 rpt gen_tac >>
 strip_tac >>
 Induct_on `s` >>
 rw [table_lang_def, smart_deriv_matches_def] >>
 fs [good_table_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 rw []
 >- (imp_res_tac alistTheory.ALOOKUP_NONE
     >> fs [EXTENSION]
     >> `n NOTIN frange regexp_compare state_map` by metis_tac[]
     >> fs [frange_def])
 >- metis_tac [alistTheory.ALOOKUP_NONE]
 >- (`∃r'.(lookup regexp_compare r' state_map = SOME n) /\
          (lookup regexp_compare (smart_deriv h r') state_map =
           SOME x')` by metis_tac []
     >> `table_lang finals table x' s <=>
         smart_deriv_matches (smart_deriv h r') (MAP CHR s)`
         by metis_tac[]
     >> pop_assum SUBST_ALL_TAC
     >> `r' = r`
         by (qpat_x_assum `fmap_inj _ __` mp_tac
              >> rw_tac set_ss [fmap_inj_def,fdom_def,regexp_compare_eq])
     >> rw []
     >> metis_tac [ORD_CHR_lem,mem_alphabet]))

val vec_lang_lem1 = Q.prove
(`∀(n:num). MEM n finals_list ⇔
           (ALOOKUP (MAP (λx. (x,T)) finals_list) n = SOME T)`,
 rw [EQ_IMP_THM]
  >- rw [alistTheory.ALOOKUP_TABULATE]
  >- (`MEM (n,T) (MAP (λx. (x,T)) finals_list)` by METIS_TAC [alistTheory.ALOOKUP_MEM]
      >> fs[MEM_MAP]));

val vec_lang_lem2 =
  alistTheory.alookup_stable_sorted
     |> Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:(num, 'a) alist`]
     |> Q.SPECL [`$<=`, `mergesort`, `n`, `table`]
     |> SIMP_RULE (srw_ss()++ARITH_ss) [transitive_def, total_def, mergesort_STABLE_SORT];

(* Following are a bit suss because of use of ORD *)
val vec_lang_lem3 =
  alistTheory.alookup_stable_sorted
     |> Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:'a option`]
     |> Q.SPECL [`$<=`, `mergesort`, `n`, `MAP (λ(c,n). (c,SOME n)) table2`]
     |> SIMP_RULE (srw_ss()++ARITH_ss)
           [transitive_def, total_def, mergesort_STABLE_SORT, stringTheory.char_le_def];

val vec_lang_lem4 = Q.prove (
`!l x. ALOOKUP (MAP (λ(c,n). (c,SOME n)) l) x =
       OPTION_MAP SOME (ALOOKUP l x)`,
 Induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 fs [stringTheory.ORD_11]);

val leq_thm =
 let val leq = numSyntax.leq_tm
 in Q.prove (`transitive ^leq ∧ total ^leq ∧ antisymmetric ^leq`,
    srw_tac [ARITH_ss] [transitive_def, total_def, antisymmetric_def])
 end;

val length_mergesort = Q.prove
(`!l R. LENGTH (mergesort R l) = LENGTH l`,
 metis_tac[mergesort_perm,PERM_LENGTH]);

val table_to_vec_thm = Q.prove (
`!table final_states max_char max_state table' final_states'.
  (max_char = alphabet_size) /\
  SORTED $<= final_states /\
  (!x. MEM x final_states ⇒ x < max_state) ∧
  (!n l c. (ALOOKUP table n = SOME l) ∧ (?x. ALOOKUP l c = SOME x) ⇒ c < max_char) ∧
  PERM (MAP FST table) (COUNT_LIST (LENGTH table)) ∧
  (table_to_vectors table = table') /\
  (accepts_to_vector final_states max_state = final_states')
  ⇒
  (LENGTH table' = LENGTH table) ∧
  (LENGTH final_states' = max_state) ∧
  (!n. MEM n final_states ⇔ n < LENGTH final_states' ∧ EL n final_states') ∧
  (!n. (?l. ALOOKUP table n = SOME l) ⇔ n < LENGTH table') ∧
  (!n l. n < LENGTH table' ⇒ (LENGTH (EL n table') = max_char)) ∧
  (!n c x.
    (?l. (ALOOKUP table n = SOME l) ∧ (ALOOKUP l c = SOME x)) ⇔
    n < LENGTH table' ∧ c < LENGTH (EL n table') ∧ (EL c (EL n table') = SOME x))`
 ,
 simp [good_table_def, table_to_vectors_def,accepts_to_vector_def] >>
 rpt gen_tac >>
 strip_tac >>
(* `FINITE final_states` by metis_tac [finite_bounded] >> *)
 qabbrev_tac `sorted_table = mergesort (inv_image $<= FST) table` >>
 `LENGTH sorted_table = LENGTH table` by metis_tac [mergesort_perm, PERM_LENGTH] >>
 `SORTS mergesort (inv_image $<= (FST : num # (num,'a) alist -> num))`
          by metis_tac [mergesort_STABLE_SORT, STABLE_DEF,
                        leq_thm, total_inv_image, transitive_inv_image] >>
 `MAP FST sorted_table = COUNT_LIST (LENGTH table)`
            by (match_mp_tac sorted_perm_count_list >>
                fs [SORTS_DEF] >>
                rw [] >>
                metis_tac [PERM_TRANS, PERM_SYM, PERM_MAP]) >>
 simp [] >>
 conj_tac
 >- metis_tac[mergesort_perm,PERM_LENGTH] >>
 conj_tac
 >- (`SORTED $<= (MAP FST (MAP (\x.(x,T)) final_states))`
            by rw [MAP_MAP_o, combinTheory.o_DEF]
      >> metis_tac [alist_to_vec_thm]) >>
 conj_tac
 >- (`SORTED $<= (MAP FST (MAP (\x.(x,T)) final_states))`
            by rw [MAP_MAP_o, combinTheory.o_DEF]
     >> `LENGTH (alist_to_vec (MAP (λx. (x,T)) final_states)
                              F max_state max_state) = max_state`
           by METIS_TAC [alist_to_vec_thm]
    >> POP_ASSUM SUBST_ALL_TAC
    >> RW_TAC std_ss [EQ_IMP_THM]
       >- (`n < max_state` by METIS_TAC [] >>
           `ALOOKUP (MAP (λx. (x,T)) final_states) n = SOME T`
               by METIS_TAC [vec_lang_lem1] >> METIS_TAC [alist_to_vec_thm])
       >- (CCONTR_TAC >> fs []
           >> Cases_on `ALOOKUP (MAP (λx. (x,T)) final_states) n`
              >- (metis_tac [alist_to_vec_thm, vec_lang_lem1])
              >- (NTAC 2 (POP_ASSUM MP_TAC) >> rw [vec_lang_lem1]
                  >> DISCH_TAC >> fs[] >> rw[] >> metis_tac [alist_to_vec_thm])))
 >>
 conj_asm1_tac
 >- (rw [] >> eq_tac >> rw []
     >- (imp_res_tac alistTheory.ALOOKUP_MEM >>
         imp_res_tac MEM_PERM >>
         fs [MEM_MAP, MEM_COUNT_LIST] >>
         metis_tac [FST,mergesort_perm,PERM_LENGTH])
     >- (`ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [dense_alist_to_vec_thm, LENGTH_COUNT_LIST,mergesort_perm,PERM_LENGTH] >>
         `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [vec_lang_lem2] >>
         rw [])) >>
 `SORTS mergesort (inv_image $<= (FST : num # 'a option -> num))`
          by metis_tac [mergesort_STABLE_SORT, STABLE_DEF, leq_thm,
                        total_inv_image, transitive_inv_image] >>
 `(λa b:num. a ≤ b) = $<=` by metis_tac [] >> pop_assum SUBST_ALL_TAC >>
 simp [EL_MAP,length_mergesort] >>
 conj_tac
 >- (rw [] >>
     `?n' table2'. EL n sorted_table = (n',table2')` by metis_tac [pair_CASES] >>
     rw [] >>
     qabbrev_tac `sorted_table2 =
                  mergesort (inv_image $<= FST) (MAP (λ(c,n). (c,SOME n)) table2')` >>
     qabbrev_tac `table2 = EL n (MAP SND sorted_table)` >>
     `SORTED $<= (MAP FST sorted_table2)`
             by (fs [SORTS_DEF, sorted_map, leq_thm] >>
                 metis_tac []) >>
     metis_tac [alist_to_vec_thm])
 >- (* last conjunct *)
 (fs [length_mergesort] >>
  rw [] >>  eq_tac >>  strip_tac >>
  res_tac >>
 simp [EL_MAP] >>
 `?n' table2'. EL n sorted_table = (n',table2')` by metis_tac [pair_CASES] >>
 rw [] >>
 qabbrev_tac `sorted_table2 =
              mergesort (inv_image $<= FST) (MAP (λ(c,n). (c,SOME n)) table2')` >>
 qabbrev_tac `table2 = EL n (MAP SND sorted_table)` >>
 `SORTED $<= (MAP FST sorted_table2)`
         by (fs [SORTS_DEF, sorted_map, leq_thm] >>
             metis_tac [])
 >- metis_tac [alist_to_vec_thm]
 >- (imp_res_tac alist_to_vec_thm >>
     fs [AND_IMP_INTRO] >>
     FIRST_X_ASSUM match_mp_tac >>
     rw [] >>
     `table2' = table2`
            by (UNABBREV_ALL_TAC >>
                rw [EL_MAP]) >>
     rw [] >>
     `ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [dense_alist_to_vec_thm, LENGTH_COUNT_LIST] >>
     `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
                by metis_tac [vec_lang_lem2] >>
     rw [] >>
     fs [] >>
     `ALOOKUP (MAP (λ(c,n). (c,SOME n)) table2) c = SOME (SOME x)`
              by metis_tac [vec_lang_lem4, OPTION_MAP_DEF] >>
     fs [Once (GSYM vec_lang_lem3)] >>
     metis_tac [NOT_SOME_NONE, alist_to_vec_thm])
 >- (REV_FULL_SIMP_TAC std_ss [EL_MAP] >>
     `table2' = table2`
                by (UNABBREV_ALL_TAC >>
                    rw [EL_MAP]) >>
     fs [] >>
     res_tac >>
     simp [] >>
     Cases_on `ALOOKUP sorted_table2 c`
     >- (`ALOOKUP (MAP (λ(c,n). (c,SOME n)) table2) c = NONE`
                 by metis_tac [vec_lang_lem4, OPTION_MAP_DEF, vec_lang_lem3] >>
         metis_tac [NOT_SOME_NONE, alist_to_vec_thm])
    >- (`ALOOKUP sorted_table n = SOME (EL n (MAP SND sorted_table))`
           by metis_tac [dense_alist_to_vec_thm, LENGTH_COUNT_LIST] >>
        `ALOOKUP table n = SOME (EL n (MAP SND sorted_table))`
           by metis_tac [vec_lang_lem2] >>
        rw [] >>
        REV_FULL_SIMP_TAC std_ss [EL_MAP] >>
        `SOME x = x'` by metis_tac [SOME_11, alist_to_vec_thm] >>
        simp [] >>
        qunabbrev_tac `sorted_table2` >>
        fs [Once vec_lang_lem3] >>
        fs [vec_lang_lem4])))
);


val Brz_invariant_final = Q.prove (
`!seen next_state state_map table.
  Brz_invariant seen [] (next_state,state_map,table)
  ⇒
  (next_state = LENGTH table) ∧
  PERM (MAP FST table) (COUNT_LIST (LENGTH table)) ∧
  (∀x. MEM x (get_accepts state_map) ==> x < LENGTH table) ∧
  (∀n l c. (ALOOKUP table n = SOME l) ∧ (∃x. ALOOKUP l c = SOME x) ⇒ MEM c ALPHABET)`
 ,
 simp [Brz_invariant_def,invar_def,set_def,ounion_oempty,union_def] >>
 rpt gen_tac >> strip_tac >>
 conj_asm1_tac
 >- (`!x. x ∈ set (MAP FST table) ⇒ x < next_state`
           by (fs [count_def, EXTENSION, range_def, frange_def,dom_def]
                >> rw [fdom_oimage_inst,apply_def,oin_fdom]
                >> fs [fdom_def,fapply_def]
                >> metis_tac [THE_DEF]) >>
     `LENGTH table = CARD (set (MAP FST table))`
           by metis_tac [LENGTH_MAP,ALL_DISTINCT_CARD_LIST_TO_SET, good_table_def] >>
     `fdom num_cmp (oimage num_cmp (apply state_map) seen) = range state_map`
       by (simp_tac set_ss [range_def, frange_def] >>
           qpat_x_assum `dom _ = dom __` mp_tac >>
           rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
           simp_tac set_ss [fdom_def] >> metis_tac[THE_DEF])
     >> rw [])
>> conj_asm1_tac
    >- (match_mp_tac PERM_ALL_DISTINCT
          >> rw [all_distinct_count_list, MEM_COUNT_LIST]
              >- fs [good_table_def]
              >- (`fdom num_cmp (oimage num_cmp (apply state_map) seen) = range state_map`
                    by (simp_tac set_ss [range_def, frange_def] >>
                        qpat_x_assum `dom _ = dom __` mp_tac >>
                        rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
                        simp_tac set_ss [fdom_def] >> metis_tac[THE_DEF])
                    >> rw[]))
>> conj_tac
   >- (rw [mem_get_accepts]
      >> `x IN range state_map`
            by (simp_tac set_ss [range_def, frange_def] >> metis_tac[])
      >> rfs [count_def] )
   >- (rw [] >> fs [good_table_def] >> metis_tac [])
);

val good_vec_def =
 Define
  `good_vec vec final_states
      <=>
    (!l c. MEM c ALPHABET ∧ MEM l vec ⇒ c < LENGTH l) /\
    (!n1 c n2 l. n1 < LENGTH vec ∧ (EL n1 vec = l) ∧
                 c < LENGTH (EL n1 vec) ∧
                 (EL c (EL n1 vec) = SOME n2) ==> n2 < LENGTH vec) /\
    (LENGTH final_states = LENGTH vec)`;

val Brz_inv_to_good_vec = Q.prove
(`!seen next_state state_map table.
 Brz_invariant seen [] (next_state,state_map,table) ∧
  (table_to_vectors table = vec) /\
  (accepts_to_vector (get_accepts state_map) next_state = final_states)
  ==>
  (next_state = LENGTH table) ∧
  good_vec vec final_states ∧
  (∀r n. (lookup regexp_compare r state_map = SOME n) ⇒ n < LENGTH vec)`
 ,
 simp [good_vec_def]
  >> rpt gen_tac >> strip_tac
  >> imp_res_tac Brz_invariant_final
  >> fs [Brz_invariant_def,invar_def,
        ounion_oempty,union_def, set_def, oset_def]
  >>
  `(LENGTH vec = LENGTH table) ∧
   (LENGTH final_states = LENGTH table) ∧
   (∀n. MEM n (get_accepts state_map) ⇔ n < LENGTH final_states ∧ EL n final_states) ∧
   (∀n. (∃l. ALOOKUP table n = SOME l) ⇔ n < LENGTH vec) ∧
   (!n l. n < LENGTH vec ⇒ (LENGTH (EL n vec) = alphabet_size)) ∧
   (∀n c x.
     (∃l. (ALOOKUP table n = SOME l) ∧ (ALOOKUP l c = SOME x))
     <=>
       n < LENGTH vec ∧ c < LENGTH (EL n vec) ∧
       (EL c (EL n vec) = SOME x))`
     by
      (match_mp_tac table_to_vec_thm
        >> rw [sorted_get_accepts]
        >> metis_tac [mem_alphabet,alphabet_size_def])
  >> rw []
 >- (fs [MEM_EL] >> rw []
      >> metis_tac [EL_MEM,mem_alphabet,alphabet_size_def])
 >- (`!a. a < LENGTH table <=> MEM a (MAP FST table)`
        by metis_tac [MEM_PERM,MEM_COUNT_LIST]
      >> rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def,SYM dom_def]
      >> rw [dom_def,fdom_def, member_iff_lookup]
      >> metis_tac [good_table_def,THE_DEF])
 >- (`!a. a < LENGTH table <=> MEM a (MAP FST table)`
        by metis_tac [MEM_PERM,MEM_COUNT_LIST]
       >> rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def,SYM dom_def]
       >> simp_tac set_ss [dom_def,fdom_def, member_iff_lookup]
       >> metis_tac [THE_DEF]));

val compile_regexp_good_vec = Q.store_thm
("compile_regexp_good_vec",
`!r state_map table final_states.
  dom_Brz empty [normalize r] (1,singleton (normalize r) 0,[]) /\
  (compile_regexp r = (state_map, table, final_states))
  ==>
  good_vec table final_states ∧
  (!r n. (lookup regexp_compare r state_map = SOME n) ⇒ n < LENGTH table) ∧
  normalize r ∈ fdom regexp_compare state_map`
 ,
 simp [compile_regexp_def]
  >> rpt gen_tac >> strip_tac
  >> fs []
  >> `?seen next_state state_map table.
         Brzozowski empty [normalize r] (1,singleton (normalize r) 0,[])
          = (seen,next_state,state_map,table)`
       by metis_tac [pair_CASES]
  >> fs []
  >> `Brz_invariant empty [normalize r] (1,singleton (normalize r) 0,[])`
     by
      (fs [Brz_invariant_def,invar_def,dom_def, normalize_thm, fmap_inj_def, good_table_def,
          singleton_thm,empty_def,invariant_def,mem_regexp_def,member_iff_lookup]
        >> rw [lookup_def]
           >- (fs [fdom_def, singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw []
                >> metis_tac [eq_cmp_regexp_compare, eq_cmp_def,normalize_thm])
           >- (rw [union_def,set_def,GSYM empty_def, GSYM oempty_def] >>
               rw [EXTENSION,fdom_def, osingleton_def, singleton_def, lookup_def] >>
               CASE_TAC)
           >- (rw [range_def,frange_def, EXTENSION, singleton_def,lookup_def,EQ_IMP_THM]
                >- (BasicProvers.EVERY_CASE_TAC >> rw [])
                >- (Q.EXISTS_TAC `normalize r` >> rw [regexp_compare_id] >> decide_tac))
           >- (rw [GSYM empty_def, GSYM oempty_def]
               >> rw [fdom_def, lookup_def, empty_def, oempty_def])
           >- (ntac 2 (pop_assum mp_tac)
                >> simp_tac set_ss [fdom_def,singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw[]
                >> metis_tac [eq_cmp_def, eq_cmp_regexp_compare]))
 >> imp_res_tac Brz_inv_thm
 >> imp_res_tac Brz_mono
 >> imp_res_tac Brz_inv_to_good_vec
 >> fs []
 >> rw []
    >- metis_tac []
    >- (`normalize r ∈ fdom regexp_compare (singleton (normalize r) 0)`
         by rw [submap_def,fdom_def,singleton_def,lookup_def,regexp_compare_id]
         >> metis_tac [submap_def])
);


val vec_lang_correct = Q.prove
(`!table final_states max_char vec final_states'.
  (max_char = alphabet_size) /\
  SORTED $<= final_states /\
  (∀x. MEM x final_states ⇒ x < LENGTH table) ∧
  (∀n l c. (ALOOKUP table n = SOME l) ∧ (∃x. ALOOKUP l c = SOME x) ⇒ c < max_char) ∧
  (PERM (MAP FST table) (COUNT_LIST (LENGTH table))) ∧
  (!n'. n' ∈ BIGUNION (IMAGE alist_range (alist_range table)) ⇒ n' < LENGTH table) ∧
  (table_to_vectors table = vec) /\
  (accepts_to_vector final_states (LENGTH table) = final_states')
  ⇒
  !n s. (!c. MEM c s ⇒ c < max_char) ∧ n < LENGTH table
       ==>
        (table_lang final_states table n s
           <=>
         exec_dfa (fromList final_states')
                  (fromList (MAP fromList vec))
                  n
                  (MAP CHR s))`
 ,
 rpt gen_tac
  >> strip_tac
  >> `(LENGTH vec = LENGTH table) ∧
      (LENGTH final_states' = LENGTH table) ∧
      (∀n. MEM n final_states ⇔ n < LENGTH final_states' ∧ EL n final_states') ∧
      (∀n. (∃l. ALOOKUP table n = SOME l) ⇔ n < LENGTH vec) ∧
      (!n l. n < LENGTH vec ⇒ (LENGTH (EL n vec) = max_char)) ∧
      (∀n c x.
        (∃l. (ALOOKUP table n = SOME l) ∧ (ALOOKUP l c = SOME x))
        ⇔
        n < LENGTH vec ∧ c < LENGTH (EL n vec) ∧
        (EL c (EL n vec) = SOME x))`
        by (match_mp_tac table_to_vec_thm
             >> rw []
             >> metis_tac [])
  >> Induct_on `s`
  >> rw [table_lang_def, exec_dfa_thm,fromList_Vector,sub_def]
  >> `h < alphabet_size` by metis_tac []
  >> rw [ORD_CHR_lem]
  >> BasicProvers.EVERY_CASE_TAC
  >> fs []
     >- metis_tac [NOT_SOME_NONE]
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> metis_tac [SOME_11, NOT_SOME_NONE])
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> metis_tac [NOT_SOME_NONE])
     >- (`n < LENGTH (table_to_vectors table)` by metis_tac[]
         >> fs [EL_MAP,sub_def]
         >> `x' = x''` by metis_tac [SOME_11, NOT_SOME_NONE]
          >> rw []
          >> fs [fromList_Vector]
          >> FIRST_X_ASSUM match_mp_tac
          >> FIRST_X_ASSUM match_mp_tac
          >> rw [PULL_EXISTS]
          >> rw [alistTheory.alist_range_def, EXTENSION]
          >> metis_tac [])
);


val Brz_lang_def = Define `
  Brz_lang r =
    let (state_map,table_vec,finals_vec) = compile_regexp r in
    let tableV = fromList (MAP fromList table_vec) in
    let finalsV = fromList finals_vec
    in
      exec_dfa finalsV tableV (apply state_map (normalize r))`;

val string_to_numlist = Q.prove
(`!s. (!c. c IN set s ==> ORD c IN set ALPHABET) ==>
      ?nl. (s = MAP CHR nl) /\ (!n. n IN set nl ==> n IN set ALPHABET)`,
 Induct >> rw []
  >> `∃nl. (s = MAP CHR nl) ∧ ∀n. MEM n nl ⇒ MEM n ALPHABET` by metis_tac[]
  >> `?n. (h = CHR n) /\ n < 256` by metis_tac [CHR_ONTO]
  >> Q.EXISTS_TAC `n::nl`
  >> rw []
  >> metis_tac [ORD_CHR_RWT,alphabet_size_def]);


val Brzozowski_correct = Q.store_thm
("Brzozowski_correct",
`!r s.
  dom_Brz empty [normalize r] (1,singleton (normalize r) 0,[]) /\
  (!c. MEM c s ⇒ MEM (ORD c) ALPHABET)
  ==>
  (Brz_lang r s = regexp_lang (normalize r) s)`
 ,
 rw [GSYM regexp_lang_smart_deriv, Brz_lang_def]
  >> UNABBREV_ALL_TAC
  >> fs [compile_regexp_def]
  >> `?seen next_state state_map table.
        Brzozowski empty [normalize r] (1,singleton (normalize r) 0,[])
          = (seen,next_state,state_map,table)`
       by metis_tac [pair_CASES,SND]
  >> fs [LET_THM]
  >> rw []
  >> `Brz_invariant empty [normalize r] (1,singleton (normalize r) 0,[])`
      by (rw_tac set_ss [Brz_invariant_def,invar_def,dom_def, normalize_thm,
                      fmap_inj_def, good_table_def, singleton_thm,empty_def,
                      invariant_def,mem_regexp_def,member_iff_lookup]
           >- fs [lookup_def]
           >- (fs [fdom_def, singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw []
                >> metis_tac [eq_cmp_regexp_compare, eq_cmp_def,normalize_thm])
           >- (rw [union_def,set_def,GSYM empty_def, GSYM oempty_def] >>
               rw [EXTENSION,fdom_def, osingleton_def, singleton_def, lookup_def] >>
               CASE_TAC)
           >- (rw [range_def,frange_def, EXTENSION, singleton_def,lookup_def,EQ_IMP_THM]
                >- (BasicProvers.EVERY_CASE_TAC >> rw [])
                >- (Q.EXISTS_TAC `normalize r` >> rw [regexp_compare_id] >> decide_tac))
           >- (rw [GSYM empty_def, GSYM oempty_def]
               >> rw [fdom_def, lookup_def, empty_def, oempty_def])
           >- (ntac 2 (pop_assum mp_tac)
                >> simp_tac set_ss [fdom_def,singleton_def,lookup_def]
                >> BasicProvers.EVERY_CASE_TAC
                >> rw[]
                >> metis_tac [eq_cmp_def, eq_cmp_regexp_compare])
           >- fs [alistTheory.ALOOKUP_def]
           >- fs [alistTheory.ALOOKUP_def]
           >- fs [alistTheory.ALOOKUP_def])
 >> imp_res_tac Brz_inv_thm
 >> imp_res_tac Brz_mono
 >> imp_res_tac Brz_invariant_final
 >> fs [Brz_invariant_def]
 >> `smart_deriv_matches (normalize r) s
      <=>
     table_lang (get_accepts state_map) table (apply state_map (normalize r)) (MAP ORD s)`
     by (fs [invar_def,set_def,ounion_oempty,union_def]
          >> `fdom num_cmp (oimage num_cmp (apply state_map) seen) = frange regexp_compare state_map`
                    by (simp_tac set_ss [frange_def] >>
                        qpat_x_assum `dom _ = dom __` mp_tac >>
                        rw [fdom_oimage_inst,apply_def, oin_fdom,fapply_def, dom_def] >>
                        simp_tac set_ss [fdom_def] >> metis_tac[THE_DEF])
          >> mp_tac (table_lang_correct
                   |> INST_TYPE [alpha |-> ``:num``]
                   |> Q.SPEC `get_accepts state_map`
                   |> Q.SPEC `table:(num,(num,num)alist)alist`
                   |> Q.SPEC `state_map:(regexp,num)balanced_map`)
          >> fs[]
          >> `(∀n r. (lookup regexp_compare r state_map = SOME n) ⇒
                     (MEM n (get_accepts state_map) ⇔ nullable r))`
               by (rw [mem_get_accepts,EQ_IMP_THM]
                    >- (`r' IN fdom regexp_compare state_map` by rw [fdom_def]
                         >> metis_tac [fmap_inj_def, eq_cmp_regexp_compare, eq_cmp_def])
                    >- metis_tac[])
          >> rw []
          >> pop_assum mp_tac
          >> imp_res_tac string_to_numlist
          >> DISCH_THEN (assume_tac o Q.SPECL [`0n`, `normalize r`, `nl`])
          >> rfs[]
          >> rw[]
          >> `normalize r IN fdom regexp_compare (singleton (normalize r) 0)`
                by (rw [fdom_def, singleton_def,lookup_def,EQ_IMP_THM]
                     >> BasicProvers.EVERY_CASE_TAC
                     >> fs [regexp_compare_id])
          >> `normalize r IN fdom regexp_compare state_map /\
              (lookup regexp_compare (normalize r) (singleton (normalize r) 0) =
               lookup regexp_compare (normalize r) state_map)`
              by metis_tac [submap_def]
          >> fs [singleton_def,lookup_def,regexp_compare_id]
          >> qpat_x_assum `table_lang (get_accepts state_map) table 0 nl ⇔
                         smart_deriv_matches (normalize r) (MAP CHR nl)`
             (SUBST_ALL_TAC o SYM)
          >> rw [MAP_MAP_o,combinTheory.o_DEF,apply_def, fapply_def]
          >> pop_assum (SUBST_ALL_TAC o SYM)
          >> rw []
          >> `MAP (λx. ORD (CHR x)) nl = MAP (\x.x) nl`
              by (irule MAP_CONG >> rw [] >> metis_tac [mem_alphabet,ORD_CHR_lem])
         >> rw[])
 >> rw []
 >> imp_res_tac string_to_numlist
 >> rw [MAP_MAP_o,combinTheory.o_DEF,apply_def, fapply_def]
 >> `MAP (λx. ORD (CHR x)) nl = MAP (\x.x) nl`
              by (irule MAP_CONG >> rw [] >> metis_tac [mem_alphabet,ORD_CHR_lem])
 >> rw []
 >> match_mp_tac (GSYM (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] vec_lang_correct))
 >> rw []
    >- rw [sorted_get_accepts]
    >- metis_tac [mem_alphabet]
    >- (fs [good_table_def, alistTheory.alist_range_def]
         >> res_tac
         >> `n'' IN range state_map`
              by (simp_tac set_ss [range_def, frange_def] >> metis_tac[])
         >> `n'' IN count (LENGTH table)` by metis_tac [EXTENSION]
         >> metis_tac [IN_COUNT])
   >- metis_tac [mem_alphabet]
   >- (`normalize r IN fdom regexp_compare (singleton (normalize r) 0)`
          by (rw [fdom_def, singleton_def,lookup_def,EQ_IMP_THM]
               >> BasicProvers.EVERY_CASE_TAC
               >> fs [regexp_compare_id])
        >> `normalize r IN fdom regexp_compare state_map /\
            (lookup regexp_compare (normalize r) state_map =
             lookup regexp_compare (normalize r) (singleton (normalize r) 0))`
               by metis_tac [submap_def]
        >> rw [singleton_def,lookup_def,regexp_compare_id]
        >> `0n IN range state_map`
              by (simp_tac set_ss [range_def, frange_def]
                    >> Q.EXISTS_TAC `normalize r`
                    >> rw [singleton_def,lookup_def,EQ_IMP_THM]
                    >> CASE_TAC
                    >> fs [regexp_compare_id])
        >> `0n IN count (LENGTH table)` by metis_tac [EXTENSION]
        >> metis_tac [IN_COUNT])
);

val Brzozowski_correct_again = Q.store_thm
("Brzozowski_correct",
`!r s.
  dom_Brz empty [normalize r] (1,singleton (normalize r) 0,[]) /\
  (!c. MEM c s ⇒ MEM (ORD c) ALPHABET)
  ==>
  (regexp_matcher r s = regexp_lang r s)`
 ,
 rw []
  >> `Brz_lang r s = regexp_lang r s`
      by metis_tac [regexp_lang_normalize,Brzozowski_correct]
  >> pop_assum (SUBST_ALL_TAC o SYM)
  >> rw [Brz_lang_def, regexp_matcher_def, LET_THM,apply_def,fapply_def]);

val Brzozowski_partial_eval = Q.store_thm
("Brzozowski_partial_eval",
`!r state_numbering delta accepts deltaV acceptsV start_state.
  (compile_regexp r = (state_numbering,delta,accepts)) /\
  (deltaV = fromList (MAP fromList delta)) /\
  (acceptsV = fromList accepts) /\
  (lookup regexp_compare (normalize r) state_numbering = SOME start_state) /\
  dom_Brz empty [normalize r] (1,singleton (normalize r) 0,[])
  ==> !s. EVERY (\c. MEM (ORD c) ALPHABET) s
          ==>
         (exec_dfa acceptsV deltaV start_state s = regexp_lang r s)`
 ,
 rw [EVERY_MEM]
  >> `regexp_matcher r s = regexp_lang r s`
      by metis_tac [Brzozowski_correct_again]
  >> pop_assum (SUBST_ALL_TAC o SYM)
  >> rw [regexp_matcher_def, LET_THM]);

val all_ord_string = Q.prove
(`EVERY (\c. MEM (ORD c) ALPHABET) s
   <=>
  EVERY (\c. ORD c < alphabet_size) s`,
 simp_tac list_ss [mem_alphabet_iff]);

val Brzozowski_partial_eval_conseq = Q.store_thm
("Brzozowski_partial_eval_conseq",
 `!r state_numbering delta accepts deltaV acceptsV start_state.
  (compile_regexp r = (state_numbering,delta,accepts)) /\
  (deltaV = fromList (MAP fromList delta)) /\
  (acceptsV = fromList accepts) /\
  (lookup regexp_compare (normalize r) state_numbering = SOME start_state) /\
  dom_Brz_alt empty [normalize r]
  ==>
  !s. EVERY (λc. ORD c < alphabet_size) s
      ==>
      (exec_dfa acceptsV deltaV start_state s = regexp_lang r s)`
 ,
 metis_tac[Brzozowski_partial_eval,all_ord_string,dom_Brz_alt_equal,all_ord_string]);


(*---------------------------------------------------------------------------*)
(* Eliminate check that all chars in string are in alphabet. This can be     *)
(* be done when alphabet = [0..255]                                          *)
(*---------------------------------------------------------------------------*)

val Brzozowski_partial_eval_256 = save_thm
("Brzozowski_partial_eval_256",
  if Regexp_Type.alphabet_size = 256 then
   SIMP_RULE list_ss [ORD_BOUND,alphabet_size_def] Brzozowski_partial_eval_conseq
  else TRUTH);


(* val _ = EmitTeX.tex_theory"-"; *)

val _ = export_theory();
