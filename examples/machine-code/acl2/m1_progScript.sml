
open HolKernel boolLib bossLib Parse;
open pred_setTheory set_sepTheory progTheory listTheory pairTheory 
open combinTheory addressTheory sexpTheory imported_acl2Theory;
open complex_rationalTheory hol_defaxiomsTheory arithmeticTheory;

val _ = new_theory "m1_prog";


infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;



(* ----------------------------------------------------------------------------- *)
(* The M1_ set                                                                   *)
(* ----------------------------------------------------------------------------- *)

val _ = Hol_datatype `
  m1_el =   tPC    of sexp
          | tLocal of num => sexp
          | tStack of sexp
          | tInstr of sexp => sexp
          | tOK    of bool`;

val m1_el_11 = DB.fetch "-" "m1_el_11";
val m1_el_distinct = DB.fetch "-" "m1_el_distinct";

val _ = Parse.type_abbrev("m1_set",``:m1_el set``);


(* ----------------------------------------------------------------------------- *)
(* Converting from m1_state to m1_set                                          *)
(* ----------------------------------------------------------------------------- *)

val instr_def = Define `instr a s = nth a (program s)`;
val nth_local_def = Define `nth_local a s = nth (nat a) (locals s)`;
val m1_ok_def = Define `m1_ok s = ?x1 x2 x3 x4. s = make_state x1 x2 x3 x4`;

val m1_2set'_def = Define `
  m1_2set' (ps:unit set, ls: num set, ss: unit set, is: sexp set, os: unit set) (s:sexp) =
    IMAGE (\a. tPC (pc s)) ps UNION
    IMAGE (\a. tLocal a (nth_local a s)) ls UNION
    IMAGE (\a. tStack (stack s)) ss UNION
    IMAGE (\a. tInstr a (instr a s)) is UNION
    IMAGE (\a. tOK (m1_ok s)) os`;

val m1_2set_def   = Define `m1_2set s = m1_2set' (UNIV,UNIV,UNIV,UNIV,UNIV) s`;
val m1_2set''_def = Define `m1_2set'' x s = m1_2set s DIFF m1_2set' x s`;

(* theorems *)

val m1_2set'_SUBSET_m1_2set = prove(
  ``!y s. m1_2set' y s SUBSET m1_2set s``,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ SIMP_TAC std_ss [SUBSET_DEF,m1_2set'_def,m1_2set_def,IN_IMAGE,IN_UNION,IN_UNIV]
  \\ METIS_TAC [NOT_IN_EMPTY]);

val SPLIT_m1_2set = prove(
  ``!x s. SPLIT (m1_2set s) (m1_2set' x s, m1_2set'' x s)``,
  REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPLIT_def,EXTENSION,IN_UNION,IN_DIFF,m1_2set''_def]
  \\ `m1_2set' x s SUBSET m1_2set s` by METIS_TAC [m1_2set'_SUBSET_m1_2set]
  \\ SIMP_TAC bool_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,IN_DIFF]
  \\ METIS_TAC [SUBSET_DEF]);

val SUBSET_m1_2set = prove(
  ``!u s. u SUBSET m1_2set s = ?y. u = m1_2set' y s``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_REWRITE_TAC [m1_2set'_SUBSET_m1_2set]
  \\ Q.EXISTS_TAC `(
       { a |a| ?x. tPC x IN u },
       { a |a| ?x. tLocal a x IN u },
       { a |a| ?x. tStack x IN u },
       { a |a| ?x. tInstr a x IN u },
       { a |a| ?x. tOK x IN u })`
  \\ FULL_SIMP_TAC std_ss [m1_2set'_def,m1_2set_def,EXTENSION,SUBSET_DEF,IN_IMAGE,
       IN_UNION,GSPECIFICATION,IN_INSERT,NOT_IN_EMPTY,IN_UNIV]
  \\ STRIP_TAC \\ ASM_REWRITE_TAC [] \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ PAT_ASSUM ``!x:'a. b:bool`` IMP_RES_TAC \\ FULL_SIMP_TAC std_ss [m1_el_11,m1_el_distinct]);

val SPLIT_m1_2set_EXISTS = prove(
  ``!s u v. SPLIT (m1_2set s) (u,v) = ?y. (u = m1_2set' y s) /\ (v = m1_2set'' y s)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [SPLIT_m1_2set]
  \\ FULL_SIMP_TAC bool_ss [SPLIT_def,m1_2set'_def,m1_2set''_def]
  \\ `u SUBSET (m1_2set s)` by
       (FULL_SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [SUBSET_m1_2set] \\ Q.EXISTS_TAC `y` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_UNION,DISJOINT_DEF,NOT_IN_EMPTY,IN_INTER]
  \\ METIS_TAC []);



val IN_m1_2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a x s. tPC x IN (m1_2set s) = (x = pc s)) /\
  (!a x s. tPC x IN (m1_2set' (ps,ls,ss,is,os) s) = (x = pc s) /\ a IN ps) /\
  (!a x s. tPC x IN (m1_2set'' (ps,ls,ss,is,os) s) = (x = pc s) /\ ~(a IN ps)) /\ 
  (!a x s. tLocal a x IN (m1_2set s) = (x = nth_local a s)) /\
  (!a x s. tLocal a x IN (m1_2set' (ps,ls,ss,is,os) s) = (x = nth_local a s) /\ a IN ls) /\
  (!a x s. tLocal a x IN (m1_2set'' (ps,ls,ss,is,os) s) = (x = nth_local a s) /\ ~(a IN ls)) /\ 
  (!a x s. tStack x IN (m1_2set s) = (x = stack s)) /\
  (!a x s. tStack x IN (m1_2set' (ps,ls,ss,is,os) s) = (x = stack s) /\ a IN ss) /\
  (!a x s. tStack x IN (m1_2set'' (ps,ls,ss,is,os) s) = (x = stack s) /\ ~(a IN ss)) /\ 
  (!a x s. tInstr a x IN (m1_2set s) = (x = instr a s)) /\
  (!a x s. tInstr a x IN (m1_2set' (ps,ls,ss,is,os) s) = (x = instr a s) /\ a IN is) /\
  (!a x s. tInstr a x IN (m1_2set'' (ps,ls,ss,is,os) s) = (x = instr a s) /\ ~(a IN is)) /\ 
  (!a x s. tOK x IN (m1_2set s) = (x = m1_ok s)) /\
  (!a x s. tOK x IN (m1_2set' (ps,ls,ss,is,os) s) = (x = m1_ok s) /\ a IN os) /\
  (!a x s. tOK x IN (m1_2set'' (ps,ls,ss,is,os) s) = (x = m1_ok s) /\ ~(a IN os))``,
  SRW_TAC [] [m1_2set'_def,m1_2set''_def,m1_2set_def,IN_UNION,IN_DIFF,oneTheory.one] 
  \\ METIS_TAC []);

val SET_NOT_EQ = prove(
  ``!x y. ~(x = y:'a set) = ?a. ~(a IN x = a IN y)``,
   FULL_SIMP_TAC std_ss [EXTENSION])

val m1_2set''_11 = prove(
  ``!y y' s s'. (m1_2set'' y' s' = m1_2set'' y s) ==> (y = y')``,
  REPEAT STRIP_TAC
  \\ `?ps ls ss is os. y = (ps,ls,ss,is,os)` by METIS_TAC [PAIR]
  \\ `?ps2 ls2 ss2 is2 os2. y' = (ps2,ls2,ss2,is2,os2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ CCONTR_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (`~((?y. tPC y IN m1_2set'' (ps,ls,ss,is,os) s) = 
            (?y. tPC y IN m1_2set'' (ps2,ls2,ss2,is2,os2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tLocal x y IN m1_2set'' (ps,ls,ss,is,os) s) = 
            (?y. tLocal x y IN m1_2set'' (ps2,ls2,ss2,is2,os2) s'))` by 
         FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tStack y IN m1_2set'' (ps,ls,ss,is,os) s) = 
            (?y. tStack y IN m1_2set'' (ps2,ls2,ss2,is2,os2) s'))` by
         FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tInstr x y IN m1_2set'' (ps,ls,ss,is,os) s) = 
            (?y. tInstr x y IN m1_2set'' (ps2,ls2,ss2,is2,os2) s'))` by
         FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] THEN1 METIS_TAC [])
  THEN1 (`~((?y. tOK y IN m1_2set'' (ps,ls,ss,is,os) s) = 
            (?y. tOK y IN m1_2set'' (ps2,ls2,ss2,is2,os2) s'))` by
         FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] THEN1 METIS_TAC []));

val DELETE_m1_2set = (SIMP_RULE std_ss [oneTheory.one] o prove)(``
  (!a s. (m1_2set' (ps,ls,ss,is,os) s) DELETE tPC (pc s) =
         (m1_2set' (ps DELETE a,ls,ss,is,os) s)) /\ 
  (!a s. (m1_2set' (ps,ls,ss,is,os) s) DELETE tLocal a (nth_local a s) =
         (m1_2set' (ps,ls DELETE a,ss,is,os) s)) /\ 
  (!a s. (m1_2set' (ps,ls,ss,is,os) s) DELETE tStack (stack s) =
         (m1_2set' (ps,ls,ss DELETE a,is,os) s)) /\ 
  (!a s. (m1_2set' (ps,ls,ss,is,os) s) DELETE tInstr a (instr a s) =
         (m1_2set' (ps,ls,ss,is DELETE a,os) s)) /\
  (!a s. (m1_2set' (ps,ls,ss,is,os) s) DELETE tOK (m1_ok s) =
         (m1_2set' (ps,ls,ss,is,os DELETE a) s))``, 
  SRW_TAC [] [m1_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,
    EXISTS_OR_THM,IN_DELETE,IN_INSERT,NOT_IN_EMPTY,oneTheory.one]
  \\ Cases_on `x` \\ SRW_TAC [] [] \\ METIS_TAC []);

val EMPTY_m1_2set = prove(``
  (m1_2set' (ps,ls,ss,is,os) s = {}) = 
  (ps = {}) /\ (ls = {}) /\ (ss = {}) /\ (is = {}) /\ (os = {})``,
  SRW_TAC [] [m1_2set'_def,EXTENSION,IN_UNION,GSPECIFICATION,LEFT_AND_OVER_OR,EXISTS_OR_THM]
  \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Defining the M1_MODEL                                                        *)
(* ----------------------------------------------------------------------------- *)

val tP_def = Define `tP x = SEP_EQ {tPC x}`;
val tS_def = Define `tS x = SEP_EQ {tStack x}`;
val tL_def = Define `tL a x = SEP_EQ {tLocal a x}`;
val tO_def = Define `tO x = SEP_EQ {tOK x}`;
val tI_def = Define `tI a x = SEP_EQ {tInstr a x}`;

val PC_def = Define `PC x = tP x * tO T`;

val M1_INSTR_def = Define `M1_INSTR (a,w) = { tInstr a w }`;
val M1_NEXT_def = Define `M1_NEXT s1 s2 = (step s1 = s2)`;

val M1_MODEL_def = Define `
  M1_MODEL = (m1_2set, M1_NEXT, M1_INSTR, (\x y. (x:sexp) = y))`;


(* theorems *)

val lemma =
  METIS_PROVE [SPLIT_m1_2set]
  ``p (m1_2set' y s) ==> (?u v. SPLIT (m1_2set s) (u,v) /\ p u /\ (\v. v = m1_2set'' y s) v)``;

val M1_SPEC_SEMANTICS = prove(
  ``SPEC M1_MODEL p {} q =
    !y s seq. p (m1_2set' y s) /\ rel_sequence M1_NEXT seq s ==>
              ?k. q (m1_2set' y (seq k)) /\ (m1_2set'' y s = m1_2set'' y (seq k))``,
  SIMP_TAC bool_ss [GSYM RUN_EQ_SPEC,RUN_def,M1_MODEL_def,STAR_def,SEP_REFINE_def]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC bool_ss [SPLIT_m1_2set_EXISTS] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `!s r. b` (STRIP_ASSUME_TAC o UNDISCH o SPEC_ALL o
     (fn th => MATCH_MP th (UNDISCH lemma))  o Q.SPECL [`s`,`(\v. v = m1_2set'' y s)`])
  \\ FULL_SIMP_TAC bool_ss [SPLIT_m1_2set_EXISTS]
  \\ IMP_RES_TAC m1_2set''_11 \\ Q.EXISTS_TAC `i` \\ METIS_TAC []);


(* ----------------------------------------------------------------------------- *)
(* Theorems for construction of |- SPEC M1_MODEL ...                            *)
(* ----------------------------------------------------------------------------- *)

val SEP_EQ_STAR_LEMMA = prove(
  ``!p s t. (SEP_EQ t * p) s <=> t SUBSET s /\ (t SUBSET s ==> p (s DIFF t))``,  
  METIS_TAC [EQ_STAR]);

val FLIP_CONJ = prove(``!b c. b /\ (b ==> c) = b /\ c``,METIS_TAC []);

val EXPAND_STAR =  
  GEN_ALL o (SIMP_CONV std_ss [tP_def, tS_def, tL_def, tO_def, tI_def,
    SEP_EQ_STAR_LEMMA,INSERT_SUBSET,IN_m1_2set,DELETE_m1_2set,
    DIFF_INSERT,DIFF_EMPTY,EMPTY_SUBSET] THENC SIMP_CONV std_ss [FLIP_CONJ]
   THENC REWRITE_CONV [GSYM CONJ_ASSOC])

val STAR_m1_2set = LIST_CONJ (map EXPAND_STAR 
  [``(tP x * p) (m1_2set' (ps,ls,ss,is,os) s)``,
   ``(tL a x * p) (m1_2set' (ps,ls,ss,is,os) s)``,
   ``(tS x * p) (m1_2set' (ps,ls,ss,is,os) s)``,
   ``(tI a x * p) (m1_2set' (ps,ls,ss,is,os) s)``,
   ``(tO x * p) (m1_2set' (ps,ls,ss,is,os) s)``]);

val CODE_POOL_m1_2set_LEMMA = prove(
  ``!x y z. (x = z INSERT y) = (z INSERT y) SUBSET x /\ (x DIFF (z INSERT y) = {})``,
  SIMP_TAC std_ss [EXTENSION,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY,IN_DIFF] \\ METIS_TAC []);

val CODE_POOL_m1_2set = prove(
  ``CODE_POOL M1_INSTR {(p,c)} (m1_2set' (ps,ls,ss,is,os) s) =
      ({p} = is) /\ (ls = {}) /\ (ss = {}) /\ (ps = {}) /\ (os = {}) /\
      (instr p s = c)``,
  SIMP_TAC bool_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,BIGUNION_INSERT,
    BIGUNION_EMPTY,UNION_EMPTY,M1_INSTR_def,CODE_POOL_m1_2set_LEMMA,
    GSYM DELETE_DEF, INSERT_SUBSET, EMPTY_SUBSET,IN_m1_2set]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [DELETE_m1_2set,EMPTY_m1_2set,DIFF_INSERT]
  \\ ASM_SIMP_TAC std_ss [GSYM AND_IMP_INTRO,DELETE_m1_2set,EMPTY_m1_2set,DIFF_EMPTY]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ ASM_SIMP_TAC std_ss [DELETE_m1_2set,EMPTY_m1_2set]);

val M1_SPEC_CODE = (RW [GSYM M1_MODEL_def] o SIMP_RULE std_ss [M1_MODEL_def] o prove)
  (``SPEC M1_MODEL (CODE_POOL (FST (SND (SND M1_MODEL))) c * p) {}
                    (CODE_POOL (FST (SND (SND M1_MODEL))) c * q) =
    SPEC M1_MODEL p c q``,
  REWRITE_TAC [SPEC_CODE]);

val IMP_M1_SPEC_LEMMA = prove(
  ``!p q.
      (!s s2 y.
        p (m1_2set' y s) ==>
        (?s1. M1_NEXT s s1) /\
        (M1_NEXT s s2 ==> q (m1_2set' y s2) /\ (m1_2set'' y s = m1_2set'' y s2))) ==>
      SPEC M1_MODEL p {} q``,
  REWRITE_TAC [M1_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC bool_ss [rel_sequence_def]
  \\ Q.EXISTS_TAC `SUC 0` \\ METIS_TAC []);

val IMP_M1_SPEC = 
  (RW1 [STAR_COMM] o RW [M1_SPEC_CODE] o
   SPECL [``CODE_POOL M1_INSTR {(p,c)} * p1``,
          ``CODE_POOL M1_INSTR {(p,c)} * q1``]) IMP_M1_SPEC_LEMMA;

val m1_2set''_thm = prove(
  ``(m1_2set'' (ps,ls,ss,is,os) s1 = m1_2set'' (ps,ls,ss,is,os) s2) =
    (!a. ~(a IN ps) ==> (pc s1 = pc s2)) /\
    (!a. ~(a IN ls) ==> (nth_local a s1 = nth_local a s2)) /\
    (!a. ~(a IN ss) ==> (stack s1 = stack s2)) /\
    (!a. ~(a IN is) ==> (instr a s1 = instr a s2)) /\
    (!a. ~(a IN os) ==> (m1_ok s1 = m1_ok s2))``,
  SIMP_TAC std_ss [oneTheory.one]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [EXTENSION]
  THEN1 (Cases \\ ASM_SIMP_TAC std_ss [IN_m1_2set] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tPC (pc s1)`)
         \\ METIS_TAC [IN_m1_2set])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tLocal a (nth_local a s1)`)
         \\ METIS_TAC [IN_m1_2set])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tStack (stack s1)`)
         \\ METIS_TAC [IN_m1_2set])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tInstr a (instr a s1)`)
         \\ FULL_SIMP_TAC std_ss [IN_m1_2set,oneTheory.one] \\ METIS_TAC [])
  THEN1 (Q.PAT_ASSUM `!x.bb` (ASSUME_TAC o Q.SPEC `tOK (m1_ok s1)`)
         \\ METIS_TAC [IN_m1_2set]));


(* ----------------------------------------------------------------------------- *)
(* Proving a SPEC theorem for each M1 instruction                                *)
(* ----------------------------------------------------------------------------- *)

val acl2_simp =
  SIMP_RULE std_ss [itel_def] o
  SIMP_RULE list_ss
    ([let_simp,andl_fold,itel_fold,itel_append,forall2_thm,exists2_thm,forall_fold,
      exists_fold,implies,andl_simp,not_simp,t_nil] @
     (map GSYM [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]));

val defs = map acl2_simp [actual_defun, app_defun, arg1_defun,
   arg2_defun, arg3_defun, bind_defun, binding_defun, boundp_defun,
   collect_at_end_defun, collect_vars_in_expr_defun, compile_defun,
   concat_symbols_defun, do_inst_defun, even_sched_defun,
   exclaim_defun, execute_goto_defun, execute_iadd_defun,
   execute_iconst_defun, execute_ifle_defun, execute_iload_defun,
   execute_imul_defun, execute_istore_defun, execute_isub_defun,
   expr_exclaim_defun, frev_defun, goto_exclaim_defun,
   iconst_exclaim_defun, ifact_defun, ifact_loop_sched_defun,
   ifact_sched_defun, ifle_exclaim_defun, iload_exclaim_defun,
   index_defun, istore_exclaim_defun, locals_defun, m1_len_defun,
   m1_member_defun, make_defun_defun, make_state_defun,
   next_inst_defun, nextn_defun, nth_defun, op_code_defun,
   op_exclaim_defun, pattern_bindings_defun, pc_defun, pop_defun,
   popn_defun, program_defun, push_defun, repeat_defun, rev1_defun,
   rev_defun, run_defun, s_big_defun, s_fix_defun, skipn_defun,
   stack_defun, step_defun, suppliedp_defun, test_even_defun,
   test_exclaim_defun, test_ifact_defun, top_defun, u_big1_defun,
   u_big_defun, u_fix_defun, update_nth_defun, while_exclaim_defun];

val defs2 = map acl2_simp [actual_defun, app_defun, arg1_defun,
   arg2_defun, arg3_defun, bind_defun, binding_defun, boundp_defun,
   collect_at_end_defun, collect_vars_in_expr_defun, compile_defun,
   concat_symbols_defun, do_inst_defun, even_sched_defun,
   exclaim_defun, execute_goto_defun, execute_iadd_defun,
   execute_iconst_defun, execute_ifle_defun, execute_iload_defun,
   execute_imul_defun, execute_istore_defun, execute_isub_defun,
   expr_exclaim_defun, frev_defun, goto_exclaim_defun,
   iconst_exclaim_defun, ifact_defun, ifact_loop_sched_defun,
   ifact_sched_defun, ifle_exclaim_defun, iload_exclaim_defun,
   index_defun, istore_exclaim_defun, m1_len_defun, m1_member_defun,
   make_defun_defun, next_inst_defun, nextn_defun, op_code_defun,
   op_exclaim_defun, pattern_bindings_defun, pop_defun, popn_defun,
   push_defun, repeat_defun, rev1_defun, rev_defun, run_defun,
   s_big_defun, s_fix_defun, skipn_defun, step_defun, suppliedp_defun,
   test_even_defun, test_exclaim_defun, test_ifact_defun, top_defun,
   u_big1_defun, u_big_defun, u_fix_defun, while_exclaim_defun];


val CODE_POOL_THM = prove(
  ``!p x. CODE_POOL M1_INSTR {(p,x)} = tI p x``,
  SIMP_TAC std_ss [CODE_POOL_def,IMAGE_INSERT,IMAGE_EMPTY,SEP_EQ_def,
    BIGUNION_INSERT,BIGUNION_EMPTY,UNION_EMPTY,M1_INSTR_def,tI_def]);  

val UNIT_IN_SET = prove(
  ``!x. () IN x = (x = {()})``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC [oneTheory.one]);

val ite_intro = store_thm("ite_intro",
  ``!p x y. (if |= p then x else y) = ite p x y``,
  ASM_SIMP_TAC std_ss [hol_defaxiomsTheory.ACL2_SIMPS] THEN METIS_TAC []);

val add_COMM = store_thm("add_COMM",
  ``!x y. add x y = add y x``,
  Cases \\ Cases \\ SIMP_TAC std_ss [add_def] \\ Cases_on `c` \\ Cases_on `c'`
  \\ SIMP_TAC std_ss [complex_rationalTheory.COMPLEX_ADD_def]
  \\ METIS_TAC [ratTheory.RAT_ADD_COMM]);

val add_ASSOC = store_thm("add_ASSOC",
  ``!x y z. add (add x y) z = add x (add y z)``,
  Cases \\ Cases \\ Cases \\ SIMP_TAC std_ss [add_def,int_def,cpx_def] 
  \\ Q.SPEC_TAC (`c`,`c`) \\ Q.SPEC_TAC (`c'`,`c2`)
  \\ SIMP_TAC std_ss [] \\ REPEAT Cases
  \\ Q.SPEC_TAC (`r`,`m`) \\ Q.SPEC_TAC (`r0`,`n`) \\ Q.SPEC_TAC (`c''`,`d`)
  \\ SIMP_TAC std_ss [complex_rationalTheory.COMPLEX_ADD_def,rat_def] 
  \\ REPEAT Cases \\ SIMP_TAC std_ss [GSYM (EVAL ``0:rat``),ratTheory.RAT_ADD_LID,
       RW1[ratTheory.RAT_ADD_COMM]ratTheory.RAT_ADD_LID,
       complex_rationalTheory.COMPLEX_ADD_def,ratTheory.RAT_ADD_ASSOC]);

val add_nat = store_thm("add_nat",
  ``!m n. add (nat m) (nat n) = nat (m + n)``,
  SIMP_TAC (srw_ss()) [add_def,int_def,nat_def,cpx_def, 
    complex_rationalTheory.COMPLEX_ADD_def,rat_def,
    ratTheory.RAT_ADD_CALCULATE,fracTheory.FRAC_ADD_CALCULATE]
  \\ `!m n. &(m + n) = &m + (&(n:num)):int` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC std_ss []);

val less_nat = store_thm("less_nat",
  ``!m n. (|= (less (nat m) (nat n))) = m < n``,
  SIMP_TAC (srw_ss()) [less_def,int_def,nat_def,cpx_def, 
    complex_rationalTheory.COMPLEX_LT_def,rat_def,
    ratTheory.RAT_LES_CALCULATE,fracTheory.NMR,fracTheory.DNM]
  \\ SRW_TAC [] [] \\ EVAL_TAC);

val sexp_not = store_thm("sexp_not",
  ``!s. (|= not s) = ~(|= s)``,
  REPEAT STRIP_TAC \\ Cases_on `s = nil` \\ POP_ASSUM MP_TAC
  \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC);

val mult_nat = store_thm("mult_nat",
  ``!m n. mult (nat m) (nat n) = nat (m * n)``,
  SIMP_TAC (srw_ss()) [mult_def,int_def,nat_def,cpx_def, 
    complex_rationalTheory.COMPLEX_MULT_def,rat_def,
    ratTheory.RAT_MUL_CALCULATE,fracTheory.FRAC_MULT_CALCULATE, 
    complex_rationalTheory.COMPLEX_ADD_def,rat_def,
    ratTheory.RAT_ADD_CALCULATE,fracTheory.FRAC_ADD_CALCULATE,
    ratTheory.RAT_SUB_CALCULATE,fracTheory.FRAC_SUB_CALCULATE]);

val add_nat_int = store_thm("add_nat_int",
  ``!m n. n <= m ==> (add (nat m) (int (-&n)) = nat (m - n))``,
  SIMP_TAC (srw_ss()) [add_def,int_def,nat_def,cpx_def, 
    complex_rationalTheory.COMPLEX_ADD_def,rat_def,
    ratTheory.RAT_ADD_CALCULATE,fracTheory.FRAC_ADD_CALCULATE,
    integerTheory.INT_SUB,GSYM integerTheory.int_sub]);

val unary_minus_int = store_thm("unary_minus_int",
  ``!i. unary_minus (int i) = int (-i)``,
  SIMP_TAC (srw_ss()) [unary_minus_def,int_def,nat_def,cpx_def, 
    complex_rationalTheory.COMPLEX_SUB_def,rat_def,
    complex_rationalTheory.com_0_def,ratTheory.rat_0_def,fracTheory.frac_0_def,
    ratTheory.RAT_SUB_CALCULATE,fracTheory.FRAC_SUB_CALCULATE,
    integerTheory.INT_SUB,GSYM integerTheory.int_sub]);

val rat_lemma = prove(
  ``!x. ?y. (rep_rat (abs_rat x) = y) /\ rat_equiv x y``,
  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [RW[quotientTheory.QUOTIENT_def]ratTheory.rat_def]
  \\ SIMP_TAC std_ss [ratTheory.rat_equiv_def,ratTheory.RAT]);

val DIVIDES_lemma = prove(
  ``!n m. 0 < n ==> DIVIDES n (m * n)``,
  EVAL_TAC \\ SIMP_TAC std_ss [GSYM integerTheory.INT_ABS_MUL] \\ REPEAT STRIP_TAC
  \\ `?nn mm. (ABS n = &nn) /\ (ABS m = &mm)` by 
        METIS_TAC [integerTheory.INT_ABS_POS,integerTheory.NUM_POSINT_EXISTS]
  \\ ASM_SIMP_TAC std_ss [integerTheory.INT_MUL,integerTheory.NUM_OF_INT]
  \\ REPEAT STRIP_TAC \\ `0 < nn` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC std_ss [arithmeticTheory.MOD_EQ_0]);

val INTEGERP_INT = prove(
  ``integerp (int n) = t``,
  SIMP_TAC std_ss [int_def,integerp_def,cpx_def,IS_INT_def,
       EVAL ``rat 0 1 = rat_0``] 
  \\ SIMP_TAC std_ss [ratTheory.rat_dnm_def,ratTheory.rat_nmr_def,rat_def]
  \\ STRIP_ASSUME_TAC (Q.SPEC `abs_frac (n,1)` rat_lemma)  
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [ratTheory.rat_equiv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [fracTheory.NMR,fracTheory.DNM]  
  \\ POP_ASSUM (ASSUME_TAC o GSYM) 
  \\ Cases_on `DIVIDES (frac_dnm y) (n * frac_dnm y)`
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC \\ POP_ASSUM MP_TAC
  \\ METIS_TAC [fracTheory.FRAC_DNMPOS,DIVIDES_lemma]); 

val nth_lemma = store_thm("nth_lemma",
  ``(nth (nat 0) x = car x) /\
    (nth (nat (SUC n)) x = nth (nat n) (cdr x))``,
  SIMP_TAC std_ss [arithmeticTheory.ADD1] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [acl2_simp nth_defun]))
  \\ SIMP_TAC (srw_ss()) [ACL2_SIMPS,nat_def,INTEGERP_INT,less_def,
        cpx_def,EVAL ``int 0``,rat_def,ratTheory.RAT_LES_CALCULATE]
  \\ ONCE_REWRITE_TAC [add_COMM] \\ SIMP_TAC std_ss [GSYM nat_def]
  \\ SIMP_TAC std_ss [add_nat_int] \\ SIMP_TAC std_ss [nat_def]
  \\ SIMP_TAC (srw_ss()) [ACL2_SIMPS,nat_def,INTEGERP_INT,less_def,int_def,
        cpx_def,EVAL ``int 0``,rat_def,ratTheory.RAT_LES_CALCULATE,
        fracTheory.NMR,fracTheory.DNM,DECIDE ``0<n+1:num``]);

val update_nth_lemma = store_thm("update_nth_lemma",
  ``(update_nth (nat 0) v list = cons v (cdr list)) /\
    (update_nth (nat (SUC n)) v list = cons (car list) (update_nth (nat n) v (cdr list)))``,
  SIMP_TAC std_ss [arithmeticTheory.ADD1] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [acl2_simp update_nth_defun]))
  \\ SIMP_TAC (srw_ss()) [ACL2_SIMPS,nat_def,INTEGERP_INT,less_def,
        cpx_def,EVAL ``int 0``,rat_def,ratTheory.RAT_LES_CALCULATE]
  \\ ONCE_REWRITE_TAC [add_COMM] \\ SIMP_TAC std_ss [GSYM nat_def]
  \\ SIMP_TAC std_ss [add_nat_int] \\ SIMP_TAC std_ss [nat_def]
  \\ SIMP_TAC (srw_ss()) [ACL2_SIMPS,nat_def,INTEGERP_INT,less_def,int_def,
        cpx_def,EVAL ``int 0``,rat_def,ratTheory.RAT_LES_CALCULATE,
        fracTheory.NMR,fracTheory.DNM,DECIDE ``0<n+1:num``]);

val nth_thm = prove(
  ``(nth (nat 0) (cons x0 x1) = x0) /\
    (nth (nat 1) (cons x0 (cons x1 x2)) = x1) /\
    (nth (nat 2) (cons x0 (cons x1 (cons x2 x3))) = x2) /\
    (nth (nat 3) (cons x0 (cons x1 (cons x2 (cons x3 x4)))) = x3)``,
  SIMP_TAC bool_ss [nth_lemma,car_def,cdr_def,
    DECIDE ``(1 = SUC 0) /\ (2 = SUC 1) /\ (3 = SUC 2) /\ (4 = SUC 3)``]);

val nth_1 = save_thm("nth_1",
  SIMP_CONV bool_ss [GSYM (EVAL ``SUC 0``),nth_lemma] ``nth (nat 1) x``);

val update_nth_1 = save_thm("update_nth_1",
  SIMP_CONV bool_ss [GSYM (EVAL ``SUC 0``),update_nth_lemma] ``update_nth (nat 1) v list``);

val not_eq_nil = store_thm("not_eq_nil",
  ``!x. (not x = nil) = (|= x)``,
  REPEAT STRIP_TAC \\ Cases_on `x = nil` \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val sexp_reduce_SUC = store_thm("sexp_reduce_SUC",
  ``!n. add (nat (SUC n)) (unary_minus (nat 1)) = nat n``,
  SIMP_TAC std_ss [ADD1,GSYM add_nat,add_ASSOC]
  \\ `add (nat 1) (unary_minus (nat 1)) = nat 0` by ALL_TAC 
  \\ ASM_SIMP_TAC std_ss [add_nat] \\ SIMP_TAC std_ss [nat_def,unary_minus_int]
  \\ SIMP_TAC std_ss [GSYM nat_def,add_nat_int]);

val make_state_thm = prove(
  ``(pc (make_state x y z p) = x) /\
    (locals (make_state x y z p) = y) /\
    (stack (make_state x y z p) = z) /\
    (program (make_state x y z p) = p)``,
  ONCE_REWRITE_TAC defs \\ SIMP_TAC std_ss [make_state_defun,nth_thm]);

val instr_step = prove(
  ``!a s. instr a (step s) = instr a s``,
  NTAC 2 (ONCE_REWRITE_TAC defs) \\ SIMP_TAC std_ss [ite_def]
  \\ SRW_TAC [] [] \\ ONCE_REWRITE_TAC defs
  \\ SIMP_TAC std_ss [instr_def,make_state_thm]);

val m1_ok_step = prove(
  ``!s. m1_ok s ==> m1_ok (step s)``,
  NTAC 2 (ONCE_REWRITE_TAC defs) \\ SIMP_TAC std_ss [ite_def]
  \\ SRW_TAC [] [] \\ ONCE_REWRITE_TAC defs
  \\ SIMP_TAC std_ss [m1_ok_def] \\ METIS_TAC []);  

val IMP_SPEC_M1_MODEL = prove(
  ``(!cs l1. (nth p1 cs = c) ==>
             (step (make_state p1 l1 s1 cs) = make_state p2 l1 s2 cs)) ==>
    SPEC M1_MODEL (tS s1 * PC p1)
         {(p1,c)} (tS s2 * PC p2)``,
  REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC IMP_M1_SPEC \\ SIMP_TAC std_ss [M1_NEXT_def]
  \\ SIMP_TAC std_ss [PC_def,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,STAR_m1_2set,CODE_POOL_m1_2set,
       UNIT_IN_SET,m1_2set''_thm,IN_INSERT,NOT_IN_EMPTY,oneTheory.one,instr_step]
  \\ STRIP_TAC \\ Cases_on `m1_ok s` \\ ASM_SIMP_TAC std_ss [m1_ok_step]
  \\ FULL_SIMP_TAC std_ss [m1_ok_def,make_state_thm,instr_def]
  \\ STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ Q.PAT_ASSUM `!cs.bb` (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [make_state_thm,nth_local_def]);

val IMP_SPEC_M1_MODEL_2 = prove(
  ``(!cs l1. (nth p1 cs = c) /\ (v = nth (nat n) l1)  ==>
             (step (make_state p1 l1 s1 cs) = make_state p2 l1 s2 cs)) ==>
    SPEC M1_MODEL (tS s1 * tL n v * PC p1)
         {(p1,c)} (tS s2 * tL n v * PC p2)``,
  REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC IMP_M1_SPEC \\ SIMP_TAC std_ss [M1_NEXT_def]
  \\ SIMP_TAC std_ss [PC_def,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,STAR_m1_2set,CODE_POOL_m1_2set,
       UNIT_IN_SET,m1_2set''_thm,IN_INSERT,NOT_IN_EMPTY,oneTheory.one,instr_step]
  \\ STRIP_TAC \\ Cases_on `m1_ok s` \\ ASM_SIMP_TAC std_ss [m1_ok_step]
  \\ FULL_SIMP_TAC std_ss [m1_ok_def,make_state_thm,instr_def,nth_local_def]
  \\ STRIP_TAC \\ STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ Q.PAT_ASSUM `!cs.bb` (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [make_state_thm,nth_local_def]);

val nth_update_nth = prove(
  ``!n w l. (nth (nat n) (update_nth (nat n) w l) = w)``,
  Induct \\ ASM_SIMP_TAC std_ss [nth_lemma,update_nth_lemma,car_def,cdr_def]);

val nth_update_nth_NEQ = prove(
  ``!n a w l. ~(n = a) ==> (nth (nat n) (update_nth (nat a) w l) = nth (nat n) l)``,
  Induct \\ ASM_SIMP_TAC std_ss [nth_lemma,update_nth_lemma,car_def,cdr_def]
  \\ Cases_on `a` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [nth_lemma,update_nth_lemma,car_def,cdr_def]);

val IMP_SPEC_M1_MODEL_3 = prove(
  ``(!cs l1. (nth p1 cs = c) /\ (v = nth (nat n) l1)  ==>
             (step (make_state p1 l1 s1 cs) = 
              make_state p2 (update_nth (nat n) w l1) s2 cs)) ==>
    SPEC M1_MODEL (tS s1 * tL n v * PC p1)
         {(p1,c)} (tS s2 * tL n w * PC p2)``,
  REPEAT STRIP_TAC  
  \\ MATCH_MP_TAC IMP_M1_SPEC \\ SIMP_TAC std_ss [M1_NEXT_def]
  \\ SIMP_TAC std_ss [PC_def,GSYM STAR_ASSOC]
  \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,STAR_m1_2set,CODE_POOL_m1_2set,
       UNIT_IN_SET,m1_2set''_thm,IN_INSERT,NOT_IN_EMPTY,oneTheory.one,instr_step]
  \\ STRIP_TAC \\ Cases_on `m1_ok s` \\ ASM_SIMP_TAC std_ss [m1_ok_step]
  \\ FULL_SIMP_TAC std_ss [m1_ok_def,make_state_thm,instr_def,nth_local_def]
  \\ STRIP_TAC \\ STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ Q.PAT_ASSUM `!cs.bb` (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [make_state_thm,nth_local_def,nth_update_nth]
  \\ REPEAT STRIP_TAC \\ Cases_on `a = n` 
  \\ FULL_SIMP_TAC std_ss [nth_update_nth_NEQ]);

val acl2_ss = std_ss ++ rewrites [hol_defaxiomsTheory.ACL2_SIMPS,
  make_state_thm,nth_thm,CONS_11,NOT_CONS_NIL,stringTheory.CHR_11]  

fun M1_TAC thm = 
  SIMP_TAC std_ss [SPEC_MOVE_COND,precond_def] \\ SIMP_TAC std_ss [ACL2_TRUE] 
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC thm \\ ONCE_REWRITE_TAC defs2
  \\ ASM_SIMP_TAC std_ss [make_state_thm,next_inst_defun]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (K ALL_TAC) \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC defs2 \\ SIMP_TAC acl2_ss [op_code_defun,List_def]  
  \\ ONCE_REWRITE_TAC defs2 \\ SIMP_TAC acl2_ss [op_code_defun,List_def]  
  \\ ONCE_REWRITE_TAC defs2 \\ SIMP_TAC acl2_ss [op_code_defun,List_def]  
  \\ ONCE_REWRITE_TAC defs2 \\ SIMP_TAC acl2_ss [op_code_defun,List_def]  
  \\ ONCE_REWRITE_TAC defs2 \\ SIMP_TAC acl2_ss [op_code_defun,List_def]
  \\ METIS_TAC [add_COMM]


val M1_ICONST = store_thm("M1_ICONST",
  ``SPEC M1_MODEL
       (tS s * PC p)
       {(p, List [sym "M1" "ICONST"; x])}
       (tS (push x s) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_IADD = store_thm("M1_IADD",
  ``SPEC M1_MODEL
       (tS s * PC p)
       {(p, List [sym "M1" "IADD"])}
       (tS (push (add (top (pop s)) (top s)) (pop (pop s))) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_ISUB = store_thm("M1_ISUB",
  ``SPEC M1_MODEL
       (tS s * PC p)
       {(p, List [sym "M1" "ISUB"])}
       (tS (push (add (top (pop s)) (unary_minus (top s))) (pop (pop s))) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_IMUL = store_thm("M1_IMUL",
  ``SPEC M1_MODEL
       (tS s * PC p)
       {(p, List [sym "M1" "IMUL"])}
       (tS (push (mult (top (pop s)) (top s)) (pop (pop s))) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_GOTO = store_thm("M1_GOTO",
  ``SPEC M1_MODEL
       (tS s * PC p)
       {(p, List [sym "M1" "GOTO"; x])}
       (tS s * PC (add p x))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_IFLE = store_thm("M1_IFLE",
  ``SPEC M1_MODEL
       (tS s * PC p * precond ((|= (not (less (nat 0) (top s))))))
       {(p, List [sym "M1" "IFLE"; x])}
       (tS (pop s) * PC (add p x))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_IFLE_NOP = store_thm("M1_IFLE_NOP",
  ``SPEC M1_MODEL
       (tS s * PC p * precond (~(|= (not (less (nat 0) (top s))))))
       {(p, List [sym "M1" "IFLE"; x])}
       (tS (pop s) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL);

val M1_ILOAD = store_thm("M1_ILOAD",
  ``SPEC M1_MODEL
       (tS s * tL n v * PC p)
       {(p, List [sym "M1" "ILOAD"; (nat n)])}
       (tS (push v s) * tL n v * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL_2);

val M1_ISTORE = store_thm("M1_ISTORE",
  ``SPEC M1_MODEL
       (tS s * tL n v * PC p)
       {(p, List [sym "M1" "ISTORE"; (nat n)])}
       (tS (pop s) * tL n (top s) * PC (add p (nat 1)))``,
  M1_TAC IMP_SPEC_M1_MODEL_3);

    
val _ = export_theory();
