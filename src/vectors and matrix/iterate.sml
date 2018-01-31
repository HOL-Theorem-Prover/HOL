
(* ========================================================================= *)
(* Generic iterated operations and special cases of sums over N and R.       *)
(*  It is translated from the corresponding code file of Harrision in Hol-Light.                
AUTHORS  : (Copyright) Liming Li, Yong Guan and Zhiping Shi
             Beijing Engineering Research Center of High Reliable      
             Emmbedded System, Capital Normal University, China   
DATE  : 2011.05.23                                                           *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Generic iteration of operation over set with finite support.              *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Neutral, monoidal, support,iterate.                                       *)
(* ------------------------------------------------------------------------- *)
val NEUTRAL_DEF = new_definition("NEUTRAL_DEF",
  `NEUTRAL op = @x. !y. (op x y = y) /\ (op y x = y)`);

val MONOIDAL_DEF = new_definition("MONOIDAL_DEF",
  ` MONOIDAL op = (!x y. op x y = op y x) /\
                   (!x y z. op x (op y z) = op (op x y) z) /\
                   (!x. op (NEUTRAL op) x = x)`);

val MONOIDAL_AC = prove
 (`!op. MONOIDAL op
        ==> (!a. op (NEUTRAL op) a = a) /\
            (!a. op a (NEUTRAL op) = a) /\
            (!a b. op a b = op b a) /\
            (!a b c. op (op a b) c = op a (op b c)) /\
            (!a b c. op a (op b c) = op b (op a c))`,
  REWRITE_TAC[MONOIDAL_DEF] THEN PROVE_TAC[]);

val SUPPORT_DEF = new_definition("SUPPORT_DEF",
  `SUPPORT op f s = {x | x IN s /\ ~(f x = NEUTRAL op)}`);

val ITERATE_DEF = new_definition("ITERATE_DEF",
  `ITERATE op s f =
        if FINITE(SUPPORT op f s)
        then ITSET (\x a. op (f x) a) (SUPPORT op f s) (NEUTRAL op)
        else NEUTRAL op`);

val IN_SUPPORT = prove
 (`!op f x s. x IN (SUPPORT op f s) = x IN s /\ ~(f x = NEUTRAL op)`,
  REWRITE_TAC[SUPPORT_DEF] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]);

val SUPPORT_SUPPORT = prove
 (`!op f s. SUPPORT op f (SUPPORT op f s) = SUPPORT op f s`,
  REWRITE_TAC[SUPPORT_DEF] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[EXTENSION, GSYM CONJ_ASSOC]);

val SUPPORT_EMPTY = prove
 (`!op f s. (!x. x IN s ==> (f(x) = NEUTRAL op)) = (SUPPORT op f s = {})`,
  REWRITE_TAC[IN_SUPPORT, EXTENSION, NOT_IN_EMPTY] THEN
  PROVE_TAC[]);

val SUPPORT_SUBSET = prove
 (`!op f s. (SUPPORT op f s) SUBSET s`,
  SIMP_TAC std_ss[SUBSET_DEF, IN_SUPPORT]);

val FINITE_SUPPORT = prove
 (`!op f s. FINITE s ==> FINITE(SUPPORT op f s)`,
  PROVE_TAC[SUPPORT_SUBSET, SUBSET_FINITE]);

val SUPPORT_CLAUSES = prove
 (`(!f. SUPPORT op f {} = {}) /\
   (!f x s. SUPPORT op f (x INSERT s) =
       if f(x) = NEUTRAL op then SUPPORT op f s
       else x INSERT (SUPPORT op f s)) /\
   (!f x s. SUPPORT op f (s DELETE x) = (SUPPORT op f s) DELETE x) /\
   (!f s t. SUPPORT op f (s UNION t) =
                    (SUPPORT op f s) UNION (SUPPORT op f t)) /\
   (!f s t. SUPPORT op f (s INTER t) =
                    (SUPPORT op f s) INTER (SUPPORT op f t)) /\
   (!f s t. SUPPORT op f (s DIFF t) =
                    (SUPPORT op f s) DIFF (SUPPORT op f t)) /\
   (!f g s.  SUPPORT op g (IMAGE f s) = IMAGE f (SUPPORT op (g o f) s))`,
  REWRITE_TAC[SUPPORT_DEF, EXTENSION, IN_INSERT, IN_DELETE, o_THM,    IN_IMAGE, NOT_IN_EMPTY, IN_UNION, IN_INTER, IN_DIFF, COND_RAND] THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN PROVE_TAC[]);

val SUPPORT_DELTA = prove
 (`!op s f a. SUPPORT op (\x. if x = a then f(x) else NEUTRAL op) s =
              if a IN s then SUPPORT op f {a} else {}`,
  REWRITE_TAC[EXTENSION, SUPPORT_DEF, IN_SING] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN BETA_TAC THEN
  PROVE_TAC[NOT_IN_EMPTY]);

val FINITE_SUPPORT_DELTA = prove
 (`!op f a. FINITE(SUPPORT op (\x. if x = a then f(x) else NEUTRAL op) s)`,
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN SIMP_TAC std_ss[FINITE_RULES, FINITE_SUPPORT]);

(* ------------------------------------------------------------------------- *)
(* Key lemmas about the generic notion.                                      *)
(* ------------------------------------------------------------------------- *)
val ITERATE_SUPPORT = prove
 (`!op f s. ITERATE op (SUPPORT op f s) f = ITERATE op s f`,
  SIMP_TAC std_ss[ITERATE_DEF, SUPPORT_SUPPORT]);

val ITERATE_EXPAND_CASES = prove
 (`!op f s. ITERATE op s f =
           if FINITE(SUPPORT op f s) then ITERATE op (SUPPORT op f s) f
              else NEUTRAL op`,
  SIMP_TAC std_ss[ITERATE_DEF, SUPPORT_SUPPORT]);

val ITERATE_CLAUSES_GEN = prove
 (`!op. MONOIDAL op
        ==> (!(f :'b -> 'a). ITERATE op {} f = NEUTRAL op) /\
            (!f x s. MONOIDAL op /\ FINITE(SUPPORT op (f :'b -> 'a) s)
                     ==> (ITERATE op (x INSERT s) f =
                                if x IN s then ITERATE op s f
                                else op (f x) (ITERATE op s f)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC std_ss[GSYM FORALL_AND_THM] THEN GEN_TAC THEN
  CONJ_TAC THENL[
    REWRITE_TAC[ITERATE_DEF, SUPPORT_CLAUSES, FINITE_RULES, ITSET_EMPTY],
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ITERATE_DEF, SUPPORT_CLAUSES, FINITE_RULES] THEN
    CASE_TAC THENL[
      CASE_TAC THEN ASM_SIMP_TAC std_ss[MONOIDAL_AC],
      ASM_REWRITE_TAC[FINITE_INSERT] THEN CASE_TAC THENL[
        `x INSERT SUPPORT op f s = SUPPORT op f s` by
           ASM_REWRITE_TAC [EXTENSION, INSERT_DEF, SUPPORT_DEF] THENL[
          CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
          ASM_REWRITE_TAC[]],
      `SUPPORT op f s = SUPPORT op f s DELETE x` by MATCH_MP_TAC EQ_SYM THENL[ 
        REWRITE_TAC[GSYM DELETE_NON_ELEMENT, SUPPORT_DEF] THEN
        CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
        ASM_REWRITE_TAC[DE_MORGAN_THM],
        POP_ASSUM (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))] THEN
        `op (f x) (ITSET (\x a. op (f x) a) (SUPPORT op f s DELETE x) (NEUTRAL op)) =
     		(\x a. op (f x) a) x (ITSET (\x a. op (f x) a) (SUPPORT op f s DELETE x) (NEUTRAL op))` by BETA_TAC THEN
		ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
        BETA_TAC THEN PROVE_TAC[MONOIDAL_AC]]]]);

val ITERATE_CLAUSES = prove
 (`!op. MONOIDAL op
        ==> (!f. ITERATE op {} f = NEUTRAL op) /\
            (!f x s. FINITE(s)
                     ==> (ITERATE op (x INSERT s) f =
                          if x IN s then ITERATE op s f
                          else op (f x) (ITERATE op s f)))`,
  SIMP_TAC std_ss[ITERATE_CLAUSES_GEN, FINITE_SUPPORT]);

val ITERATE_UNION = prove
 (`!op. MONOIDAL op
        ==> !f s t. FINITE s /\ FINITE t /\ DISJOINT s t
                    ==> (ITERATE op (s UNION t) f =
                         op (ITERATE op s f) (ITERATE op t f))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SIMP_TAC std_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM, UNION_COMM] THEN 
  ASM_SIMP_TAC std_ss[ITERATE_CLAUSES, IN_UNION, UNION_EMPTY, FINITE_UNION,
                      INSERT_UNION_EQ, DISJOINT_INSERT] THEN
  PROVE_TAC[MONOIDAL_AC]);

val FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f: 'a ->'b) A s. 
(!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                  FINITE A ==> FINITE {x | x IN s /\ f(x) IN A}`,
  GEN_TAC THEN CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN
  REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ (f:'a ->'b) x IN EMPTY} = EMPTY`
    SUBST1_TAC THEN REWRITE_TAC[FINITE_RULES] THEN
REWRITE_TAC[EXTENSION] THEN
CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[NOT_IN_EMPTY],
ALL_TAC] THEN
  X_GEN_TAC `t:'b->bool` THEN
  DISCH_TAC THEN X_GEN_TAC `y:'b` THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:'a ->'b) x IN (y INSERT t)} =
                if (?x. x IN s /\ (f x = y))
                then (@x. x IN s /\ (f x = y)) INSERT {x | x IN s /\ f x IN t}
                else {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [ALL_TAC, COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION, IN_INSERT] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV)THENL
   [ALL_TAC, PROVE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `z = @x. x IN s /\ ((f:'a ->'b) x = y)` THEN
  PROVE_TAC[]);

val EQ_IMP = TAUT `(a <=> b) ==> a ==> b`;

val FINITE_IMAGE_INJ_EQ = prove
 (`!(f: 'a ->'b) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss[IMAGE_FINITE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[AND_IMP_INTRO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]);

val ITERATE_IMAGE = prove
 (`!op. MONOIDAL op
       ==> !f:'a ->'b g:'b ->'c s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (ITERATE op (IMAGE f s) g = ITERATE op s (g o f))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!s. FINITE s /\
        (!x y: 'a. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (ITERATE op (IMAGE f s) (g: 'b ->'c) = ITERATE op s (g o f))`
  ASSUME_TAC THENL
   [REWRITE_TAC [GSYM AND_IMP_INTRO] THEN 
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    ASM_SIMP_TAC std_ss[ITERATE_CLAUSES, IMAGE_CLAUSES,IMAGE_FINITE] THEN
    REWRITE_TAC[IN_INSERT] THEN PROVE_TAC[IN_IMAGE],
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
    MATCH_MP_TAC (prove
(`(a <=> a') /\ (a' ==> (b = b')) ==>
 ((if a then b else c) = if a' then b' else c)`,PROVE_TAC[])) THEN
    REWRITE_TAC[SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ,
      FIRST_X_ASSUM MATCH_MP_TAC] THEN PROVE_TAC[IN_SUPPORT]]);

val ITERATE_EQ_NEUTRAL = prove
 (`!op. MONOIDAL op
        ==> !f:'a->'b s. (!x. x IN s ==> (f(x) = NEUTRAL op))
                       ==> (ITERATE op s f = NEUTRAL op)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUPPORT op (f:'a->'b) s = {}` ASSUME_TAC THENL
   [PROVE_TAC[EXTENSION, NOT_IN_EMPTY, IN_SUPPORT],
    PROVE_TAC[ITERATE_CLAUSES, ITERATE_SUPPORT]]);

val ITERATE_SING = prove
 (`!op. MONOIDAL op ==> !f:'a->'b x. (ITERATE op {x} f = f x)`,
  SIMP_TAC bool_ss[ITERATE_CLAUSES, FINITE_RULES, NOT_IN_EMPTY] THEN
  PROVE_TAC[MONOIDAL_DEF]);

val ITERATE_DELETE = prove
 (`!op. MONOIDAL op
        ==> !f:'a->'b s a. FINITE s /\ a IN s
                         ==> (op (f a) (ITERATE op (s DELETE a) f) =
                              ITERATE op s f)`,
  PROVE_TAC[ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE, INSERT_DELETE]);

val ITERATE_DELTA = prove
 (`!op. MONOIDAL op
        ==> (!f a s. ITERATE op s (\x. if x = a then f(x) else NEUTRAL op) =
                    if a IN s then f(a) else NEUTRAL op)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES] THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES, ITERATE_SING]);

val FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f: 'a ->'b) A s. 
(!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                  FINITE A ==> FINITE {x | x IN s /\ f(x) IN A}`,
  GEN_TAC THEN CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN
  REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ (f:'a ->'b) x IN EMPTY} = EMPTY`
    SUBST1_TAC THEN REWRITE_TAC[FINITE_RULES] THEN
REWRITE_TAC[EXTENSION] THEN
CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[NOT_IN_EMPTY],
ALL_TAC] THEN
  X_GEN_TAC `t:'b->bool` THEN
  DISCH_TAC THEN X_GEN_TAC `y:'b` THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:'a ->'b) x IN (y INSERT t)} =
                if (?x. x IN s /\ (f x = y))
                then (@x. x IN s /\ (f x = y)) INSERT {x | x IN s /\ f x IN t}
                else {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [ALL_TAC, COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION, IN_INSERT] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV)THENL
   [ALL_TAC, PROVE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `z = @x. x IN s /\ ((f:'a ->'b) x = y)` THEN
  PROVE_TAC[]);

val EQ_IMP = TAUT `(a <=> b) ==> a ==> b`;

val FINITE_IMAGE_INJ_EQ = prove
 (`!(f: 'a ->'b) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss[IMAGE_FINITE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[AND_IMP_INTRO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]);

val ITERATE_IMAGE = prove
 (`!op. MONOIDAL op
       ==> !f:'a ->'b g:'b ->'c s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (ITERATE op (IMAGE f s) g = ITERATE op s (g o f))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!s. FINITE s /\
        (!x y: 'a. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (ITERATE op (IMAGE f s) (g: 'b ->'c) = ITERATE op s (g o f))`
  ASSUME_TAC THENL
   [REWRITE_TAC [GSYM AND_IMP_INTRO] THEN 
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    ASM_SIMP_TAC std_ss[ITERATE_CLAUSES, IMAGE_CLAUSES,IMAGE_FINITE] THEN
    REWRITE_TAC[IN_INSERT] THEN PROVE_TAC[IN_IMAGE],
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
    MATCH_MP_TAC (prove
(`(a <=> a') /\ (a' ==> (b = b')) ==>
 ((if a then b else c) = if a' then b' else c)`,PROVE_TAC[])) THEN
    REWRITE_TAC[SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ,
      FIRST_X_ASSUM MATCH_MP_TAC] THEN PROVE_TAC[IN_SUPPORT]]);

open HolKernel;

val ITERATE_BIJECTION = prove
 (`!op. MONOIDAL op
        ==>  ! f:'a -> 'b p s.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p(x) = y))
                ==> (ITERATE op s f = ITERATE op s (f o p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ITERATE op (IMAGE (p:'a -> 'a) s) (f:'a -> 'b)` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION, IN_IMAGE],
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (INST_TYPE [beta |-> alpha] ITERATE_IMAGE))] THEN
  PROVE_TAC[]);


val ITERATE_ITERATE_PRODUCT = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'a->'b->bool x:'a->'b->'c.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> (ITERATE op s (\i. ITERATE op (t i) (x i)) =
                     ITERATE op {i,j | i IN s /\ j IN t i} (\(i,j). x i j))`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[NOT_IN_EMPTY, 
					   prove(`{a,b | F} = {}`, REWRITE_TAC[EXTENSION] THEN
											   CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
											   REWRITE_TAC[NOT_IN_EMPTY]), 
					   ITERATE_CLAUSES] THEN
  REWRITE_TAC[prove(`{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}`, 
			REWRITE_TAC[EXTENSION, IN_UNION, IN_IMAGE] THEN
			CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
			PROVE_TAC[IN_INSERT])] THEN
  ASM_SIMP_TAC bool_ss[FINITE_INSERT, ITERATE_CLAUSES, IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION th) o
   rand o snd)) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC bool_ss[IMAGE_FINITE, FINITE_PRODUCT_DEPENDENT, IN_INSERT] THEN
    REWRITE_TAC[DISJOINT_DEF, EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY] THEN
	CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[EXISTS_PROD, FORALL_PROD, PAIR_EQ],
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_IMAGE th) o
   rand o snd)) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [SIMP_TAC bool_ss[FORALL_PROD, PAIR_EQ],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ETA_AX]]);


val ITERATE_EQ = prove
 (`!op. MONOIDAL op
        ==> !f:'a->'b g s.
         (!x. x IN s ==> (f x = g x)) ==> (ITERATE op s f = ITERATE op s g)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN `SUPPORT op g s = SUPPORT op (f:'a->'b) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_SUPPORT] THEN PROVE_TAC[], ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `FINITE(SUPPORT op (f:'a->'b) s) /\
    (!x. x IN (SUPPORT op f s) ==> (f x = g x))`
  MP_TAC THENL [PROVE_TAC[IN_SUPPORT], REWRITE_TAC[GSYM AND_IMP_INTRO]] THEN
  SPEC_TAC(`SUPPORT op (f:'a->'b) s`,`t:'a->bool`) THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES] THEN
  PROVE_TAC[IN_INSERT]);


val ITERATE_EQ_GENERAL = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h.
                (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
                ==> (ITERATE op s f = ITERATE op t g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (h:'a->'b) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE] THEN PROVE_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ITERATE op s ((g:'b->'c) o (h:'a->'b))` THEN CONJ_TAC THENL
   [PROVE_TAC[ITERATE_EQ, o_THM],
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
    PROVE_TAC[]]);

val ITERATE_EQ_GENERAL_INVERSES = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h k.
                (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
                ==> (ITERATE op s f = ITERATE op t g)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
  EXISTS_TAC `h:'a->'b` THEN PROVE_TAC[]);

val ITERATE_OP = prove
 (`!op. MONOIDAL op
        ==> !f g s. FINITE s
                    ==> (ITERATE op s (\x. op (f x) (g x)) =
                        op (ITERATE op s f) (ITERATE op s g))`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES, MONOIDAL_AC]);

val ITERATE_SUPERSET = prove
 (`!op. MONOIDAL op
        ==> !f:'a->'b u v.
            u SUBSET v /\
            (!x. x IN v /\ ~(x IN u) ==> (f(x) = NEUTRAL op))
            ==> (ITERATE op v f = ITERATE op u f)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[SUPPORT_DEF, EXTENSION] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_DEF]);

val ITERATE_CASES = prove
 (`!op. MONOIDAL op
        ==> !s P f g:'a->'b.
                FINITE s
                ==> (ITERATE op s (\x. if P x then f x else g x) =
                     op (ITERATE op {x | x IN s /\ P x} f)
                        (ITERATE op {x | x IN s /\ ~P x} g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `op (ITERATE op {x | x IN s /\ P x} (\x. if P x then f x else (g:'a->'b) x))
       (ITERATE op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fn th => ASM_SIMP_TAC std_ss[GSYM(MATCH_MP (INST_TYPE [beta |-> alpha, alpha |-> beta] ITERATE_UNION) th),
      FINITE_RESTRICT,
      prove(`DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}`, 
		SIMP_TAC bool_ss[IN_DISJOINT, GSPEC_ETA, IN_ABS] THEN PROVE_TAC[])]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
	SIMP_TAC bool_ss[GSYM GSPEC_OR, GSYM LEFT_AND_OVER_OR, EXCLUDED_MIDDLE, GSPEC_ID],
    BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC bool_ss[GSPEC_ETA, IN_ABS]]);

val ITERATE_CLAUSES_NUMSEG = prove
 (`!op. MONOIDAL op
        ==> (!m. ITERATE op (count 0 DIFF count m) f = if m = 0 then f(0) else NEUTRAL op) /\
            (!m n. ITERATE op (count (SUC n) DIFF count m) f =
                      if m < SUC n then op (ITERATE op (count (SUC n) DIFF count m) f) (f(SUC n))
                      else ITERATE op (count (n) DIFF count m) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; FINITE_EMPTY] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[monoidal]);;

(* ------------------------------------------------------------------------- *)
(* Sums of natural numbers.                                                  *)
(* ------------------------------------------------------------------------- *)
val NSUM_DEF = Define
  `NSUM = ITERATE (( + ):num->num->num)`;

val NEUTRAL_ADD = prove
 (`NEUTRAL(( + ):num->num->num) = 0`,
  REWRITE_TAC[NEUTRAL_DEF] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  PROVE_TAC[ADD_CLAUSES]);

val NEUTRAL_MUL = prove
 (`NEUTRAL(( * ):num->num->num) = 1`,
  REWRITE_TAC[NEUTRAL_DEF] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  PROVE_TAC[MULT_CLAUSES, MULT_EQ_1]);

val MONOIDAL_ADD = prove
 (`MONOIDAL(( + ):num->num->num)`,
  REWRITE_TAC[MONOIDAL_DEF, NEUTRAL_ADD] THEN ARITH_TAC);

val MONOIDAL_MUL = prove
 (`MONOIDAL(( * ):num->num->num)`,
  REWRITE_TAC[MONOIDAL_DEF, NEUTRAL_MUL] THEN ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Sums of real numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

val NEUTRAL_REAL_ADD = prove
 (`NEUTRAL(( + ):real->real->real) = &0`,
  REWRITE_TAC[NEUTRAL_DEF] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  PROVE_TAC[REAL_ADD_LID, REAL_ADD_RID]);

val NEUTRAL_REAL_MUL = prove
 (`NEUTRAL(( * ):real->real->real) = &1`,
  REWRITE_TAC[NEUTRAL_DEF] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  PROVE_TAC[REAL_MUL_LID, REAL_MUL_RID]);

val MONOIDAL_REAL_ADD = prove
 (`MONOIDAL (( + ):real->real->real)`,
  REWRITE_TAC[MONOIDAL_DEF, NEUTRAL_REAL_ADD] THEN REAL_ARITH_TAC);

val MONOIDAL_REAL_MUL = prove
 (`MONOIDAL (( * ):real->real->real)`,
  REWRITE_TAC[MONOIDAL_DEF, NEUTRAL_REAL_MUL] THEN REAL_ARITH_TAC);

val SUM_DEF = Define
  `SUM = ITERATE (( + ):real->real->real)`;

val SUM_CLAUSES = prove
 (`(!f. SUM {} f = &0) /\
   (!x f s. FINITE(s)
            ==> (SUM (x INSERT s) f =
                 if x IN s then SUM s f else f(x) + SUM s f))`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC bool_ss[ITERATE_CLAUSES, MONOIDAL_REAL_ADD]);

val SUM_SUPPORT = prove
 (`!f s. SUM (SUPPORT (+) f s) f = SUM s f`,
  SIMP_TAC bool_ss[SUM_DEF, ITERATE_DEF, SUPPORT_SUPPORT]);

val SUM_ADD = prove
 (`!f g s. FINITE s ==> ((SUM s (\x. f(x) + g(x)) = SUM s f + SUM s g))`,
  SIMP_TAC bool_ss[SUM_DEF, ITERATE_OP, MONOIDAL_REAL_ADD]);

val SUM_EQ_0 = prove
 (`!f s. (!x:'a. x IN s ==> (f(x) = &0)) ==> (SUM s f = &0)`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC bool_ss[ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_ADD]);

val SUM_0 = prove
 (`!s:'a->bool. SUM s (\n. &0) = &0`,
  SIMP_TAC bool_ss[SUM_EQ_0]);

val SUM_LMUL = prove
 (`!f c s:'a->bool. SUM s (\x. c * f(x)) = c * SUM s f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, SUM_0] THEN REWRITE_TAC[SUM_DEF] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN `SUPPORT (+) (\x:'a. c * f(x)) s = SUPPORT (+) f s` SUBST1_TAC
  THENL [ASM_SIMP_TAC bool_ss[SUPPORT_DEF, REAL_ENTIRE, NEUTRAL_REAL_ADD],
         ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_REAL_ADD, REAL_MUL_RZERO] THEN
  UNDISCH_TAC `FINITE (SUPPORT (+) f (s:'a->bool))` THEN
  SPEC_TAC(`SUPPORT (+) f (s:'a->bool)`,`t:'a->bool`) THEN
  REWRITE_TAC[GSYM SUM_DEF] THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[SUM_CLAUSES, REAL_MUL_RZERO, REAL_ADD_LDISTRIB]);

val SUM_RMUL = prove
 (`!f c s:'a->bool. SUM s (\x. f(x) * c) = SUM s f * c`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[SUM_LMUL]);

val SUM_NEG = prove
 (`!f s. SUM s (\x. -(f(x))) = -(SUM s f)`,
  ONCE_REWRITE_TAC[REAL_ARITH ``-x = -(&1) * x``] THEN
  SIMP_TAC bool_ss[SUM_LMUL]);

val SUM_SUB = prove
 (`!f g s. FINITE s ==> (SUM s (\x. f(x) - g(x)) = SUM s f - SUM s g)`,
  ONCE_REWRITE_TAC[real_sub] THEN SIMP_TAC bool_ss[SUM_NEG, SUM_ADD]);

val SUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (SUM s f = SUM s g)`,
  REWRITE_TAC[SUM_DEF] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_DELETE = prove
 (`!f s a. FINITE s /\ a IN s ==> (SUM (s DELETE a) f = SUM s f - f(a))`,
  SIMP_TAC bool_ss[REAL_ARITH ``(y = z - x) <=> (x + y = z:real)``, SUM_DEF, ITERATE_DELETE,
           MONOIDAL_REAL_ADD]);

val SUM_SING = prove
 (`!f x. SUM {x} f = f(x)`,
  SIMP_TAC bool_ss[SUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, REAL_ADD_RID]);

val SUM_DELTA = prove
 (`!s a. SUM s (\x. if x = a:'a then b else &0) = if a IN s then b else &0`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC bool_ss[ITERATE_DELTA, MONOIDAL_REAL_ADD]);

val SUM_SWAP = prove
 (`!f:'a->'b->real s t.
      FINITE(s) /\ FINITE(t)
      ==> (SUM s (\i. SUM t (f i)) = SUM t (\j. SUM s (\i. f i j)))`,
  GEN_TAC THEN SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[SUM_CLAUSES, SUM_0, SUM_ADD] THEN REWRITE_TAC[ETA_AX]);

val SUM_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (SUM (IMAGE f s) g = SUM s (g o f))`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_SUPERSET = prove
 (`!f:'a->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> (SUM v f = SUM u f)`,
  SIMP_TAC bool_ss[SUM_DEF, GSYM NEUTRAL_REAL_ADD, ITERATE_SUPERSET, MONOIDAL_REAL_ADD]);

val SUM_RESTRICT_SET = prove
 (`!P s f. SUM {x | x IN s /\ P x} f = SUM s (\x. if P x then f x else &0)`,
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DEF, NEUTRAL_REAL_ADD] THEN SIMP_TAC bool_ss[GSPEC_ETA, IN_ABS] THEN
  REWRITE_TAC[prove(`~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)`, PROVE_TAC[]),
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC bool_ss[IN_ABS]);

val SUM_SUM_PRODUCT = prove
 (`!s:'a->bool t:'a->'b->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> (SUM s (\i. SUM (t i) (x i)) =
             SUM {i,j | i IN s /\ j IN t i} (\(i,j). x i j))`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL = prove
 (`!s:'a->bool t:'b->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
        ==> (SUM s f = SUM t g)`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL_INVERSES = prove
 (`!s:'a->bool t:'b->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
        ==> (SUM s f = SUM t g)`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CASES = prove
 (`!s P f g. FINITE s
             ==> (SUM s (\x:'a. if P x then f x else g x) =
                  SUM {x | x IN s /\ P x} f + SUM {x | x IN s /\ ~P x} g)`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CASES_1 = prove
 (`!s a. FINITE s /\ a IN s
         ==> (SUM s (\x. if x = a then y else f(x)) = SUM s f + (y - f a))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC bool_ss[SUM_CASES] THEN
  ASM_SIMP_TAC bool_ss[GSYM IN_DELETE, GSPEC_ID, SUM_DELETE] THEN
  ASM_SIMP_TAC bool_ss[prove(`a IN s ==> ({x | x IN s /\ (x = a)} = {a})`,
		SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS, IN_SING] THEN PROVE_TAC[])] THEN
  REWRITE_TAC[SUM_SING] THEN REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Specialize them to sums over intervals of numbers.                        *)
(* ------------------------------------------------------------------------- *)

val SUM_ADD_COUNT = prove
 (`!f g n. SUM (count n) (\i. f(i) + g(i)) = SUM (count n) f + SUM (count n) g`,
  SIMP_TAC bool_ss[SUM_ADD, FINITE_COUNT]);

val SUM_ADD_NUMSEG = prove
 (`!f g m n.
     SUM (count n DIFF count m) (\i. f(i) + g(i)) =
          SUM (count n DIFF count m) f + SUM (count n DIFF count m) g`,
  SIMP_TAC bool_ss[SUM_ADD, FINITE_COUNT, FINITE_DIFF]);

val SUM_SUB_COUNT = prove
 (`!f g n. SUM (count n) (\i. f(i) - g(i)) = SUM (count n) f - SUM (count n) g`,
  SIMP_TAC bool_ss[SUM_SUB, FINITE_COUNT]);

val SUM_SUB_NUMSEG = prove
 (`!f g m n.
     SUM (count n DIFF count m) (\i. f(i) - g(i)) =
          SUM (count n DIFF count m) f - SUM (count n DIFF count m) g`,
  SIMP_TAC bool_ss[SUM_SUB, FINITE_COUNT, FINITE_DIFF]);

val SUM_EQ_COUNT = prove
 (`!f g n. (!i. i < n ==> (f(i) = g(i)))
             ==> (SUM (count n) f = SUM (count n) g)`,
  PROVE_TAC[SUM_EQ, FINITE_COUNT, IN_COUNT]);

val IN_NUMSEG = store_thm
  ("IN_NUMSEG",
   `!x m n. x IN (count n DIFF count m) =  m <= x /\ x < n`,
   RW_TAC bool_ss [GSPECIFICATION, count_def, DIFF_DEF, NOT_LESS, CONJ_SYM]);

val SUM_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i < n ==> (f(i) = g(i)))
             ==> (SUM (count n DIFF count m) f = SUM (count n DIFF count m) g)`,
  PROVE_TAC[SUM_EQ, FINITE_COUNT, FINITE_DIFF, IN_NUMSEG]);

val SUM_EQ_0_COUNT = prove
 (`!f s. (!i. i < n ==> (f(i) = &0)) ==> (SUM (count n) f = &0)`,
  SIMP_TAC bool_ss[SUM_EQ_0, IN_COUNT]);

val SUM_EQ_0_NUMSEG = prove
 (`!f s.
    (!i. m <= i /\ i < n ==> (f(i) = &0)) ==> (SUM (count n DIFF count m) f = &0)`,
  SIMP_TAC bool_ss[SUM_EQ_0, IN_NUMSEG]);

val SUM_SWAP_COUNT = prove
 (`!a b f.
     SUM(count a) (\i. SUM(count b) (f i)) = SUM(count b) (\j. SUM(count a) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  REWRITE_TAC[FINITE_COUNT]);

val SUM_SWAP_NUMSEG = prove
 (`!a b c d f.
     SUM(count b DIFF count a) (\i. SUM(count d DIFF count c) (f i)) =
	 SUM(count d DIFF count c) (\j. SUM(count b DIFF count a) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  SIMP_TAC bool_ss[FINITE_DIFF, FINITE_COUNT]);

val REAL_MUL_SUM = prove
 (`!s t f g.
        FINITE s /\ FINITE t
        ==> (SUM s f * SUM t g = SUM s (\i. SUM t (\j. f(i) * g(j))))`,
  SIMP_TAC bool_ss[SUM_LMUL, SUM_RMUL]);

val REAL_MUL_SUM_COUNT = prove
 (`!m n. SUM (count m) f * SUM (count n) g =
             SUM (count m) (\i. SUM (count n) (\j. f(i) * g(j)))`,
  SIMP_TAC bool_ss[REAL_MUL_SUM, FINITE_COUNT]);

val REAL_MUL_SUM_NUMSEG = prove
 (`!m n p q.
   SUM (count n DIFF count m) f * SUM (count q DIFF count p) g =
       SUM (count n DIFF count m) (\i. SUM (count q DIFF count p) (\j. f(i) * g(j)))`,
  SIMP_TAC bool_ss[REAL_MUL_SUM, FINITE_COUNT, FINITE_DIFF]);

val REAL_MUL_SUM = prove
 (`!s t f g.
        FINITE s /\ FINITE t
        ==> (SUM s f * SUM t g = SUM s (\i. SUM t (\j. f(i) * g(j))))`,
  SIMP_TAC bool_ss[SUM_LMUL, SUM_RMUL]);

val REAL_MUL_SUM_COUNT = prove
 (`!m n. SUM (count m) f * SUM (count n) g =
             SUM (count m) (\i. SUM (count n) (\j. f(i) * g(j)))`,
  SIMP_TAC bool_ss[REAL_MUL_SUM, FINITE_COUNT]);

val REAL_MUL_SUM_NUMSEG = prove
 (`!m n p q.
   SUM (count n DIFF count m) f * SUM (count q DIFF count p) g =
       SUM (count n DIFF count m) (\i. SUM (count q DIFF count p) (\j. f(i) * g(j)))`,
  SIMP_TAC bool_ss[REAL_MUL_SUM, FINITE_COUNT, FINITE_DIFF]);

  
val ITERATE_DELETE = prove
 (`!op. MONOIDAL op
        ==> !f:'a->'b s a. FINITE s /\ a IN s
                         ==> (op (f a) (ITERATE op (s DELETE a) f) =
                              ITERATE op s f)`,
  PROVE_TAC[ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE, INSERT_DELETE]);

val ITERATE_ITERATE_PRODUCT = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'a->'b->bool x:'a->'b->'c.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> (ITERATE op s (\i. ITERATE op (t i) (x i)) =
                     ITERATE op {i,j | i IN s /\ j IN t i} (\(i,j). x i j))`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[NOT_IN_EMPTY, 
					   prove(`{a,b | F} = {}`, REWRITE_TAC[EXTENSION] THEN
											   CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
											   REWRITE_TAC[NOT_IN_EMPTY]), 
					   ITERATE_CLAUSES] THEN
  REWRITE_TAC[prove(`{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}`, 
			REWRITE_TAC[EXTENSION, IN_UNION, IN_IMAGE] THEN
			CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
			PROVE_TAC[IN_INSERT])] THEN
  ASM_SIMP_TAC bool_ss[FINITE_INSERT, ITERATE_CLAUSES, IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION th) o
   rand o snd)) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC bool_ss[IMAGE_FINITE, FINITE_PRODUCT_DEPENDENT, IN_INSERT] THEN
    REWRITE_TAC[DISJOINT_DEF, EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY] THEN
	CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[EXISTS_PROD, FORALL_PROD, PAIR_EQ],
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_IMAGE th) o
   rand o snd)) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [SIMP_TAC bool_ss[FORALL_PROD, PAIR_EQ],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ETA_AX]]);

val ITERATE_EQ_GENERAL = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h.
                (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
                ==> (ITERATE op s f = ITERATE op t g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (h:'a->'b) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE] THEN PROVE_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ITERATE op s ((g:'b->'c) o (h:'a->'b))` THEN CONJ_TAC THENL
   [PROVE_TAC[ITERATE_EQ, o_THM],
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
    PROVE_TAC[]]);

val ITERATE_EQ_GENERAL_INVERSES = prove
 (`!op. MONOIDAL op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h k.
                (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
                ==> (ITERATE op s f = ITERATE op t g)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
  EXISTS_TAC `h:'a->'b` THEN PROVE_TAC[]);

val ITERATE_CASES = prove
 (`!op. MONOIDAL op
        ==> !s P f g:'a->'b.
                FINITE s
                ==> (ITERATE op s (\x. if P x then f x else g x) =
                     op (ITERATE op {x | x IN s /\ P x} f)
                        (ITERATE op {x | x IN s /\ ~P x} g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `op (ITERATE op {x | x IN s /\ P x} (\x. if P x then f x else (g:'a->'b) x))
       (ITERATE op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fn th => ASM_SIMP_TAC std_ss[GSYM(MATCH_MP (INST_TYPE [beta |-> alpha, alpha |-> beta] ITERATE_UNION) th),
      FINITE_RESTRICT,
      prove(`DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}`, 
		SIMP_TAC bool_ss[IN_DISJOINT, GSPEC_ETA, IN_ABS] THEN PROVE_TAC[])]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
	SIMP_TAC bool_ss[GSYM GSPEC_OR, GSYM LEFT_AND_OVER_OR, EXCLUDED_MIDDLE, GSPEC_ID],
    BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC bool_ss[GSPEC_ETA, IN_ABS]]);

val SUM_SUPPORT = prove
 (`!f s. SUM (SUPPORT (+) f s) f = SUM s f`,
  SIMP_TAC bool_ss[SUM_DEF, ITERATE_DEF, SUPPORT_SUPPORT]);

val SUM_DELETE = prove
 (`!f s a. FINITE s /\ a IN s ==> (SUM (s DELETE a) f = SUM s f - f(a))`,
  SIMP_TAC bool_ss[REAL_ARITH ``(y = z - x) <=> (x + y = z:real)``, SUM_DEF, ITERATE_DELETE,
           MONOIDAL_REAL_ADD]);

val SUM_SWAP = prove
 (`!f:'a->'b->real s t.
      FINITE(s) /\ FINITE(t)
      ==> (SUM s (\i. SUM t (f i)) = SUM t (\j. SUM s (\i. f i j)))`,
  GEN_TAC THEN SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[SUM_CLAUSES, SUM_0, SUM_ADD] THEN REWRITE_TAC[ETA_AX]);

val SUM_RESTRICT_SET = prove
 (`!P s f. SUM {x | x IN s /\ P x} f = SUM s (\x. if P x then f x else &0)`,
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DEF, NEUTRAL_REAL_ADD] THEN SIMP_TAC bool_ss[GSPEC_ETA, IN_ABS] THEN
  REWRITE_TAC[prove(`~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)`, PROVE_TAC[]),
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC bool_ss[IN_ABS]);

val SUM_SUM_PRODUCT = prove
 (`!s:'a->bool t:'a->'b->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> (SUM s (\i. SUM (t i) (x i)) =
             SUM {i,j | i IN s /\ j IN t i} (\(i,j). x i j))`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL = prove
 (`!s:'a->bool t:'b->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
        ==> (SUM s f = SUM t g)`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL_INVERSES = prove
 (`!s:'a->bool t:'b->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
        ==> (SUM s f = SUM t g)`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CASES = prove
 (`!s P f g. FINITE s
             ==> (SUM s (\x:'a. if P x then f x else g x) =
                  SUM {x | x IN s /\ P x} f + SUM {x | x IN s /\ ~P x} g)`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CASES_1 = prove
 (`!s a. FINITE s /\ a IN s
         ==> (SUM s (\x. if x = a then y else f(x)) = SUM s f + (y - f a))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC bool_ss[SUM_CASES] THEN
  ASM_SIMP_TAC bool_ss[GSYM IN_DELETE, GSPEC_ID, SUM_DELETE] THEN
  ASM_SIMP_TAC bool_ss[prove(`a IN s ==> ({x | x IN s /\ (x = a)} = {a})`,
		SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS, IN_SING] THEN PROVE_TAC[])] THEN
  REWRITE_TAC[SUM_SING] THEN REAL_ARITH_TAC);

val SUM_SWAP_COUNT = prove
 (`!a b f.
     SUM(count a) (\i. SUM(count b) (f i)) = SUM(count b) (\j. SUM(count a) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  REWRITE_TAC[FINITE_COUNT]);

val SUM_SWAP_NUMSEG = prove
 (`!a b c d f.
     SUM(count b DIFF count a) (\i. SUM(count d DIFF count c) (f i)) =
	 SUM(count d DIFF count c) (\j. SUM(count b DIFF count a) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  SIMP_TAC bool_ss[FINITE_DIFF, FINITE_COUNT]);

val PRODUCT_EQ_COUNT = prove
 (`!f g n. (!i. i < n ==> (f(i) = g(i)))
             ==> (PRODUCT(count(n)) f = PRODUCT(count(n)) g)`,
  PROVE_TAC[PRODUCT_EQ, IN_COUNT]);

val PRODUCT_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i < n ==> (f(i) = g(i)))
             ==> (PRODUCT(count n DIFF count m) f = PRODUCT(count n DIFF count m) g)`,
  PROVE_TAC[PRODUCT_EQ, IN_NUMSEG]);
val PRODUCT_MUL = prove
 (`!f g s. FINITE s ==> (PRODUCT s (\x. f x * g x) = PRODUCT s f * PRODUCT s g)`,
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[PRODUCT_CLAUSES] THEN REAL_ARITH_TAC);

val PRODUCT_MUL_COUNT = prove
 (`!f g n.
     PRODUCT(count(n)) (\x. f x * g x) = PRODUCT(count(n)) f * PRODUCT(count(n)) g`,
  SIMP_TAC bool_ss[PRODUCT_MUL, FINITE_COUNT]);

val PRODUCT_MUL_NUMSEG = prove
 (`!f g m n.
     PRODUCT(count(n) DIFF count(m)) (\x. f x * g x) = PRODUCT(count(n) DIFF count(m)) f * PRODUCT(count(n) DIFF count(m)) g`,
  SIMP_TAC bool_ss[PRODUCT_MUL, FINITE_COUNT, FINITE_DIFF]);

val PRODUCT_DELTA = prove
 (`!s a. PRODUCT s (\x. if x = a:'a then b else &1) = if a IN s then b else &1`,
  REWRITE_TAC[PRODUCT_DEF, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC bool_ss[ITERATE_DELTA, MONOIDAL_REAL_MUL]);  
