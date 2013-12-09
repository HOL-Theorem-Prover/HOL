open HolKernel Parse boolLib bossLib
open lcsymtacs
open arithmeticTheory whileTheory pairTheory pred_setTheory progTheory;

val _ = new_theory "triple";

infix \\
val op \\ = op THEN;

(* we define a total-correctness machine-code Hoare triple *)

val TRIPLE_def = Define`
   TRIPLE (assert,model) pre code post =
     FST post ==> FST pre /\
     SPEC model (assert (SND pre)) code (assert (SND post))`

val TERM_TAILREC_def = zDefine`
   TERM_TAILREC f g (d:'a -> bool # 'b) x =
    let (cond,y) = d (WHILE g f x) in
      (cond /\ (?n. ~g (FUNPOW f n x)),y)`

val SHORT_TERM_TAILREC_def = Define`
   SHORT_TERM_TAILREC (f:'a -> 'a + (bool # 'b)) =
    TERM_TAILREC (OUTL o f) (ISL o f) (OUTR o f)`

val case_sum_def = Define`
   case_sum f1 f2 x = case x of INL y => f1 y | INR y => f2 y`

(* theorems about this Hoare triple *)

val TRIPLE_COMPOSE = Q.store_thm("TRIPLE_COMPOSE",
   `!i p c m q. TRIPLE i p c m /\ TRIPLE i m c q ==> TRIPLE i p c q`,
   simp [TRIPLE_def, FORALL_PROD]
   \\ REPEAT strip_tac
   \\ metis_tac [SPEC_COMPOSE, UNION_IDEMPOT]
   )

val TRIPLE_EXTEND = Q.store_thm("TRIPLE_EXTEND",
   `!i p c q c'. TRIPLE i p c q ==> c SUBSET c' ==> TRIPLE i p c' q`,
   simp [TRIPLE_def, FORALL_PROD]
   \\ REPEAT strip_tac
   \\ metis_tac [SPEC_SUBSET_CODE]
   )

val TRIPLE_REFL = Q.store_thm("TRIPLE_REFL",
   `!i c p. TRIPLE i p c p`,
   simp [FORALL_PROD, TRIPLE_def, SPEC_REFL]
   )

val TRIPLE_COMPOSE_ALT = Q.store_thm("TRIPLE_COMPOSE_ALT",
   `!i p c m q. TRIPLE i m c q ==> TRIPLE i p c m ==> TRIPLE i p c q`,
   metis_tac [TRIPLE_COMPOSE]
   )

val COND_MERGE = Q.store_thm("COND_MERGE",
   `(x1 ==> f (g x2)) /\ (~x1 ==> f (g y2)) ==> f (g (if x1 then x2 else y2))`,
   Cases_on `x1` \\ fs []
   )

val TERM_TAILREC_THM = Q.store_thm("TERM_TAILREC_THM",
   `TERM_TAILREC f g d x = if g x then TERM_TAILREC f g d (f x) else d x`,
   REVERSE (Cases_on `g x`)
   \\ fs [TERM_TAILREC_def, LET_DEF]
   \\ simp [Once WHILE]
   >- (Cases_on `d x`
       \\ Cases_on `q`
       \\ fs []
       \\ qexists_tac `0`
       \\ fs [FUNPOW])
   \\ Cases_on `(d (WHILE g f (f x)))`
   \\ fs []
   \\ Cases_on `q`
   \\ fs []
   \\ REPEAT strip_tac
   \\ eq_tac
   \\ REPEAT strip_tac
   >- (Cases_on `n` \\ fs [FUNPOW] \\ metis_tac [])
   \\ qexists_tac `SUC n`
   \\ fs [FUNPOW]
   )

val () = computeLib.add_persistent_funs ["TERM_TAILREC_THM"]

val TRIPLE_TERM_TAILREC = Q.prove(
   `(!x. ~FST (post (F,x))) ==>
    (!x. TRIPLE i (pre x) c (if g x then pre (f x) else post (d x))) ==>
    (!x. TRIPLE i (pre x) c (post (TERM_TAILREC f g d x)))`,
   Cases_on `i`
   \\ simp [TERM_TAILREC_def, LET_DEF]
   \\ REPEAT strip_tac
   \\ REVERSE (Cases_on `?n. ~g (FUNPOW f n x)`)
   >- (fs []
       \\ Cases_on `d (WHILE g f x)`
       \\ fs [TRIPLE_def])
   \\ qpat_assum `!c. ~bbb` kall_tac
   \\ fs []
   \\ pop_assum mp_tac
   \\ Q.SPEC_TAC (`x`, `x`)
   \\ Induct_on `n`
   \\ fs [FUNPOW]
   \\ REPEAT strip_tac
   >- (qpat_assum `!x.bbb` (MP_TAC o Q.SPEC `x`)
       \\ once_rewrite_tac [WHILE]
       \\ fs []
       \\ Cases_on `d x`
       \\ fs []
       \\ REPEAT strip_tac
       \\ fs []
       \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by all_tac)
       \\ fs []
       \\ Cases_on `q'`
       \\ fs []
       \\ qexists_tac `0`
       \\ fs [FUNPOW])
   \\ REPEAT strip_tac
   \\ REVERSE (Cases_on `g x`)
   >- (pop_assum mp_tac
       \\ pop_assum kall_tac
       \\ pop_assum kall_tac
       \\ qpat_assum `!x.bbb` (MP_TAC o Q.SPEC `x`)
       \\ once_rewrite_tac [WHILE]
       \\ fs []
       \\ Cases_on `d x`
       \\ fs []
       \\ REPEAT strip_tac
       \\ fs []
       \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by all_tac)
       \\ fs []
       \\ Cases_on `q'`
       \\ fs []
       \\ qexists_tac `0`
       \\ fs [FUNPOW])
   \\ match_mp_tac TRIPLE_COMPOSE
   \\ qexists_tac `pre (f x)`
   \\ strip_tac
   >- metis_tac []
   \\ res_tac
   \\ once_rewrite_tac [WHILE]
   \\ fs []
   \\ `(?n. ~g (FUNPOW f n (f x))) = (?n. ~g (FUNPOW f n x))` by all_tac
   >- (REPEAT strip_tac
       \\ eq_tac
       \\ REPEAT strip_tac
       >- (qexists_tac `SUC n'` \\ fs [FUNPOW])
       \\ Cases_on `n'`
       \\ fs [FUNPOW]
       \\ metis_tac [])
   \\ fs []
   )

val case_sum_thm = Q.prove(
   `!x. case_sum pre post x = if ISL x then pre (OUTL x) else post (OUTR x)`,
   Cases \\ SRW_TAC [] [case_sum_def])

val SHORT_TERM_TAILREC = Q.store_thm("SHORT_TERM_TAILREC",
   `(!x. TRIPLE i (pre x) c (case_sum pre post (f x))) ==>
    (!c x state. ~(FST (post (F,x)))) ==>
    (!x. TRIPLE i (pre x) c (post (SHORT_TERM_TAILREC f x)))`,
   simp [SHORT_TERM_TAILREC_def, LET_DEF]
   \\ REPEAT strip_tac
   \\ match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] TRIPLE_TERM_TAILREC)
   \\ fs [case_sum_thm]
   )

val TRIPLE_FRAME_BOOL = Q.store_thm("TRIPLE_FRAME_BOOL",
   `!i. TRIPLE i (c1,pre) code (c2,post) ==>
        !c. TRIPLE i (c /\ c1,pre) code (c /\ c2,post)`,
   simp [TRIPLE_def, FORALL_PROD]
   \\ REPEAT strip_tac
   \\ Cases_on `c`
   \\ fs []
   )

val INTRO_TRIPLE = Q.store_thm("INTRO_TRIPLE",
   `!M. (side ==> SPEC (SND M) (FST M pre) code (FST M post)) ==>
        !c. TRIPLE M (c, pre) code (c /\ side, post)`,
   Cases \\ SIMP_TAC std_ss [TRIPLE_def]
   )

val _ = export_theory()
