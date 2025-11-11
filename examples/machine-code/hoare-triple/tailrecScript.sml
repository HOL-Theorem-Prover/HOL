
Theory tailrec
Ancestors
  pred_set arithmetic While sum

(* ---- definitions ----- *)

Definition TAILREC_PRE_def:
  TAILREC_PRE f1 guard precondition (x:'a) ⇔
    (!k. (!m. m < k ==> guard (FUNPOW f1 m x)) ⇒precondition (FUNPOW f1 k x)) ∧
    ∃n. ~guard (FUNPOW f1 n x)
End

Definition TAILREC_def:
  TAILREC f1 (f2:'a->'b) g x = f2 (WHILE g f1 x)
End

Definition SHORT_TAILREC_def:
  SHORT_TAILREC (f:'a -> ('a + 'b) # bool) =
    TAILREC (OUTL o FST o f) (OUTR o FST o f) (ISL o FST o f)
End

Definition SHORT_TAILREC_PRE_def:
  SHORT_TAILREC_PRE (f:'a -> ('a + 'b) # bool) =
    TAILREC_PRE (OUTL o FST o f) (ISL o FST o f) (SND o f)
End


(* ---- theorems ---- *)

Theorem TAILREC_PRE_THM:
  !f1 g p x. TAILREC_PRE f1 g p (x:'a) ⇔
             p x /\ (g x ==> TAILREC_PRE f1 g p (f1 x))
Proof
   REPEAT STRIP_TAC \\ EQ_TAC \\ REWRITE_TAC [TAILREC_PRE_def] \\ STRIP_TAC THENL [
     STRIP_TAC THEN1 METIS_TAC [FUNPOW,DECIDE ``~(n < 0)``]
     \\ REVERSE (REPEAT STRIP_TAC)
     THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ METIS_TAC [])
     \\ Q.PAT_X_ASSUM `!kk. (!m. cc) ==> bb`
          (MATCH_MP_TAC o REWRITE_RULE [FUNPOW] o Q.SPEC `SUC k`)
     \\ REPEAT STRIP_TAC
     \\ Cases_on `m`
     \\ FULL_SIMP_TAC bool_ss [FUNPOW,DECIDE “SUC m < SUC n ⇔ m < n”],
     REVERSE (Cases_on `g x`) THENL [
       REVERSE (REPEAT STRIP_TAC)
       THEN1 (Q.EXISTS_TAC `0` \\ ASM_SIMP_TAC std_ss [FUNPOW])
       \\ Cases_on `k` \\ ASM_SIMP_TAC std_ss [FUNPOW]
       \\ METIS_TAC [DECIDE ``0 < SUC n``,FUNPOW],
       RES_TAC \\ REVERSE (REPEAT STRIP_TAC) THEN1 METIS_TAC [FUNPOW]
       \\ Cases_on `k` \\ ASM_SIMP_TAC std_ss [FUNPOW]
       \\ Q.PAT_X_ASSUM `!k. (!m. cc) ==> bb` MATCH_MP_TAC
       \\ METIS_TAC [FUNPOW,DECIDE “SUC m < SUC n ⇔ m < n”]]]
QED

Theorem TAILREC_PRE_INDUCT:
    !P. (!x. TAILREC_PRE f1 g p x /\ p x /\ g x /\ P (f1 x) ==> P x) /\
        (!x. TAILREC_PRE f1 g p x /\ p x /\ ~g x ==> P x) ==>
        (!x. TAILREC_PRE f1 g p x ==> P (x:'a))
Proof
  NTAC 4 STRIP_TAC \\ `?n. ~g (FUNPOW f1 n x)` by METIS_TAC [TAILREC_PRE_def]
  \\ Q.PAT_X_ASSUM `~g (FUNPOW f1 n x)` MP_TAC
  \\ Q.PAT_X_ASSUM `TAILREC_PRE f1 g p x` MP_TAC
  \\ Q.SPEC_TAC (`x`,`x`) \\ Induct_on `n`
  THEN1 (REWRITE_TAC [FUNPOW] \\ REPEAT STRIP_TAC \\ METIS_TAC [TAILREC_PRE_THM])
  \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ REPEAT STRIP_TAC \\ METIS_TAC [TAILREC_PRE_THM]
QED

Theorem TAILREC_THM:
    !f1 (f2:'a->'b) g x. TAILREC f1 f2 g x = if g x then TAILREC f1 f2 g (f1 x) else f2 x
Proof
  REPEAT STRIP_TAC \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [TAILREC_def]))
  \\ ONCE_REWRITE_TAC [WHILE] \\ REWRITE_TAC [TAILREC_def] \\ METIS_TAC []
QED

Theorem TAILREC_PRE_IMP:
    !step guard side.
      (?R. WF R /\ !x. guard x ==> R (step x) x) /\ (!x. side x) ==>
      !x. TAILREC_PRE step guard side x = T
Proof
  REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [TAILREC_PRE_def]
  \\ FULL_SIMP_TAC std_ss [prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def]
  \\ Q.PAT_X_ASSUM `!x. ?n. bbb` (STRIP_ASSUME_TAC o Q.SPEC `\n. FUNPOW step n x`)
  \\ FULL_SIMP_TAC std_ss [FUNPOW_SUC]
  \\ Q.EXISTS_TAC `n` \\ METIS_TAC []
QED

Theorem TAILREC_EQ_THM:
    (f1 = f1') /\ (f2 = (f2':'a->'b)) /\ (g = g') /\ (s = s') ==>
    (TAILREC f1 f2 g = TAILREC f1' f2' g') /\
    (TAILREC_PRE f1 g s = TAILREC_PRE f1' g' s')
Proof
  SIMP_TAC std_ss []
QED

Theorem SHORT_TAILREC_THM:
  !(f:'a -> ('a + 'b) # bool) x.
      (SHORT_TAILREC f x = if ISL (FST (f x)) then
                             SHORT_TAILREC f (OUTL (FST (f x)))
                           else OUTR (FST (f x))) /\
      (SHORT_TAILREC_PRE f x ⇔
       SND (f x) ∧
       (ISL (FST (f x)) ==> SHORT_TAILREC_PRE f (OUTL (FST (f x)))))
Proof
  SIMP_TAC std_ss [SHORT_TAILREC_def,SHORT_TAILREC_PRE_def] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [TAILREC_THM,TAILREC_PRE_THM]))
  \\ SIMP_TAC std_ss []
QED

Theorem SHORT_TAILREC_PRE_INDUCT:
    ∀P.
     (!x. SHORT_TAILREC_PRE f x /\
          SND (f x) /\ (!y. (FST (f x) = INL y) ==> P y) ==>
          P x) ==>
     (∀x. SHORT_TAILREC_PRE f x ⇒ P x)
Proof
  rewrite_tac [SHORT_TAILREC_PRE_def] \\ ntac 2 strip_tac
  \\ ho_match_mp_tac TAILREC_PRE_INDUCT \\ rw []
  \\ res_tac \\ Cases_on `f x` \\ fs [] \\ Cases_on `q` \\ fs []
QED

Theorem SHORT_TAILREC_SIM:
    !f g R P.
      (!x s q r.
         R x s /\ (f x = (q,T)) ==>
         (!y. (q = INL y) ==> ?y1. (g s = (INL y1,T)) /\ R y y1) /\
         (!y. (q = INR y) ==> ?y1. (g s = (INR y1,T)) /\ P y y1)) ==>
      !x. SHORT_TAILREC_PRE f x ==>
          !s. R x s ==>
              P (SHORT_TAILREC f x) (SHORT_TAILREC g s) /\
              SHORT_TAILREC_PRE g s
Proof
  rpt gen_tac \\ strip_tac
  \\ ho_match_mp_tac SHORT_TAILREC_PRE_INDUCT \\ rw []
  \\ Cases_on `f x` \\ fs [] \\ rw []
  \\ first_assum (qspecl_then [`x`,`s`,`q`] mp_tac)
  \\ disch_then (strip_assume_tac o UNDISCH o UNDISCH o
          REWRITE_RULE [GSYM AND_IMP_INTRO])
   \\ rewrite_tac [SHORT_TAILREC_def]
  \\ once_rewrite_tac [TAILREC_THM] \\ fs []
  \\ Cases_on `q` \\ fs [SHORT_TAILREC_def,SHORT_TAILREC_PRE_def]
  \\ once_rewrite_tac [TAILREC_PRE_THM] \\ fs []
QED

