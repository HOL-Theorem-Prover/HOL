
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory;

val _ = new_theory "tailrec";

infix \\ 
val op \\ = op THEN;


(* ---- definitions ----- *)

val TAILREC_PRE_def = Define `
  TAILREC_PRE f1 (f2:'a->'b) guard precondition (x:'a) = 
    ?inv R. inv x /\ WF R /\ (!y. inv y ==> precondition y) /\
            !y. inv y /\ guard y ==> inv (f1 y) /\ R (f1 y) y`;

val TAILREC = Defn.Hol_defn "TAILREC" `
  TAILREC x = if TAILREC_PRE f1 (f2:'a->'b) guard p x /\ guard x then TAILREC (f1 x) else f2 x`;

(* ---- theorems ---- *)

val TAILREC_PRE_INDUCT = store_thm("TAILREC_PRE_INDUCT",
  ``!P. (!x. TAILREC_PRE f1 (f2:'a->'b) g p x /\ p x /\ g x /\ P (f1 x) ==> P x) /\
        (!x. TAILREC_PRE f1 f2 g p x /\ p x /\ ~g x ==> P x) ==>
        (!x. TAILREC_PRE f1 f2 g p x ==> P (x:'a))``,
  NTAC 3 STRIP_TAC \\ REWRITE_TAC [TAILREC_PRE_def] \\ STRIP_TAC
  \\ NTAC 4 (Q.PAT_ASSUM `f (x:'a)` MP_TAC)
  \\ REWRITE_TAC [AND_IMP_INTRO,GSYM CONJ_ASSOC]   
  \\ ONCE_REWRITE_TAC [CONJ_COMM] \\ REWRITE_TAC [GSYM AND_IMP_INTRO]   
  \\ NTAC 2 STRIP_TAC \\ Q.SPEC_TAC (`x`,`x`)
  \\ recInduct (UNDISCH (SPEC_ALL relationTheory.WF_INDUCTION_THM))  
  \\ REPEAT STRIP_TAC \\ Cases_on `g x` THENL [
    `inv' (f1 x) /\ R (f1 x) x` by METIS_TAC [TAILREC_PRE_def]
    \\ Q.PAT_ASSUM `!x. TAILREC_PRE f1 f2 g p x /\ p x /\ g x /\ P (f1 x) ==> P x` MATCH_MP_TAC
    \\ RES_TAC \\ ASM_SIMP_TAC bool_ss [TAILREC_PRE_def]
    \\ Q.EXISTS_TAC `inv'` \\ Q.EXISTS_TAC `R` \\ METIS_TAC [],
    Q.PAT_ASSUM `!x. TAILREC_PRE f1 f2 g p x /\ p x /\ ~g x ==> P x` MATCH_MP_TAC
    \\ ASM_SIMP_TAC bool_ss [TAILREC_PRE_def]
    \\ Q.EXISTS_TAC `inv'` \\ Q.EXISTS_TAC `R` \\ METIS_TAC []]);

val TAILREC_PRE_STEP = prove(
  ``TAILREC_PRE f1 (f2:'a->'b) g p x /\ p x /\ g x ==> TAILREC_PRE f1 (f2:'a->'b) g p (f1 x)``,
  SIMP_TAC bool_ss [TAILREC_PRE_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `inv'` \\ Q.EXISTS_TAC `R` \\ METIS_TAC []);

val TAILREC_LEMMA = METIS_PROVE (map (DISCH_ALL) (Defn.eqns_of TAILREC))
  ``(?R. (!x. TAILREC_PRE f1 (f2:'a->'b) g p x /\ g x ==> R (f1 x) x) /\ WF R) ==>
    (TAILREC f1 f2 g p x = if TAILREC_PRE f1 (f2:'a->'b) g p x /\ g x 
                          then TAILREC f1 f2 g p (f1 x) else f2 x)``;

val TAILREC_def = store_thm("TAILREC_def",
  ``TAILREC f1 f2 g p x = if TAILREC_PRE f1 (f2:'a->'b) g p x /\ g x 
                          then TAILREC f1 f2 g p (f1 x) else f2 x``,
  MATCH_MP_TAC TAILREC_LEMMA
  \\ Q.EXISTS_TAC `(\x y. TAILREC_PRE f1 f2 g p y /\ p y /\ g y /\ (x = f1 y))`
  \\ STRIP_TAC THENL [  
    SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [TAILREC_PRE_def] 
    \\ REPEAT STRIP_TAC \\ RES_TAC,
    SIMP_TAC std_ss [relationTheory.WF_EQ_INDUCTION_THM] \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `TAILREC_PRE f1 f2 g p x`) THEN1 METIS_TAC []
    \\ Q.PAT_ASSUM `TAILREC_PRE f1 f2 g p x` MP_TAC 
    \\ Q.SPEC_TAC (`x`,`x`) \\ MATCH_MP_TAC TAILREC_PRE_INDUCT \\ METIS_TAC []]);

val TAILREC_THM = store_thm("TAILREC_THM",
  ``TAILREC_PRE f1 (f2:'a->'b) g p x ==>
      (TAILREC f1 f2 g p x = if g x then TAILREC f1 f2 g p (f1 x) else f2 x)``,
  METIS_TAC [TAILREC_def]);

val TAILREC_PROOF = store_thm("TAILREC_PROOF",
  ``(?m. (!y. P y /\ ~g y ==> p y /\ Q (f2 y)) /\
         (!y. P y /\ g y ==> p y /\ P (f1 y) /\ m (f1 y) < (m y):num)) ==>
    !x. P x ==> Q (TAILREC f1 f2 g p x) /\ TAILREC_PRE f1 (f2:'a->'b) g p x``,
  REPEAT STRIP_TAC 
  \\ `TAILREC_PRE f1 f2 g p x` by 
    (REWRITE_TAC [TAILREC_PRE_def] \\ Q.EXISTS_TAC `P` \\ Q.EXISTS_TAC `measure m` 
     \\ SIMP_TAC bool_ss [prim_recTheory.WF_measure,prim_recTheory.measure_def,
          relationTheory.inv_image_def] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `P x` MP_TAC \\ CONV_TAC (UNBETA_CONV ``x:'a``)
  \\ Q.PAT_ASSUM `TAILREC_PRE f1 f2 g p x` MP_TAC
  \\ MATCH_MP_TAC TAILREC_PRE_INDUCT  
  \\ SIMP_TAC std_ss [] \\ METIS_TAC [TAILREC_def]);
   
val TAILREC_NONREC = store_thm("TAILREC_NONREC",
  ``(TAILREC f1 f2 (\x.F) p x = f2 x) /\ (TAILREC_PRE f1 f2 (\x.F) p x = p x)``,
  ONCE_REWRITE_TAC [TAILREC_def,TAILREC_PRE_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.EXISTS_TAC `p` \\ Q.EXISTS_TAC `measure (\x. 0)`
  \\ ASM_SIMP_TAC std_ss [prim_recTheory.WF_measure]);

val TAILREC_PRE_IMP = store_thm("TAILREC_PRE_IMP", 
  ``(!x. i x ==> p x) /\
    (?f. !x. i x /\ g x ==> i ((f1:'a->'a) x) /\ f (f1 x) < ((f x):num)) ==>
    (i x ==> TAILREC_PRE (f1:'a->'a) (f2:'a->'b) g p x)``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [TAILREC_PRE_def]
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `measure f`
  \\ ASM_REWRITE_TAC [prim_recTheory.WF_measure]
  \\ SIMP_TAC std_ss [prim_recTheory.measure_def,relationTheory.inv_image_def]   
  \\ METIS_TAC []);


val _ = export_theory();
