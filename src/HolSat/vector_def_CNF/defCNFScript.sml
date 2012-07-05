open HolKernel Parse boolLib simpLib numLib rich_listTheory
     arithmeticTheory

open TotalDefn BasicProvers
val _ = new_theory "defCNF";

infixr 0 THEN ORELSE THENL ++ || << |-> THENC;
infixr 1 >> THEN1;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;
val op<< = op THENL;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_def = Define`
  (UNIQUE (v:num->bool) n (conn, INL i, INL j) = (v n = conn (v i) (v j))) /\
  (UNIQUE v n (conn, INL i, INR b) = (v n = conn (v i) b)) /\
  (UNIQUE v n (conn, INR a, INL j) = (v n = conn a (v j))) /\
  (UNIQUE v n (conn, INR a, INR b) = (v n = conn a b))`;

val DEF_def = Define
  `(DEF (v:num->bool) n [] = T) /\
   (DEF v n (x :: xs) = UNIQUE v n x /\ DEF v (SUC n) xs)`;

val OK_def = Define
  `(OK n ((conn:bool->bool->bool), INL i, INL j) = i < n /\ j < n) /\
   (OK n (conn, INL i, INR (b:bool)) = i < n) /\
   (OK n (conn, INR (a:bool), INL j) = j < n) /\
   (OK n (conn, INR a, INR b) = T)`;

val OKDEF_def = Define
  `(OKDEF n [] = T) /\
   (OKDEF n (x :: xs) = OK n x /\ OKDEF (SUC n) xs)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val DEF_SNOC = store_thm
  ("DEF_SNOC",
   ``!n x l v. DEF v n (SNOC x l) = DEF v n l /\ UNIQUE v (n + LENGTH l) x``,
   (Induct_on `l` THEN1 RW_TAC arith_ss [SNOC, DEF_def, LENGTH]) THEN
   RW_TAC std_ss [SNOC, LENGTH, DEF_def, ADD_CLAUSES, CONJ_ASSOC]);

val OKDEF_SNOC = store_thm
  ("OKDEF_SNOC",
   ``!n x l. OKDEF n (SNOC x l) = OKDEF n l /\ OK (n + LENGTH l) x``,
   (Induct_on `l` THEN1 RW_TAC arith_ss [SNOC, OKDEF_def, LENGTH]) THEN
   RW_TAC std_ss [SNOC, LENGTH, OKDEF_def, ADD_CLAUSES, CONJ_ASSOC]);

val CONSISTENCY = store_thm
  ("CONSISTENCY",
   ``!n l. OKDEF n l ==> ?v. DEF v n l``,
   REPEAT GEN_TAC THEN
   Q.SPEC_TAC (`n`, `n`) THEN
   Q.SPEC_TAC (`l`, `l`) THEN
   HO_MATCH_MP_TAC SNOC_INDUCT THEN
   (CONJ_TAC THEN1 RW_TAC std_ss [DEF_def]) THEN
   RW_TAC std_ss [OKDEF_SNOC, DEF_SNOC] THEN
   Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`) THEN
   RW_TAC std_ss [] THEN
   (Q_TAC SUFF_TAC
    `(!w. (!m. m < n + LENGTH l ==> (w m = v m)) ==> DEF w n l) /\
     ?w. (!m. m < n + LENGTH l ==> (w m = v m)) /\ UNIQUE w (n + LENGTH l) x`
    THEN1 PROVE_TAC []) THEN
   CONJ_TAC THENL
   [STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    Q.SPEC_TAC (`n`, `n`) THEN
    (Induct_on `l` THEN1 RW_TAC std_ss [DEF_def]) THEN
    RW_TAC std_ss [LENGTH, ADD_CLAUSES, DEF_def, OKDEF_def] THEN
    Q.PAT_ASSUM `UNIQUE P Q R` MP_TAC THEN
    Q.PAT_ASSUM `OK P Q` MP_TAC THEN
    Q.PAT_ASSUM `!n. OKDEF P Q ==> X` (K ALL_TAC) THEN
    Q.PAT_ASSUM `DEF P Q R` (K ALL_TAC) THEN
    Q.PAT_ASSUM `OKDEF P Q` (K ALL_TAC) THEN
    (Cases_on `h` THEN
     Cases_on `r` THEN
     Cases_on `q'` THEN
     Cases_on `r'` THEN
     RW_TAC std_ss [UNIQUE_def, OK_def]) THENL
    [Q.PAT_ASSUM `!m. P m`
     (fn th =>
      MP_TAC (Q.SPEC `n` th) THEN
      MP_TAC (Q.SPEC `x` th) THEN
      MP_TAC (Q.SPEC `x'` th)) THEN
     RW_TAC arith_ss [],
     Q.PAT_ASSUM `!m. P m`
     (fn th =>
      MP_TAC (Q.SPEC `n` th) THEN
      MP_TAC (Q.SPEC `x` th)) THEN
     RW_TAC arith_ss [],
     Q.PAT_ASSUM `!m. P m`
     (fn th =>
      MP_TAC (Q.SPEC `n` th) THEN
      MP_TAC (Q.SPEC `x` th)) THEN
     RW_TAC arith_ss [],
     Q.PAT_ASSUM `!m. P m`
     (fn th =>
      MP_TAC (Q.SPEC `n` th)) THEN
     RW_TAC arith_ss []],
    Q.PAT_ASSUM `OK P Q` MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    (Cases_on `x` THEN
     Cases_on `r` THEN
     Cases_on `q'` THEN
     Cases_on `r'` THEN
     RW_TAC std_ss [UNIQUE_def, OK_def]) THENL
    [Q.EXISTS_TAC `\m. if m = n + LENGTH l then q (v x) (v x') else v m` THEN
     RW_TAC arith_ss [],
     Q.EXISTS_TAC `\m. if m = n + LENGTH l then q (v x) y else v m` THEN
     RW_TAC arith_ss [],
     Q.EXISTS_TAC `\m. if m = n + LENGTH l then q y (v x) else v m` THEN
     RW_TAC arith_ss [],
     Q.EXISTS_TAC `\m. if m = n + LENGTH l then q y y' else v m` THEN
     RW_TAC arith_ss []]]);

val BIGSTEP = store_thm(
  "BIGSTEP",
  ``!P Q R.
       (!v:num->bool. P v ==> (Q = R v)) ==>
       ((?v. P v) /\ Q = (?v. P v /\ R v))``,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [
   STRIP_TAC THEN
   EXISTS_TAC ``v:num->bool`` THEN
   Q.PAT_ASSUM `!v:num->bool. A v` (MP_TAC o Q.SPEC `v`) THEN
   ASM_REWRITE_TAC [],
   STRIP_TAC THEN
   Q.PAT_ASSUM `!v:num->bool. A v` (MP_TAC o Q.SPEC `v`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC ``v:num->bool`` THEN
   ASM_REWRITE_TAC []
  ]);

val FINAL_DEF = store_thm(
  "FINAL_DEF",
  ``!v n x. (v n = x) = (v n = x) /\ DEF v (SUC n) []``,
  SIMP_TAC boolSimps.bool_ss [DEF_def]);

val _ = app
            (fn s => remove_ovl_mapping s {Thy = "defCNF", Name = s})
            ["OKDEF", "DEF", "UNIQUE", "OK"]

val _ = export_theory ();
