Theory normalFormsContext[bare]
Ancestors
  combin normalForms
Libs
  HolKernel Parse boolLib simpLib boolSimps tautLib Canon

(* ------------------------------------------------------------------------- *)
(* Lemmas normalForms.sml formerly proved as it loaded.                      *)
(* ------------------------------------------------------------------------- *)

(* MK_CONJ_EQ, CONJ_RASSOC_CONV, DISJ_RASSOC_CONV support *)

Theorem NF_MK_CONJ_EQ: (a <=> b) /\ (c <=> d) ==> (a /\ c <=> b /\ d)
Proof tautLib.TAUT_TAC
QED

Theorem NF_CONJ_RASSOC: (a /\ b) /\ c <=> b /\ (a /\ c)
Proof tautLib.TAUT_TAC
QED

Theorem NF_DISJ_RASSOC: (a \/ b) \/ c <=> b \/ (a \/ c)
Proof tautLib.TAUT_TAC
QED

(* SKI / SKICo conversions *)

Theorem MK_S:
  !x y. (\v. (x v) (y v)) = S (x:'a->'b->'c) y
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]
QED

Theorem MK_K:
  !x. (\v. x) = (K:'a->'b->'a) x
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]
QED

Theorem MK_I:
  (\v. v) = (I:'a->'a)
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC boolSimps.bool_ss
    [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.I_THM]
QED

Theorem MK_C:
  !x y. (\v. (x v) y) = combin$C (x:'a->'b->'c) y
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC boolSimps.bool_ss
    [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.C_DEF]
QED

Theorem MK_o:
  !x y. (\v:'a. x (y v)) = (x:'b->'c) o y
Proof
  REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
  SIMP_TAC boolSimps.bool_ss
    [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.o_DEF]
QED

Theorem FUN_EQ:
  !(f : 'a -> 'b) g. (!x. f x = g x) <=> (f = g)
Proof
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN REWRITE_TAC []
QED

(* NNF pushes *)

Theorem NOT_TRUE: ~T <=> F
Proof tautLib.TAUT_TAC
QED

Theorem NOT_FALSE: ~F <=> T
Proof tautLib.TAUT_TAC
QED

Theorem IMP_DISJ_THM': !x y. x ==> y <=> y \/ ~x
Proof tautLib.TAUT_TAC
QED

Theorem NIMP_CONJ_THM: !x y. ~(x ==> y) <=> x /\ ~y
Proof tautLib.TAUT_TAC
QED

Theorem EQ_EXPAND': !x y. (x <=> y) <=> (x \/ ~y) /\ (~x \/ y)
Proof tautLib.TAUT_TAC
QED

Theorem NEQ_EXPAND: !x y. ~(x <=> y) <=> (x \/ y) /\ (~x \/ ~y)
Proof tautLib.TAUT_TAC
QED

Theorem COND_EXPAND': !c a b. (if c then a else b) <=> ((~c \/ a) /\ (c \/ b))
Proof tautLib.TAUT_TAC
QED

Theorem NCOND_EXPAND: !c a b. ~(if c then a else b) <=> ((~c \/ ~a) /\ (c \/ ~b))
Proof tautLib.TAUT_TAC
QED

Theorem DE_MORGAN_THM1: !x y. ~(x /\ y) <=> (~x \/ ~y)
Proof tautLib.TAUT_TAC
QED

Theorem DE_MORGAN_THM2: !x y. ~(x \/ y) <=> (~x /\ ~y)
Proof tautLib.TAUT_TAC
QED

Theorem NNF_EXISTS_UNIQUE:
  !p. $?! p <=> ((?(x:'a). p x) /\ !x y. p x /\ p y ==> (x = y))
Proof
  GEN_TAC THEN
  KNOW_TAC ``$?! p = ?!(x:'a). p x`` THEN1
    (CONV_TAC (DEPTH_CONV ETA_CONV) THEN REWRITE_TAC []) THEN
  DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
  REWRITE_TAC [boolTheory.EXISTS_UNIQUE_THM]
QED

Theorem NOT_EXISTS_UNIQUE:
  !p. ~($?! p) <=> ((!(x:'a). ~p x) \/ ?x y. p x /\ p y /\ ~(x = y))
Proof
  REWRITE_TAC [NNF_EXISTS_UNIQUE, DE_MORGAN_THM1] THEN
  CONV_TAC (TOP_DEPTH_CONV (NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV)) THEN
  REWRITE_TAC [NOT_IMP, CONJ_ASSOC]
QED

Theorem RES_FORALL_THM:
  !p m. RES_FORALL p m <=> !(x:'a). x IN p ==> m x
Proof
  REWRITE_TAC [RES_FORALL_DEF] THEN BETA_TAC THEN REWRITE_TAC []
QED

Theorem RES_EXISTS_THM:
  !p m. RES_EXISTS p m <=> ?(x:'a). x IN p /\ m x
Proof
  REWRITE_TAC [RES_EXISTS_DEF] THEN BETA_TAC THEN REWRITE_TAC []
QED

Theorem NOT_RES_FORALL:
  !p m. ~RES_FORALL p m <=> ?(x:'a). x IN p /\ ~m x
Proof
  REWRITE_TAC [RES_FORALL_THM] THEN
  CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM2]
QED

Theorem NOT_RES_EXISTS:
  !p m. ~RES_EXISTS p m <=> !(x:'a). x IN p ==> ~m x
Proof
  REWRITE_TAC [RES_EXISTS_THM] THEN
  CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM2, DE_MORGAN_THM1]
QED

(* TAUTOLOGY_CONV / CONTRACT_CONV support *)

Theorem BOOL_CASES: !a b. (a ==> b) /\ (~a ==> b) ==> b
Proof tautLib.TAUT_TAC
QED

Theorem T_OR: !t. T \/ t <=> T
Proof tautLib.TAUT_TAC
QED

Theorem OR_T: !t. t \/ T <=> T
Proof tautLib.TAUT_TAC
QED

Theorem T_AND: !t. T /\ t <=> t
Proof tautLib.TAUT_TAC
QED

Theorem AND_T: !t. t /\ T <=> t
Proof tautLib.TAUT_TAC
QED

Theorem OR_F: !t. t \/ F <=> t
Proof tautLib.TAUT_TAC
QED

Theorem CONTRACT_DISJ: !a b b'. (~a ==> (b <=> b')) ==> (~a ==> (a \/ b <=> b'))
Proof tautLib.TAUT_TAC
QED

Theorem DISJ_CONGRUENCE: !a b b'. (~a ==> (b <=> b')) ==> (a \/ b <=> a \/ b')
Proof tautLib.TAUT_TAC
QED

Theorem NEG_EQ: !a b. ~(a <=> b) <=> (a <=> ~b)
Proof tautLib.TAUT_TAC
QED

(* Definitional CNF forms; Canon.CNF_CONV is used *)

Theorem EQ_DEFCNF:
  !x y z.
     (x <=> (y <=> z)) <=>
     (z \/ ~y \/ ~x) /\ (y \/ ~z \/ ~x) /\ (x \/ ~y \/ ~z) /\ (x \/ y \/ z)
Proof tautLib.TAUT_TAC
QED

Theorem AND_DEFCNF:
  !x y z. (x <=> (y /\ z)) <=> (y \/ ~x) /\ (z \/ ~x) /\ (x \/ ~y \/ ~z)
Proof tautLib.TAUT_TAC
QED

Theorem OR_DEFCNF:
  !x y z. (x <=> (y \/ z)) <=> (y \/ z \/ ~x) /\ (x \/ ~y) /\ (x \/ ~z)
Proof tautLib.TAUT_TAC
QED

(* Lambda elimination *)

Theorem LAMB_EQ_ELIM:
  !(s:'a -> 'b) t. ((\x. s x) = t) <=> (!x. s x = t x)
Proof
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN SIMP_TAC boolSimps.bool_ss []
QED

Theorem EQ_LAMB_ELIM:
  !(s:'a -> 'b) t. (s = (\x. t x)) <=> (!x. s x = t x)
Proof
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN SIMP_TAC boolSimps.bool_ss []
QED

(* condify_SS support *)

Theorem COND_SIMP:
  !a f g. (if a then f a else g a):'a = (if a then f T else g F)
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_NOT: !a. ~a <=> if a then F else T
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_AND: !a b. a /\ b <=> (if a then b else F)
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_OR: !a b. a \/ b <=> if a then T else b
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_IMP: !a b. a ==> b <=> if a then b else T
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_EQ: !a b. (a <=> b) <=> if a then b else ~b
Proof
  SIMP_TAC boolSimps.bool_ss [EQ_IMP_THM, COND_EXPAND] THEN tautLib.TAUT_TAC
QED

Theorem COND_COND:
  !a b c x y.
    (if (if a then b else c) then (x:'a) else y) =
    (if a then (if b then x else y) else (if c then x else y))
Proof
  STRIP_TAC THEN MP_TAC (SPEC ``a:bool`` EXCLUDED_MIDDLE) THEN
  STRIP_TAC THEN ASM_SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_ETA: !a. (if a then T else F) = a
Proof SIMP_TAC boolSimps.bool_ss []
QED

Theorem COND_BOOL: !c. (if c then T else F) = c
Proof tautLib.TAUT_TAC
QED

(* CONDS_ELIM_CONV / CONDS_CELIM_CONV support *)

Theorem TH_COND:
  ((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
    ==> x = (b /\ x1 \/ ~b /\ x0)
Proof BOOL_CASES_TAC ``b:bool`` THEN ASM_REWRITE_TAC []
QED

Theorem TH_COND':
  ((b <=> F) ==> x = x0) /\ ((b <=> T) ==> x = x1)
    ==> x = ((~b \/ x1) /\ (b \/ x0))
Proof BOOL_CASES_TAC ``b:bool`` THEN ASM_REWRITE_TAC []
QED

(* GEN_NNF_CONV support *)

Theorem PTHS_CONJ:
  (~((!) P) <=> ?x:'a. ~(P x)) /\
  (~((?) P) <=> !x:'a. ~(P x)) /\
  (~((?!) P) <=> (!x:'a. ~(P x)) \/ ?x y. P x /\ P y /\ ~(y = x))
Proof
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) empty_rewrites [GSYM ETA_AX] THEN
  SIMP_TAC boolSimps.bool_ss
    [NOT_EXISTS_THM, NOT_FORALL_THM, boolTheory.EXISTS_UNIQUE_DEF,
     DE_MORGAN_THM, NOT_IMP, GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  REWRITE_TAC []
QED

Theorem PTH_EXU:
  ((?!) P) <=> (?x:'a. P x) /\ !x y. ~(P x) \/ ~(P y) \/ (y = x)
Proof
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] THEN
  SIMP_TAC boolSimps.bool_ss
    [boolTheory.EXISTS_UNIQUE_DEF, tautLib.TAUT `a /\ b ==> c <=> ~a \/ ~b \/ c`] THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  REWRITE_TAC []
QED
