(* ========================================================================= *)
(* Permutations, both general and specifically on finite sets.               *)
(*    (HOL-Light's Library/permutations.ml)                                  *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 2010                            *)
(*              (c) Copyright, Liming Li 2011                                *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib tautLib numLib cardinalTheory hurdUtils;

val _ = new_theory "permutes";

(* ========================================================================= *)
(* HOL-Light compatibility layer                                             *)
(* ========================================================================= *)

(* |- CARD {} = 0 /\
      !x s. FINITE s ==>
            CARD (x INSERT s) = if x IN s then CARD s else SUC (CARD s)
 *)
val CARD_CLAUSES = CONJ CARD_EMPTY (PROVE [CARD_INSERT]
  ``!x s. FINITE s ==>
           (CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))``);

(* |- (!f. IMAGE f {} = {}) /\
      !f x s. IMAGE f (x INSERT s) = f x INSERT IMAGE f s *)
val IMAGE_CLAUSES = CONJ IMAGE_EMPTY IMAGE_INSERT;

(* |- FINITE {} /\ !x s. FINITE (x INSERT s) <=> FINITE s *)
val FINITE_RULES = CONJ FINITE_EMPTY FINITE_INSERT;

(* |- !n. SUC n <> 0 *)
val NOT_SUC = numTheory.NOT_SUC;

(* |- !m n. SUC m = SUC n <=> m = n *)
val SUC_INJ = prim_recTheory.INV_SUC_EQ;

(* |- (!m. ~(m < 0)) /\ !m n. m < SUC n <=> m = n \/ m < n *)
val LT = CONJ (DECIDE ``!m:num. ~(m < 0)``) prim_recTheory.LESS_THM;

(* |- !n. ~(n < n) *)
val LT_REFL = prim_recTheory.LESS_REFL;

(* ========================================================================= *)
(* Permutations, both general and specifically on finite sets.               *)
(* ========================================================================= *)

(* NOTE: the old name `PERMUTES` is conflict with pred_setTheory:

   val _ = overload_on("PERMUTES", ``\f s. BIJ f s s``);

   but the two definitions are not equivalent, according to Michael Norrish.
   So I've chosen to use lower-case name: permutes.
                                           -- Chun Tian (binghe), May 28, 2018
 *)
val _ = set_fixity "permutes" (Infix(NONASSOC, 450)); (* same as relation *)

Definition permutes :
   p permutes s <=> (!x. ~(x IN s) ==> (p(x) = x)) /\ (!y. ?!x. p x = y)
End

(* connection to ‘pred_set$PERMUTES’, added by Chun Tian *)
Theorem permutes_alt :
    !f s. f permutes s <=> f PERMUTES s /\ !x. x NOTIN s ==> f(x) = x
Proof
    RW_TAC std_ss [permutes, BIJ_ALT, IN_FUNSET]
 >> EQ_TAC >> RW_TAC bool_ss []
 >| [ (* goal 1 (of 3) : f x IN s *)
      CCONTR_TAC \\
     ‘f x <> x’ by PROVE_TAC [] \\
     ‘f (f x) = f x’ by PROVE_TAC [] \\
      Q.PAT_X_ASSUM ‘!y. ?!x. f x = y’ (MP_TAC o (Q.SPEC ‘f (x:'a)’)) \\
      RW_TAC std_ss [EXISTS_UNIQUE_THM] \\
      DISJ2_TAC >> qexistsl_tac [‘f x’, ‘x’] >> art [],
      (* goal 2 (of 3): ?!x. x IN s /\ y = f x *)
      Q.PAT_X_ASSUM ‘!y. ?!x. f x = y’ (MP_TAC o (Q.SPEC ‘y’)) \\
      RW_TAC pure_ss [EXISTS_UNIQUE_THM]
      >- (Q.EXISTS_TAC ‘x’ >> METIS_TAC []) \\
      rename1 ‘y = z’ \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 3 (of 3): f x = x *)
      Cases_on ‘y IN s’
      >- (Q.PAT_X_ASSUM ‘!y. y IN s ==> ?!x. x IN s /\ y = f x’
            (MP_TAC o (Q.SPEC ‘y’)) \\
          RW_TAC bool_ss [EXISTS_UNIQUE_THM] >- (Q.EXISTS_TAC ‘x’ >> rw []) \\
          rename1 ‘y = z’ \\
          FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
          CONJ_TAC >> CCONTR_TAC >> METIS_TAC []) \\
     ‘f y = y’ by PROVE_TAC [] \\
      SIMP_TAC std_ss [EXISTS_UNIQUE_THM] \\
      CONJ_TAC >- (Q.EXISTS_TAC ‘y’ >> rw []) \\
      qx_genl_tac [‘x’, ‘z’] >> rpt STRIP_TAC \\
     ‘x NOTIN s’ by METIS_TAC [] \\
     ‘z NOTIN s’ by METIS_TAC [] \\
     ‘f x = x /\ f z = z’ by PROVE_TAC [] \\
      PROVE_TAC [] ]
QED

Theorem permutes_alt_univ :
    !f. f permutes UNIV <=> f PERMUTES UNIV
Proof
    rw [permutes_alt]
QED

Theorem permutes_imp :
    !f s. f permutes s ==> f PERMUTES s
Proof
    RW_TAC bool_ss [permutes_alt]
QED

(* ------------------------------------------------------------------------- *)
(* Inverse function (on whole universe).                                     *)
(* ------------------------------------------------------------------------- *)

Definition inverse :
   inverse (f :'a->'b) = \y. @x. f x = y
End

(* This connection was suggested by Jeremy Dawson *)
Theorem inverse_alt_LINV :
    !f. (!y. ?x. f x = y) /\ (!x y. (f x = f y) ==> (x = y)) ==>
        inverse f = LINV f UNIV
Proof
    Q.X_GEN_TAC ‘f’ >> STRIP_TAC
 >> simp [FUN_EQ_THM]
 >> Q.X_GEN_TAC ‘y’ >> rw [inverse]
 >> SELECT_ELIM_TAC >> rw []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> irule LINV_DEF >> rw [INJ_DEF]
 >> Q.EXISTS_TAC ‘UNIV’ >> rw []
QED

Theorem SURJECTIVE_INVERSE :
   !f. (!y. ?x. f x = y) <=> !y. f (inverse f y) = y
Proof
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL[
REWRITE_TAC[inverse] THEN
CONV_TAC (ONCE_DEPTH_CONV Thm.BETA_CONV) THEN CONV_TAC SELECT_CONV,
Q.EXISTS_TAC(`inverse f y`)] THEN PROVE_TAC[]
QED

Theorem SURJECTIVE_INVERSE_o :
   !f. (!y. ?x. f x = y) <=> (f o inverse f = I)
Proof
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM, SURJECTIVE_INVERSE]
QED

(* cf. cardinalTheory.INJECTIVE_LEFT_INVERSE *)
Theorem INJECTIVE_INVERSE :
   !f. (!x y. (f x = f y) ==> (x = y)) <=> (!x. inverse f (f x) = x)
Proof
  GEN_TAC THEN EQ_TAC THENL[
REPEAT STRIP_TAC THEN
REWRITE_TAC[inverse] THEN
CONV_TAC (ONCE_DEPTH_CONV Thm.BETA_CONV) THEN FIRST_ASSUM MATCH_MP_TAC THEN
CONV_TAC SELECT_CONV THEN Q.EXISTS_TAC(`x`) THEN REFL_TAC,
PROVE_TAC[]]
QED

Theorem INJECTIVE_INVERSE_o :
   !f. (!x y. (f x = f y) ==> (x = y)) = (inverse f o f = I)
Proof
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM, INJECTIVE_INVERSE]
QED

Theorem INVERSE_UNIQUE_o :
   !f g. (f o g = I) /\ (g o f = I) ==> (inverse f = g)
Proof
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM] THEN
  PROVE_TAC[INJECTIVE_INVERSE, SURJECTIVE_INVERSE]
QED

Theorem INVERSE_I :
   inverse I = I
Proof
  MATCH_MP_TAC INVERSE_UNIQUE_o THEN REWRITE_TAC[I_o_ID]
QED

(* ------------------------------------------------------------------------- *)
(* Transpositions.                                                           *)
(* ------------------------------------------------------------------------- *)

(* cf. “pair$SWAP” (pairTheory.SWAP_def) *)
Definition swap_def :
   swap (i,j) k = if k = i then j else if k = j then i else k
End

Theorem SWAP_REFL :
   !a. swap (a,a) = I
Proof
  REWRITE_TAC[FUN_EQ_THM, swap_def, I_THM] THEN PROVE_TAC[]
QED

Theorem SWAP_SYM :
   !a b. swap(a,b) = swap(b,a)
Proof
  REWRITE_TAC[FUN_EQ_THM, swap_def, I_THM] THEN PROVE_TAC[]
QED

Theorem SWAP_IDEMPOTENT :
   !a b. swap(a,b) o swap(a,b) = I
Proof
  REWRITE_TAC[FUN_EQ_THM, swap_def, o_THM, I_THM] THEN PROVE_TAC[]
QED

Theorem INVERSE_SWAP :
   !a b. inverse(swap(a,b)) = swap(a,b)
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[SWAP_IDEMPOTENT]
QED

Theorem SWAP_GALOIS :
   !a b x y. (x = swap(a,b) y) = (y = swap(a,b) x)
Proof
  REWRITE_TAC[swap_def] THEN PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Basic consequences of the definition.                                     *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTES_IN_IMAGE :
   !p s x. p permutes s ==> (p(x) IN s <=> x IN s)
Proof
  REWRITE_TAC[permutes] THEN PROVE_TAC[]
QED

Theorem PERMUTES_IMAGE :
   !p s. p permutes s ==> (IMAGE p s = s)
Proof
  REWRITE_TAC[permutes, EXTENSION, IN_IMAGE] THEN PROVE_TAC[]
QED

Theorem PERMUTES_INJECTIVE :
   !p s. p permutes s ==> !x y. (p(x) = p(y)) = (x = y)
Proof
  REWRITE_TAC[permutes] THEN PROVE_TAC[]
QED

Theorem PERMUTES_SURJECTIVE :
   !p s. p permutes s ==> !y. ?x. p(x) = y
Proof
  REWRITE_TAC[permutes] THEN PROVE_TAC[]
QED

Theorem PERMUTES_INVERSES_o :
   !p s. p permutes s ==> (p o inverse(p) = I) /\ (inverse(p) o p = I)
Proof
  REWRITE_TAC[GSYM INJECTIVE_INVERSE_o, GSYM SURJECTIVE_INVERSE_o] THEN
  REWRITE_TAC[permutes] THEN PROVE_TAC[]
QED

Theorem PERMUTES_INVERSES :
   !p s. p permutes s
         ==> (!x. p(inverse(p) x) = x) /\ (!x. inverse(p) (p x) = x)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM]
QED

Theorem PERMUTES_SUBSET :
   !p s t. p permutes s /\ s SUBSET t ==> p permutes t
Proof
  REWRITE_TAC[permutes, SUBSET_DEF] THEN PROVE_TAC[]
QED

Theorem PERMUTES_EMPTY :
   !p. p permutes {} <=> (p = I)
Proof
  REWRITE_TAC[FUN_EQ_THM, I_THM, permutes, NOT_IN_EMPTY] THEN PROVE_TAC[]
QED

Theorem PERMUTES_SING :
   !p a. p permutes {a} <=> (p = I)
Proof
  REWRITE_TAC[FUN_EQ_THM, I_THM, permutes, IN_SING] THEN PROVE_TAC[]
QED

Theorem PERMUTES_UNIV :
   !p. p permutes UNIV <=> !y. ?!x. p x = y
Proof
  REWRITE_TAC[permutes, IN_UNIV]
QED

Theorem PERMUTES_INVERSE_EQ :
   !p s. p permutes s ==> !x y. (inverse(p) y = x) <=> (p x = y)
Proof
  REWRITE_TAC[permutes, inverse] THEN METIS_TAC[]
QED

Theorem PERMUTES_SWAP :
   !a b s. a IN s /\ b IN s ==> swap(a,b) permutes s
Proof
  REWRITE_TAC[permutes, swap_def] THEN METIS_TAC[]
QED

Theorem PERMUTES_SUPERSET :
   !p s t. p permutes s /\ (!x. x IN (s DIFF t) ==> (p(x) = x))
           ==> p permutes t
Proof
  REWRITE_TAC[permutes, IN_DIFF] THEN PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Group properties.                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTES_I :
   !s. I permutes s
Proof
  REWRITE_TAC[permutes, I_THM] THEN PROVE_TAC[]
QED

Theorem PERMUTES_COMPOSE :
   !p q s x. p permutes s /\ q permutes s ==> (q o p) permutes s
Proof
  REWRITE_TAC[permutes, o_THM] THEN PROVE_TAC[]
QED

Theorem PERMUTES_INVERSE :
   !p s. p permutes s ==> inverse(p) permutes s
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[permutes] THEN PROVE_TAC[]
QED

Theorem PERMUTES_INVERSE_INVERSE :
   !p s. p permutes s ==> (inverse(inverse(p)) = p)
Proof
  REWRITE_TAC [FUN_EQ_THM] THEN
  PROVE_TAC[PERMUTES_INVERSE_EQ, PERMUTES_INVERSE]
QED

(* ------------------------------------------------------------------------- *)
(* The number of permutations on a finite set.                               *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTES_INSERT_LEMMA :
   !p a s. p permutes (a INSERT s) ==> (swap(a,p(a)) o p) permutes s
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
  Q.EXISTS_TAC `a INSERT s` THEN CONJ_TAC THEN
  METIS_TAC[PERMUTES_SWAP, PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_COMPOSE,
            o_THM, swap_def, IN_DIFF]
QED

Theorem PERMUTES_INSERT :
   {p | p permutes (a INSERT s)} =
        IMAGE (\(b,p). swap(a,b) o p)
              {(b,p) | b IN a INSERT s /\ p IN {p | p permutes s}}
Proof
  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN Q.X_GEN_TAC `p: 'a -> 'a` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC std_ss[EXISTS_PROD]THEN EQ_TAC THENL
   [DISCH_TAC THEN
    qexistsl_tac [`(p: 'a -> 'a) a`, `swap(a,p a) o (p: 'a -> 'a)`]  THEN
    ASM_REWRITE_TAC[SWAP_IDEMPOTENT, o_ASSOC, I_o_ID] THEN
    PROVE_TAC[PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_INSERT_LEMMA],
    SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM] THEN
    qx_genl_tac [`b: 'a `, `q: 'a -> 'a `] THEN
    STRIP_TAC THEN MATCH_MP_TAC PERMUTES_COMPOSE THEN
    PROVE_TAC[PERMUTES_SUBSET, SUBSET_DEF, IN_INSERT, PERMUTES_SWAP]]
QED

Theorem HAS_SIZE_PERMUTATIONS :
  !s:'a ->bool n: num.
    (s HAS_SIZE n) ==> ({p | p permutes s} HAS_SIZE (FACT n))
Proof
    SIMP_TAC std_ss [HAS_SIZE, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM]
 >> SET_INDUCT_TAC (* 2 sub-goals here *)
 >> SIMP_TAC std_ss [PERMUTES_EMPTY, CARD_CLAUSES, GSPEC_EQ, FINITE_SING,
                     CARD_SING, FACT]
 >> REWRITE_TAC [GSYM HAS_SIZE, PERMUTES_INSERT]
 >> MATCH_MP_TAC HAS_SIZE_IMAGE_INJ
 >> CONJ_TAC (* still 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      SIMP_TAC std_ss [FORALL_PROD] \\
      CONV_TAC (DEPTH_CONV SET_SPEC_CONV) \\
      REWRITE_TAC[PAIR_EQ] \\
      qx_genl_tac [`b: 'a`, `q: 'a -> 'a`, `c: 'a`, `r: 'a -> 'a`] \\
      STRIP_TAC \\
      Q.SUBGOAL_THEN `c: 'a = b` SUBST_ALL_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        FIRST_X_ASSUM (MP_TAC o C Q.AP_THM `e: 'a`) \\
        REWRITE_TAC [o_THM, swap_def] \\
        Q.SUBGOAL_THEN `((q: 'a -> 'a) e = e) /\ ((r: 'a -> 'a) e = e)`
                (fn th => SIMP_TAC std_ss[th]) \\
        PROVE_TAC [permutes],
        (* goal 1.2 (of 2) *)
        FIRST_X_ASSUM (MP_TAC o Q.AP_TERM `(\q:'a -> 'a. swap(e:'a,b) o q)`) \\
        BETA_TAC \\
        REWRITE_TAC [SWAP_IDEMPOTENT, o_ASSOC, I_o_ID] ],
      (* goal 2 (of 2) *)
      Know `{(b,p) | b IN e INSERT s /\ p IN {p | p permutes s}} =
            (e INSERT s) CROSS {p | p permutes s}`
      >- (REWRITE_TAC [EXTENSION, CROSS_DEF] \\
          GEN_TAC >> REWRITE_TAC [GSPECIFICATION] >> BETA_TAC \\
          REWRITE_TAC [PAIR_EQ] >> EQ_TAC >> STRIP_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1 (of 2) *)
            Cases_on `x'` >> FULL_SIMP_TAC std_ss [],
            (* goal 2.2 (of 2) *)
            Q.EXISTS_TAC `(FST x, SND x)` >> FULL_SIMP_TAC std_ss [] ] ) \\
      DISCH_TAC >> ASM_REWRITE_TAC [] \\
      ASM_SIMP_TAC std_ss [HAS_SIZE, FINITE_INSERT, CARD_CLAUSES, FINITE_CROSS,
                           CARD_CROSS,FACT] ]
QED

Theorem FINITE_PERMUTATIONS :
   !s. FINITE s ==> FINITE {p | p permutes s}
Proof
  METIS_TAC[HAS_SIZE_PERMUTATIONS, HAS_SIZE]
QED

Theorem CARD_PERMUTATIONS :
   !s. FINITE s ==> (CARD {p | p permutes s} = FACT(CARD s))
Proof
  METIS_TAC[HAS_SIZE, HAS_SIZE_PERMUTATIONS]
QED

(* ------------------------------------------------------------------------- *)
(* Alternative characterizations of permutation of finite set.               *)
(* ------------------------------------------------------------------------- *)

(* TODO: the following 2 theorem need long proof search of METIC_TAC *)
Theorem PERMUTES_FINITE_INJECTIVE :
   !s: 'a->bool p.
        FINITE s
        ==> (p permutes s <=>
             (!x. ~(x IN s) ==> (p x = x)) /\
             (!x. x IN s ==> p x IN s) /\
             (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y)))
Proof
  REWRITE_TAC[permutes] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o Q.SPEC `p: 'a -> 'a ` o MATCH_MP
   (REWRITE_RULE[GSYM AND_IMP_INTRO] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_SIMP_TAC std_ss[SUBSET_DEF, FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN Q.X_GEN_TAC `y: 'a ` THEN
  Q.ASM_CASES_TAC `(y: 'a) IN s` THEN METIS_TAC[]
QED

Theorem PERMUTES_FINITE_SURJECTIVE :
   !s: 'a ->bool p.
        FINITE s
        ==> (p permutes s <=>
             (!x. ~(x IN s) ==> (p x = x)) /\ (!x. x IN s ==> p x IN s) /\
             (!y. y IN s ==> ?x. x IN s /\ (p x = y)))
Proof
  REWRITE_TAC[permutes] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o Q.SPEC `p: 'a -> 'a ` o MATCH_MP
   (REWRITE_RULE[GSYM AND_IMP_INTRO] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_SIMP_TAC std_ss[SUBSET_DEF, FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN Q.X_GEN_TAC `y: 'a ` THEN
  Q.ASM_CASES_TAC `(y: 'a) IN s` THEN METIS_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Various combinations of transpositions with 2, 1 and 0 common elements.   *)
(* ------------------------------------------------------------------------- *)

Theorem SWAP_COMMON :
  !a b c: 'a. ~(a = c) /\ ~(b = c) ==>
              (swap(a,b) o swap(a,c) = swap(b,c) o swap(a,b))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, swap_def, o_THM] THEN
  DISCH_TAC THEN GEN_TAC THEN
  MAP_EVERY Q.ASM_CASES_TAC [`x: 'a = a`, `x: 'a = b`, `x: 'a = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[]
QED

Theorem SWAP_COMMON' :
   !a b c:'a. ~(a = b) /\ ~(a = c)
             ==> (swap(a,c) o swap(b,c) = swap(b,c) o swap(a,b))
Proof
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [SWAP_SYM] THEN
  ASM_SIMP_TAC std_ss[GSYM SWAP_COMMON] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) empty_rewrites [SWAP_SYM] THEN
  REFL_TAC
QED

Theorem SWAP_INDEPENDENT :
   !a b c d:'a. ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d)
               ==> (swap(a,b) o swap(c,d) = swap(c,d) o swap(a,b))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, swap_def, o_THM]  THEN
  DISCH_TAC THEN GEN_TAC THEN
  MAP_EVERY Q.ASM_CASES_TAC [`x: 'a = a`, `x: 'a = b`, `x: 'a = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Permutations as transposition sequences.                                  *)
(* ------------------------------------------------------------------------- *)

Inductive swapseq :
   (swapseq 0 I) /\
   (!a b p n. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (swap(a,b) o p))
End

Definition permutation :
   permutation p = ?n. swapseq n p
End

(* ------------------------------------------------------------------------- *)
(* Some closure properties of the set of permutations, with lengths.         *)
(* ------------------------------------------------------------------------- *)

Theorem SWAPSEQ_I = CONJUNCT1 swapseq_rules

Theorem PERMUTATION_I :
   permutation I
Proof
  REWRITE_TAC[permutation] THEN PROVE_TAC[SWAPSEQ_I]
QED

Theorem SWAPSEQ_SWAP :
   !a b. swapseq (if a = b then 0 else 1) (swap(a,b))
Proof
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ONE] THEN
  PROVE_TAC[swapseq_rules, I_o_ID, SWAPSEQ_I, SWAP_REFL]
QED

Theorem PERMUTATION_SWAP :
   !a b. permutation (swap(a,b))
Proof
  REWRITE_TAC[permutation] THEN PROVE_TAC[SWAPSEQ_SWAP]
QED

Theorem SWAPSEQ_COMPOSE :
   !n p m q. swapseq n p /\ swapseq m q ==> swapseq (n + m) (p o q)
Proof
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM, GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC swapseq_ind THEN
  REWRITE_TAC[ADD_CLAUSES, I_o_ID, GSYM o_ASSOC] THEN
  PROVE_TAC[swapseq_rules]
QED

Theorem PERMUTATION_COMPOSE :
   !p q. permutation p /\ permutation q ==> permutation (p o q)
Proof
  REWRITE_TAC[permutation] THEN PROVE_TAC[SWAPSEQ_COMPOSE]
QED

Theorem SWAPSEQ_ENDSWAP :
   !n p a b:'a. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (p o swap(a,b))
Proof
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM, GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC swapseq_ind THEN REWRITE_TAC[I_o_ID, GSYM o_ASSOC] THEN
  PROVE_TAC[o_ASSOC, swapseq_rules, I_o_ID]
QED

Theorem SWAPSEQ_INVERSE_EXISTS :
   !n p:'a->'a. swapseq n p ==> ?q. swapseq n q /\ (p o q = I) /\ (q o p = I)
Proof
  HO_MATCH_MP_TAC swapseq_ind THEN CONJ_TAC THENL
   [PROVE_TAC[I_o_ID, swapseq_rules], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`n:num`, `q:'a->'a`, `a:'a`, `b:'a`] SWAPSEQ_ENDSWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  Q.EXISTS_TAC `(q:'a->'a) o swap(a,b)` THEN
  ASM_REWRITE_TAC[GSYM o_ASSOC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV)
                  empty_rewrites [o_ASSOC] THEN
  ASM_REWRITE_TAC[SWAP_IDEMPOTENT, I_o_ID]
QED

Theorem SWAPSEQ_INVERSE :
   !n p. swapseq n p ==> swapseq n (inverse p)
Proof
  PROVE_TAC[SWAPSEQ_INVERSE_EXISTS, INVERSE_UNIQUE_o]
QED

Theorem PERMUTATION_INVERSE :
   !p. permutation p ==> permutation (inverse p)
Proof
  REWRITE_TAC[permutation] THEN PROVE_TAC[SWAPSEQ_INVERSE]
QED

(* ------------------------------------------------------------------------- *)
(* The identity map only has even transposition sequences.                   *)
(* ------------------------------------------------------------------------- *)

Theorem SYMMETRY_LEMMA[local] :
  (!a b c d:'a. P a b c d ==> P a b d c) /\
  (!a b c d.
     ~(a = b) /\ ~(c = d) /\
     ((a = c) /\ (b = d) \/ (a = c) /\ ~(b = d) \/ ~(a = c) /\ (b = d) \/
      ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d))
     ==> P a b c d)
  ==> (!a b c d. ~(a = b) /\ ~(c = d) ==> P a b c d)
Proof
  REPEAT STRIP_TAC THEN MAP_EVERY Q.ASM_CASES_TAC
   [`a:'a = c`, `a:'a = d`, `b:'a = c`, `b:'a = d`] THEN
  PROVE_TAC[]
QED

Theorem SWAP_GENERAL :
   !a b c d:'a.
        ~(a = b) /\ ~(c = d)
        ==> (swap(a,b) o swap(c,d) = I) \/
            ?x y z. ~(x = a) /\ ~(y = a) /\ ~(z = a) /\ ~(x = y) /\
                    (swap(a,b) o swap(c,d) = swap(x,y) o swap(a,z))
Proof
  HO_MATCH_MP_TAC SYMMETRY_LEMMA THEN CONJ_TAC THENL
   [SIMP_TAC std_ss[SWAP_SYM], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [PROVE_TAC[SWAP_IDEMPOTENT],
    DISJ2_TAC THEN qexistsl_tac [`b:'a`, `d:'a`, `b:'a`] THEN
    PROVE_TAC[SWAP_COMMON],
    DISJ2_TAC THEN qexistsl_tac [`c:'a`, `d:'a`, `c:'a`] THEN
    PROVE_TAC[SWAP_COMMON'],
    DISJ2_TAC THEN qexistsl_tac [`c:'a`, `d:'a`, `b:'a`] THEN
  PROVE_TAC[SWAP_INDEPENDENT]]
QED

Theorem FIXING_SWAPSEQ_DECREASE :
   !n p a b:'a.
      swapseq n p /\ ~(a = b) /\ ((swap(a,b) o p) a = a)
      ==> ~(n = 0) /\ swapseq (n - 1) (swap(a,b) o p)
Proof
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [swapseq_cases] THEN
  REWRITE_TAC[SUC_NOT, GSYM SUC_NOT] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[I_THM, o_THM, swap_def] THEN PROVE_TAC[],
    ALL_TAC] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
  qx_genl_tac [`c:'a`, `d:'a`, `q:'a->'a`, `m:num`] THEN
  REWRITE_TAC[ADD1,EQ_ADD_RCANCEL, GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[o_ASSOC] THEN STRIP_TAC THEN
  MP_TAC(Q.SPECL [`a:'a`, `b:'a`, `c:'a`, `d:'a`] SWAP_GENERAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[I_o_ID, ADD_SUB] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  qx_genl_tac [`x:'a`, `y:'a`, `z:'a`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o Q.SPECL
   [`q:'a->'a`, `a:'a`, `z:'a`]) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    empty_rewrites [EQ_SYM_EQ] THEN ASM_REWRITE_TAC[] THEN
    Q.PAT_X_ASSUM `$= X Y` MP_TAC THEN
    REWRITE_TAC[GSYM o_ASSOC] THEN
    Q.ABBREV_TAC `r:'a->'a = swap(a:'a,z) o q` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM, o_THM, swap_def] THEN PROVE_TAC[],
    qid_spec_tac `n:num` THEN INDUCT_TAC THEN
    REWRITE_TAC[SUC_NOT, SUC_SUB1, GSYM o_ASSOC] THEN
  PROVE_TAC[swapseq_rules]]
QED

Theorem SWAPSEQ_IDENTITY_EVEN :
   !n. swapseq n (I:'a->'a) ==> EVEN n
Proof
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN Q.X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [swapseq_cases] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o CONJUNCT1) MP_TAC) THEN
  REWRITE_TAC[EVEN] THEN SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  qx_genl_tac [`a:'a`, `b:'a`, `p:'a->'a`, `m:num`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(Q.SPECL [`m:num`, `p:'a->'a`, `a:'a`, `b:'a`]
    FIXING_SWAPSEQ_DECREASE) THEN
  GEN_REWRITE_TAC
    (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    empty_rewrites [EQ_SYM_EQ] THEN ASM_REWRITE_TAC[I_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``(m - 1):num``) THEN
  Q.UNDISCH_THEN `SUC m = n` (SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[DECIDE ``m - 1 < SUC m``] THEN Q.UNDISCH_TAC `~(m = 0)` THEN
  qid_spec_tac `m:num` THEN INDUCT_TAC THEN
  REWRITE_TAC[SUC_SUB1, EVEN]
QED

(* ------------------------------------------------------------------------- *)
(* Therefore we have a welldefined notion of parity.                         *)
(* ------------------------------------------------------------------------- *)

Definition evenperm :
   evenperm p = EVEN(@n. swapseq n p)
End

Theorem SWAPSEQ_EVEN_EVEN :
   !m n p:'a->'a. swapseq m p /\ swapseq n p ==> (EVEN m <=> EVEN n)
Proof
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``swapseq (n + m) :('a->'a)->bool``) THEN
  ASM_SIMP_TAC bool_ss[SWAPSEQ_COMPOSE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SWAPSEQ_IDENTITY_EVEN) THEN
  SIMP_TAC bool_ss[EVEN_ADD]
QED

Theorem EVENPERM_UNIQUE :
   !n p b. swapseq n p /\ (EVEN n = b) ==> (evenperm p = b)
Proof
  REWRITE_TAC[evenperm] THEN METIS_TAC[SWAPSEQ_EVEN_EVEN]
QED

(* ------------------------------------------------------------------------- *)
(* And it has the expected composition properties.                           *)
(* ------------------------------------------------------------------------- *)

Theorem EVENPERM_I :
   evenperm I = T
Proof
  MATCH_MP_TAC EVENPERM_UNIQUE THEN PROVE_TAC[swapseq_rules, EVEN]
QED

Theorem EVENPERM_SWAP :
   !a b:'a. evenperm (swap(a,b)) <=> (a = b)
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC EVENPERM_UNIQUE THEN
  METIS_TAC[SWAPSEQ_SWAP, EVEN, num_CONV ``1:num``]
QED

Theorem EVENPERM_COMPOSE :
   !p q. permutation p /\ permutation q
         ==> (evenperm (p o q) = (evenperm p = evenperm q))
Proof
  REWRITE_TAC[permutation] THEN
  SIMP_TAC bool_ss[GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN
               ASSUME_TAC(MATCH_MP SWAPSEQ_COMPOSE th)) THEN
  METIS_TAC[EVENPERM_UNIQUE, SWAPSEQ_COMPOSE, EVEN_ADD]
QED

Theorem EVENPERM_INVERSE :
   !p. permutation p ==> (evenperm (inverse p) = evenperm p)
Proof
  REWRITE_TAC[permutation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EVENPERM_UNIQUE THEN
  METIS_TAC[SWAPSEQ_INVERSE, EVENPERM_UNIQUE]
QED

(* ------------------------------------------------------------------------- *)
(* A more abstract characterization of permutations.                         *)
(* ------------------------------------------------------------------------- *)

(* cf. pred_setTheory.BIJ_ALT *)
Theorem PERMUTATION_BIJECTIVE :
   !p. permutation p ==> !y. ?!x. p(x) = y
Proof
  REWRITE_TAC[permutation] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  SIMP_TAC bool_ss[FUN_EQ_THM, I_THM, o_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  METIS_TAC[]
QED

Theorem PERMUTATION_FINITE_SUPPORT :
   !p. permutation p ==> FINITE {x:'a| ~(p x = x)}
Proof
  SIMP_TAC bool_ss[permutation, GSYM LEFT_FORALL_IMP_THM] THEN
  CONV_TAC SWAP_VARS_CONV THEN HO_MATCH_MP_TAC swapseq_ind THEN
  REWRITE_TAC[I_THM, FINITE_RULES,
              Q.prove (`{x | F} = {}`,REWRITE_TAC[EXTENSION] THEN
              CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
              REWRITE_TAC[NOT_IN_EMPTY])] THEN
  qx_genl_tac [`a:'a`, `b:'a`, `p:'a->'a`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_FINITE_I THEN
  Q.EXISTS_TAC `(a:'a) INSERT b INSERT {x | ~(p x = x)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT, SUBSET_DEF, IN_INSERT] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[o_THM, swap_def] THEN PROVE_TAC[]
QED

Theorem PERMUTATION_LEMMA :
   !s p:'a->'a.
       FINITE s /\
       (!y. ?!x. p(x) = y) /\ (!x. ~(x IN s) ==> (p x = x))
       ==> permutation p
Proof
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    Q.SUBGOAL_THEN `p:'a->'a = I` (fn th => REWRITE_TAC[th, PERMUTATION_I]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM, I_THM],
    ALL_TAC] THEN
  Q.X_GEN_TAC `s:'a->bool` THEN STRIP_TAC THEN Q.X_GEN_TAC `a:'a` THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `permutation ((swap(a,p(a)) o swap(a,p(a))) o (p:'a->'a))`
  MP_TAC THENL [ALL_TAC, REWRITE_TAC[SWAP_IDEMPOTENT, I_o_ID]] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN MATCH_MP_TAC PERMUTATION_COMPOSE THEN
  REWRITE_TAC[PERMUTATION_SWAP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [Q.UNDISCH_TAC `!y. ?!x. (p:'a->'a) x = y` THEN
    SIMP_TAC bool_ss[EXISTS_UNIQUE_THM, swap_def, o_THM] THEN
    Q.ASM_CASES_TAC `(p:'a->'a) a = a` THEN ASM_REWRITE_TAC[] THENL
     [PROVE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[Q.prove(
     ‘((if p then x else y) = a) <=> if p then x = a else y = a’,
     PROVE_TAC[])] THEN
    REWRITE_TAC[TAUT `(if p then x else y) <=> p /\ x \/ ~p /\ y`] THEN
    PROVE_TAC[],
    REWRITE_TAC[swap_def, o_THM] THEN
    Q.ASM_CASES_TAC `(p:'a->'a) a = a` THEN ASM_REWRITE_TAC[] THEN
    PROVE_TAC[]]
QED

Theorem PERMUTATION :
   !p. permutation p <=> (!y. ?!x. p(x) = y) /\ FINITE {x:'a| ~(p(x) = x)}
Proof
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC bool_ss[PERMUTATION_BIJECTIVE, PERMUTATION_FINITE_SUPPORT] THEN
  STRIP_TAC THEN MATCH_MP_TAC PERMUTATION_LEMMA THEN
  Q.EXISTS_TAC `{x:'a| ~(p x = x)}` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  ASM_REWRITE_TAC[]
QED

Theorem PERMUTATION_INVERSE_WORKS :
   !p. permutation p ==> (inverse p o p = I) /\ (p o inverse p = I)
Proof
  PROVE_TAC[PERMUTATION_BIJECTIVE, SURJECTIVE_INVERSE_o,
            INJECTIVE_INVERSE_o]
QED

Theorem PERMUTATION_INVERSE_COMPOSE :
   !p q. permutation p /\ permutation q
         ==> (inverse (p o q) = inverse q o inverse p)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTATION_INVERSE_WORKS)) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [o_ASSOC] THEN
  ASM_REWRITE_TAC[I_o_ID]
QED

val IMP_CONJ = CONJ_EQ_IMP;

Theorem PERMUTATION_COMPOSE_EQ :
   (!p q:'a->'a. permutation(p) ==> (permutation(p o q) <=> permutation q)) /\
   (!p q:'a->'a. permutation(q) ==> (permutation(p o q) <=> permutation p))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERMUTATION_INVERSE) THEN
  EQ_TAC THEN ASM_SIMP_TAC std_ss [PERMUTATION_COMPOSE] THENL
   [DISCH_THEN(MP_TAC o Q.SPEC `inverse(p:'a->'a)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] PERMUTATION_COMPOSE)),
    DISCH_THEN(MP_TAC o Q.SPEC `inverse(q:'a->'a)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] PERMUTATION_COMPOSE))] THEN
  ASM_SIMP_TAC std_ss [GSYM o_ASSOC, PERMUTATION_INVERSE_WORKS] THEN
  ASM_SIMP_TAC bool_ss [o_ASSOC, PERMUTATION_INVERSE_WORKS] THEN
  REWRITE_TAC[I_o_ID]
QED

Theorem PERMUTATION_COMPOSE_SWAP :
   (!p a b:'a. permutation(swap(a,b) o p) <=> permutation p) /\
   (!p a b:'a. permutation(p o swap(a,b)) <=> permutation p)
Proof
  SIMP_TAC bool_ss [PERMUTATION_COMPOSE_EQ, PERMUTATION_SWAP]
QED

(* ------------------------------------------------------------------------- *)
(* Relation to "permutes".                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTATION_PERMUTES :
   !p:'a->'a. permutation p <=> ?s. FINITE s /\ p permutes s
Proof
  GEN_TAC THEN REWRITE_TAC[PERMUTATION, permutes] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [Q.EXISTS_TAC `{x:'a | ~(p x = x)}` THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC SUBSET_FINITE_I THEN Q.EXISTS_TAC `s:'a->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DEF] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]]
QED

(* ------------------------------------------------------------------------- *)
(* Hence a sort of induction principle composing by swaps.                   *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTES_INDUCT :
   !P s. FINITE s /\
         P I /\
         (!a b:'a p. a IN s /\ b IN s /\ P p /\ permutation p
                    ==> P (swap(a,b) o p))
         ==> (!p. p permutes s ==> P p)
Proof
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a ==> c ==> d`] THEN
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_REWRITE_TAC[PERMUTES_EMPTY, IN_INSERT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  Q.SUBGOAL_THEN `p = swap(e,p e) o swap(e,p e) o (p:'a->'a)` SUBST1_TAC THENL
   [REWRITE_TAC[o_ASSOC, SWAP_IDEMPOTENT, I_o_ID], ALL_TAC] THEN
  Q.PAT_X_ASSUM `$==> X Y` MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN
  DISCH_THEN(fn th => FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_INSERT_LEMMA,
                PERMUTATION_PERMUTES, FINITE_INSERT, PERMUTATION_COMPOSE,
                PERMUTATION_SWAP]
QED

(* ------------------------------------------------------------------------- *)
(* More lemmas about permutations.                                           *)
(* ------------------------------------------------------------------------- *)

Theorem PERMUTES_NUMSET_LE :
   !p s:num->bool. p permutes s /\ (!i. i IN s ==> p(i) <= i) ==> (p = I)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, I_THM] THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN Q.X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN
  Q.ASM_CASES_TAC `(n:num) IN s` THENL [ALL_TAC, PROVE_TAC[permutes]] THEN
  ASM_SIMP_TAC bool_ss[EQ_LESS_EQ] THEN REWRITE_TAC[GSYM NOT_LESS] THEN
  PROVE_TAC[PERMUTES_INJECTIVE, LESS_EQ_REFL,NOT_LESS]
QED

Theorem PERMUTES_NUMSET_GE :
   !p s:num->bool. p permutes s /\ (!i. i IN s ==> i <= p(i)) ==> (p = I)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`inverse(p:num->num)`, `s:num->bool`] PERMUTES_NUMSET_LE) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [PROVE_TAC[PERMUTES_INVERSE, PERMUTES_INVERSES, PERMUTES_IN_IMAGE],
    PROVE_TAC[PERMUTES_INVERSE_INVERSE, INVERSE_I]]
QED

Theorem IMAGE_INVERSE_PERMUTATIONS :
   !s:'a->bool. {inverse p | p permutes s} = {p | p permutes s}
Proof
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[PERMUTES_INVERSE_INVERSE, PERMUTES_INVERSE]
QED

Theorem IMAGE_COMPOSE_PERMUTATIONS_L :
   !s q:'a->'a. q permutes s ==> ({q o p | p permutes s} = {p | p permutes s})
Proof
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q.X_GEN_TAC `p:'a->'a` THEN EQ_TAC THENL
   [PROVE_TAC[PERMUTES_COMPOSE],
    DISCH_TAC THEN Q.EXISTS_TAC `inverse (q:'a->'a) o (p:'a->'a)` THEN
    ASM_SIMP_TAC bool_ss[o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
    PROVE_TAC [PERMUTES_INVERSES_o, I_o_ID]]
QED

Theorem IMAGE_COMPOSE_PERMUTATIONS_R :
   !s q:'a->'a. q permutes s ==> ({p o q | p permutes s} = {p | p permutes s})
Proof
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q.X_GEN_TAC `p:'a->'a` THEN EQ_TAC THENL
   [PROVE_TAC[PERMUTES_COMPOSE],
    DISCH_TAC THEN Q.EXISTS_TAC `(p:'a->'a) o inverse (q:'a->'a)` THEN
    ASM_SIMP_TAC bool_ss[GSYM o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
    PROVE_TAC [PERMUTES_INVERSES_o, I_o_ID]]
QED

Theorem PERMUTES_IN_COUNT :
   !p n i. p permutes count n /\ i IN count n ==> p(i) < n
Proof
  REWRITE_TAC[permutes, IN_COUNT] THEN PROVE_TAC[]
QED

val _ = export_theory ();
