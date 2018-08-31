(* ==================================================================   
TITLE: Developing the theory of permutation
 It is translated from the corresponding code file of Harrision in Hol-Light.   
AUTHORS  : (Copyright) Liming Li
             Beijing Engineering Research Center of High Reliable      
             Emmbedded System, Capital Normal University, China   
DATE  : 2011.04.23   

 ================================================================== *)
(*
set_trace "Unicode" 0;
*)
app load ["fcpTheory","fcpLib","realTheory","realLib"];
open arithmeticTheory combinTheory pred_setTheory pairTheory boolTheory
	 PairedLambda pred_setLib fcpTheory fcpLib Q tautLib numLib realTheory
	 realLib InductiveDefinition;
	 

(* ========================================================================= *)
(* From fcpTheory                                                            *)
(* ========================================================================= *)

val CARD_CLAUSES = CONJ CARD_EMPTY (PROVE [CARD_INSERT]
  ``!x s. FINITE s ==>
           (CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))``);
val IMAGE_CLAUSES = CONJ IMAGE_EMPTY IMAGE_INSERT;
val FINITE_RULES = CONJ FINITE_EMPTY FINITE_INSERT;
val NOT_SUC = numTheory.NOT_SUC;
val SUC_INJ = prim_recTheory.INV_SUC_EQ;
val LT = CONJ (DECIDE ``!m:num. ~(m < 0)``) prim_recTheory.LESS_THM;
val LT_REFL = prim_recTheory.LESS_REFL;


val CARD_IMAGE_INJ = prove(
  `!(f:'a->'b) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[DECIDE ``a /\ b ==> c = b ==> a ==> c``] THEN
  SPEC_THEN `\s. (!x y. (f x = f y) ==> y IN s ==> x IN s ==> (x = y)) ==>
      (CARD (IMAGE f s) = CARD s)` (MATCH_MP_TAC o BETA_RULE) FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY, IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [CARD_CLAUSES, IMAGE_FINITE, IN_IMAGE] THEN
  COND_CASES_TAC THEN PROVE_TAC[IN_INSERT]);

val HAS_SIZE_IMAGE_INJ = prove(
  `!(f:'a->'b) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ (s HAS_SIZE n)
        ==> ((IMAGE f s) HAS_SIZE n)`,
  SIMP_TAC std_ss [HAS_SIZE_def, IMAGE_FINITE] THEN PROVE_TAC[CARD_IMAGE_INJ]);

(* ========================================================================= *)
(* Permutations, both general and specifically on finite sets.               *)
(* ========================================================================= *)

val PERMUTES_DEF = new_infixr_definition
    ("PERMUTES_DEF ", `PERMUTES p s = (!x. ~(x IN s) ==> (p(x) = x)) /\ (!y. ?!x. p x = y)`,490);

(* ------------------------------------------------------------------------- *)
(* Inverse function (on whole universe).                                     *)
(* ------------------------------------------------------------------------- *)

val INVERSE_DEF = Define `INVERSE(f) = \y. @x. f x = y`;

val SURJECTIVE_INVERSE = store_thm(
  "SURJECTIVE_INVERSE",
  `!f. (!y. ?x. f x = y) = !y. f(INVERSE f y) = y`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL[
REWRITE_TAC[INVERSE_DEF] THEN 
CONV_TAC (ONCE_DEPTH_CONV Thm.BETA_CONV) THEN CONV_TAC SELECT_CONV,
EXISTS_TAC(`INVERSE f y`)] THEN PROVE_TAC[]);

val SURJECTIVE_INVERSE_o = store_thm(
  " SURJECTIVE_INVERSE_o",
  `!f. (!y. ?x. f x = y) <=> (f o INVERSE f = I)`,
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM, SURJECTIVE_INVERSE]);

val INJECTIVE_INVERSE = store_thm(
  "INJECTIVE_INVERSE",
  `!f. (!x x'. (f x = f x') ==> (x = x')) = (!x. INVERSE f (f x) = x)`,
  GEN_TAC THEN EQ_TAC THENL[
REPEAT STRIP_TAC THEN
REWRITE_TAC[INVERSE_DEF] THEN 
CONV_TAC (ONCE_DEPTH_CONV Thm.BETA_CONV) THEN FIRST_ASSUM MATCH_MP_TAC THEN
CONV_TAC SELECT_CONV THEN EXISTS_TAC(`x`) THEN REFL_TAC,
PROVE_TAC[]]);

val INJECTIVE_INVERSE_o = store_thm(
  "INJECTIVE_INVERSE_o",
  `!f. (!x x'. (f x = f x') ==> (x = x')) = (INVERSE f o f = I)`,
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM, INJECTIVE_INVERSE]);

val INVERSE_UNIQUE_o = store_thm(
  "INVERSE_UNIQUE_o",
  `!f g. (f o g = I) /\ (g o f = I) ==> (INVERSE f = g)`,
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM] THEN
  PROVE_TAC[INJECTIVE_INVERSE, SURJECTIVE_INVERSE]);

val INVERSE_I = store_thm(
  "INVERSE_I",
  `INVERSE I = I`,
  MATCH_MP_TAC INVERSE_UNIQUE_o THEN REWRITE_TAC[I_o_ID]);

(* ------------------------------------------------------------------------- *)
(* Transpositions.                                                           *)
(* ------------------------------------------------------------------------- *)

val SWAP_DEF = new_definition("SWAP_DEF",
  `SWAP(i,j) k = if k = i then j else if k = j then i else k`);

val SWAP_REFL = store_thm(
  "SWAP_REFL",
  `!a. SWAP(a,a) = I`,
  REWRITE_TAC[FUN_EQ_THM, SWAP_DEF, I_THM] THEN PROVE_TAC[]);

val SWAP_SYM = store_thm(
  "SWAP_SYM",
  `!a b. SWAP(a,b) = SWAP(b,a)`,
  REWRITE_TAC[FUN_EQ_THM, SWAP_DEF, I_THM] THEN PROVE_TAC[]);

val SWAP_IDEMPOTENT = store_thm(
  "SWAP_IDEMPOTENT",
  `!a b. SWAP(a,b) o SWAP(a,b) = I`,
  REWRITE_TAC[FUN_EQ_THM, SWAP_DEF, o_THM, I_THM] THEN PROVE_TAC[]);

val INVERSE_SWAP = store_thm(
  "INVERSE_SWAP",
  `!a b. INVERSE(SWAP(a,b)) = SWAP(a,b)`,
REPEAT GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[SWAP_IDEMPOTENT]);

val SWAP_GALOIS = store_thm(
  "SWAP_GALOIS",
  `!a b x y. (x = SWAP(a,b) y) = (y = SWAP(a,b) x)`,
REWRITE_TAC[SWAP_DEF] THEN PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Basic consequences of the definition.                                     *)
(* ------------------------------------------------------------------------- *)

val PERMUTES_IN_IMAGE = store_thm(
  "PERMUTES_IN_IMAGE",
  `!p s x. p PERMUTES s ==> (p(x) IN s = x IN s)`,
  REWRITE_TAC[PERMUTES_DEF] THEN PROVE_TAC[]);

val PERMUTES_IMAGE = store_thm(
  "PERMUTES_IMAGE",
  `!p s. p PERMUTES s ==> (IMAGE p s = s)`,
REWRITE_TAC[PERMUTES_DEF, EXTENSION, IN_IMAGE] THEN PROVE_TAC[]);

val PERMUTES_INJECTIVE = store_thm(
  "PERMUTES_INJECTIVE",
  `!p s. p PERMUTES s ==> !x y. (p(x) = p(y)) = (x = y)`,
REWRITE_TAC[PERMUTES_DEF] THEN PROVE_TAC[]);

val PERMUTES_SURJECTIVE = store_thm(
  "PERMUTES_SURJECTIVE",
  `!p s. p PERMUTES s ==> !y. ?x. p(x) = y`,
REWRITE_TAC[PERMUTES_DEF] THEN PROVE_TAC[]);

val PERMUTES_INVERSES_o = store_thm(
  "PERMUTES_INVERSES_o",
  `!p s. p PERMUTES s ==> (p o INVERSE(p) = I) /\ (INVERSE(p) o p = I)`,
  REWRITE_TAC[GSYM INJECTIVE_INVERSE_o, GSYM SURJECTIVE_INVERSE_o] THEN
  REWRITE_TAC[PERMUTES_DEF] THEN PROVE_TAC[]);

val PERMUTES_INVERSES = store_thm(
  " PERMUTES_INVERSES",
  `!p s. p PERMUTES s
         ==> (!x. p(INVERSE p x) = x) /\ (!x. INVERSE p (p x) = x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM]);

val PERMUTES_SUBSET = store_thm(
  "PERMUTES_SUBSET",
  `!p s t. p PERMUTES s /\ s SUBSET t ==> p PERMUTES t`,
  REWRITE_TAC[PERMUTES_DEF, SUBSET_DEF] THEN PROVE_TAC[]);

val PERMUTES_EMPTY = store_thm(
  "PERMUTES_EMPTY",
  `!p. p PERMUTES {} = (p = I)`,
  REWRITE_TAC[FUN_EQ_THM, I_THM, PERMUTES_DEF, NOT_IN_EMPTY] THEN PROVE_TAC[]);

val PERMUTES_SING = store_thm(
  "PERMUTES_SING",
  `!p a.  p PERMUTES {a} = (p = I)`,
  REWRITE_TAC[FUN_EQ_THM, I_THM, PERMUTES_DEF, IN_SING] THEN PROVE_TAC[]);

val PERMUTES_UNIV = store_thm(
  "PERMUTES_UNIV",
  `!p. p PERMUTES UNIV = !y. ?!x. p x = y`,
  REWRITE_TAC[PERMUTES_DEF, IN_UNIV]);

val PERMUTES_INVERSE_EQ = store_thm(
  "PERMUTES_INVERSE_EQ",
  `!p. p PERMUTES s ==> !x y. (INVERSE p y = x) = (p x = y)`,
  REWRITE_TAC[PERMUTES_DEF, INVERSE_DEF] THEN METIS_TAC[]);

val PERMUTES_SWAP = store_thm(
  "PERMUTES_SWAP",
  `!a b s. a IN s /\ b IN s ==> SWAP(a,b) PERMUTES s`,
  REWRITE_TAC[PERMUTES_DEF, SWAP_DEF] THEN METIS_TAC[]);

val PERMUTES_SUPERSET = store_thm(
  "PERMUTES_SUPERSET",
  `!p s t. p PERMUTES s /\ (!x. x IN (s DIFF t) ==> (p(x) = x))
           ==> p PERMUTES t`,
  REWRITE_TAC[PERMUTES_DEF, IN_DIFF] THEN PROVE_TAC[]);


(* ------------------------------------------------------------------------- *)
(* Group properties.                                                         *)
(* ------------------------------------------------------------------------- *)


val PERMUTES_I = store_thm(
  "PERMUTES_I",
  `!s. I PERMUTES s`,
  REWRITE_TAC[PERMUTES_DEF, I_THM] THEN PROVE_TAC[]);

val PERMUTES_COMPOSE = store_thm(
  "PERMUTES_COMPOSE",
  `!p q s x. p PERMUTES s /\ q PERMUTES s ==> (q o p) PERMUTES s`,
  REWRITE_TAC[PERMUTES_DEF, o_THM] THEN PROVE_TAC[]);

val PERMUTES_INVERSE = store_thm(
  "PERMUTES_INVERSE",
  `!p s. p PERMUTES s ==> INVERSE (p) PERMUTES s`,
  REPEAT STRIP_TAC THEN
 FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[PERMUTES_DEF] THEN PROVE_TAC[]);

val PERMUTES_INVERSE_INVERSE = store_thm(
  "PERMUTES_INVERSE_INVERSE",
  `!p s. p PERMUTES s ==> (INVERSE (INVERSE (p)) = p)`,
  REWRITE_TAC [FUN_EQ_THM] THEN
 PROVE_TAC[PERMUTES_INVERSE_EQ, PERMUTES_INVERSE]);

(* ------------------------------------------------------------------------- *)
(* The number of permutations on a finite set.                               *)
(* ------------------------------------------------------------------------- *)

val PERMUTES_INSERT_LEMMA = store_thm(
  "PERMUTES_INSERT_LEMMA",
  `!p a s. p PERMUTES (a INSERT s) ==> (SWAP(a,p(a)) o p) PERMUTES s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
  EXISTS_TAC `a INSERT s` THEN CONJ_TAC THEN
  METIS_TAC[PERMUTES_SWAP, PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_COMPOSE, 
o_THM, SWAP_DEF, IN_DIFF]);

val PERMUTES_INSERT = store_thm(
  "PERMUTES_INSERT",
  `{p | p PERMUTES (a INSERT s)} =
        IMAGE (\(b,p). SWAP(a,b) o p)
              {(b,p) | b IN a INSERT s /\ p IN {p | p PERMUTES s}}`,
  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN  X_GEN_TAC `p: 'a -> 'a` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC std_ss[EXISTS_PROD]THEN EQ_TAC THENL
   [DISCH_TAC THEN 
    MAP_EVERY EXISTS_TAC [`(p: 'a -> 'a) a`, `SWAP(a,p a) o (p: 'a -> 'a)`]  THEN 
    ASM_REWRITE_TAC[SWAP_IDEMPOTENT, o_ASSOC, I_o_ID] THEN
    PROVE_TAC[PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_INSERT_LEMMA],
    SIMP_TAC std_ss[GSYM LEFT_FORALL_IMP_THM] THEN
    MAP_EVERY X_GEN_TAC [`b: 'a `, `q: 'a -> 'a `] THEN
    STRIP_TAC THEN MATCH_MP_TAC PERMUTES_COMPOSE THEN
    PROVE_TAC[PERMUTES_SUBSET, SUBSET_DEF, IN_INSERT, PERMUTES_SWAP]]);

val HAS_SIZE_PERMUTATIONS = store_thm(
  "HAS_SIZE_PERMUTATIONS",
  `!s:'a ->bool n: num. (s HAS_SIZE n) ==> ({p | p PERMUTES s} HAS_SIZE (FACT n))`,
  SIMP_TAC std_ss[HAS_SIZE_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  SET_INDUCT_TAC THEN
  SIMP_TAC std_ss[PERMUTES_EMPTY, CARD_CLAUSES,GSPEC_EQ, FINITE_SING, CARD_SING, FACT] THEN REWRITE_TAC[GSYM HAS_SIZE_def, PERMUTES_INSERT] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [SIMP_TAC std_ss[FORALL_PROD] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`b: 'a`, `q: 'a -> 'a`, `c: 'a`, `r: 'a -> 'a`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `c: 'a = b` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C AP_THM `e: 'a`) THEN REWRITE_TAC[o_THM, SWAP_DEF] THEN
      SUBGOAL_THEN `((q: 'a -> 'a) e = e) /\ ((r: 'a -> 'a) e = e)` (fn th => SIMP_TAC std_ss[th]) THEN
      PROVE_TAC[PERMUTES_DEF],
      FIRST_X_ASSUM(MP_TAC o AP_TERM `(\q:'a -> 'a. SWAP(e:'a,b) o q)`) THEN
      BETA_TAC THEN REWRITE_TAC[SWAP_IDEMPOTENT, o_ASSOC, I_o_ID]],
   `{(b,p) | b IN e INSERT s /\ p IN {p | p PERMUTES s}} = (e INSERT s) CROSS {p | p PERMUTES s}` by REWRITE_TAC[EXTENSION, CROSS_DEF] THENL[ 
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
    SIMP_TAC std_ss[FORALL_PROD],
    ASM_SIMP_TAC std_ss[HAS_SIZE_def, FINITE_INSERT, CARD_CLAUSES, FINITE_CROSS, CARD_CROSS,FACT]]]);

val FINITE_PERMUTATIONS = store_thm(
  "FINITE_PERMUTATIONS",
  `!s. FINITE s ==> FINITE {p | p PERMUTES s}`,
  METIS_TAC[HAS_SIZE_PERMUTATIONS, HAS_SIZE_def]);

val CARD_PERMUTATIONS = store_thm
  ("CARD_PERMUTATIONS",
  `!s. FINITE s ==> (CARD {p | p PERMUTES s} = FACT(CARD s))`,
  METIS_TAC[HAS_SIZE_def ,HAS_SIZE_PERMUTATIONS]);

(* ------------------------------------------------------------------------- *)
(* Alternative characterizations of finite set.  (Be included in pred_set)      *)
(* ------------------------------------------------------------------------- *)
val FINITE_IMAGE_CARD = store_thm
  ("FINITE_IMAGE_CARD",
   `!f s. FINITE s ==> CARD (IMAGE f s) <= CARD s`,
   GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
   RW_TAC std_ss[INJ_DEF, CARD_INSERT, NOT_IN_EMPTY, SUBSET_DEF, IN_IMAGE,
                 IMAGE_EMPTY, CARD_EMPTY, IN_INSERT, IMAGE_INSERT,
                 IMAGE_FINITE] THEN
   RW_TAC arith_ss []);

val SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!s t f: 'a -> 'b.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) =
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x:'a = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD t <= CARD (IMAGE (f:'a -> 'b) (s DELETE y))` MP_TAC THENL
     [MATCH_MP_TAC (SIMP_RULE std_ss[GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] CARD_SUBSET) THEN
      ASM_SIMP_TAC std_ss[IMAGE_FINITE, FINITE_DELETE] THEN
      REWRITE_TAC[SUBSET_DEF, IN_IMAGE, IN_DELETE] THEN PROVE_TAC[],
      REWRITE_TAC[GSYM NOT_LESS] THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
      EXISTS_TAC `CARD(s DELETE (y:'a))` THEN
      ASM_SIMP_TAC std_ss[FINITE_IMAGE_CARD, FINITE_DELETE, CARD_DELETE] THEN
      PROVE_TAC[NOT_ZERO_LT_ZERO,CARD_EQ_0, MEMBER_NOT_EMPTY]],
    SUBGOAL_THEN `IMAGE (f:'a -> 'b) s = t` MP_TAC THENL
     [PROVE_TAC [IMAGE_FINITE, CARD_IMAGE_INJ, SUBSET_EQ_CARD],
      PROVE_TAC[EXTENSION, IN_IMAGE]]]);

val SURJECTIVE_IFF_INJECTIVE = prove
 (`!s f: 'a -> 'a.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC std_ss[SURJECTIVE_IFF_INJECTIVE_GEN]);

val FORALL_IN_IMAGE = prove
 (`!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`,
  REWRITE_TAC[IN_IMAGE] THEN PROVE_TAC[]);
(* ------------------------------------------------------------------------- *)
(* Alternative characterizations of permutation of finite set.               *)
(* ------------------------------------------------------------------------- *)

val PERMUTES_FINITE_INJECTIVE = prove
 (`!s: 'a->bool p.
        FINITE s
        ==> (p PERMUTES s =
             (!x. ~(x IN s) ==> (p x = x)) /\
             (!x. x IN s ==> p x IN s) /\
             (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y)))`,
  REWRITE_TAC[PERMUTES_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q = r)) ==> (p /\ q = p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `p: 'a -> 'a ` o MATCH_MP
   (REWRITE_RULE[GSYM AND_IMP_INTRO] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_SIMP_TAC std_ss[SUBSET_DEF, FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `y: 'a ` THEN
  ASM_CASES_TAC `(y: 'a) IN s` THEN METIS_TAC[]);

val PERMUTES_FINITE_SURJECTIVE = prove
 (`!s: 'a ->bool p.
        FINITE s
        ==> (p PERMUTES s =
             (!x. ~(x IN s) ==> (p x = x)) /\ (!x. x IN s ==> p x IN s) /\
             (!y. y IN s ==> ?x. x IN s /\ (p x = y)))`,
  REWRITE_TAC[PERMUTES_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q = r)) ==> (p /\ q = p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `p: 'a -> 'a ` o MATCH_MP
   (REWRITE_RULE[GSYM AND_IMP_INTRO] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_SIMP_TAC std_ss[SUBSET_DEF, FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `y: 'a ` THEN
  ASM_CASES_TAC `(y: 'a) IN s` THEN METIS_TAC[]);


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
(* Some characterizations for iterated operations.                            *)
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

val ITERATE_OP = prove
 (`!op. MONOIDAL op
        ==> !f g s. FINITE s
                    ==> (ITERATE op s (\x. op (f x) (g x)) =
                        op (ITERATE op s f) (ITERATE op s g))`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES, MONOIDAL_AC]);

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

val ITERATE_DELTA = prove
 (`!op. MONOIDAL op
        ==> (!f a s. ITERATE op s (\x. if x = a then f(x) else NEUTRAL op) =
                    if a IN s then f(a) else NEUTRAL op)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES] THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC bool_ss[ITERATE_CLAUSES, ITERATE_SING]);

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

(* ------------------------------------------------------------------------- *)
(* NSUM, SUM                                                                *)
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

val PRODUCT_DEF = Define
  `PRODUCT = ITERATE (( * ):real->real->real)`;

val SUM_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (SUM (IMAGE f s) g = SUM s (g o f))`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CLAUSES = prove
 (`(!f. SUM {} f = &0) /\
   (!x f s. FINITE(s)
            ==> (SUM (x INSERT s) f =
                 if x IN s then SUM s f else f(x) + SUM s f))`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC bool_ss[ITERATE_CLAUSES, MONOIDAL_REAL_ADD]);


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

val SUM_SUPERSET = prove
 (`!f:'a->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> (SUM v f = SUM u f)`,
  SIMP_TAC bool_ss[SUM_DEF, GSYM NEUTRAL_REAL_ADD, ITERATE_SUPERSET, MONOIDAL_REAL_ADD]);

val SUM_SING = prove
 (`!f x. SUM {x} f = f(x)`,
  SIMP_TAC bool_ss[SUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, REAL_ADD_RID]);

val SUM_DELTA = prove
 (`!s a. SUM s (\x. if x = a:'a then b else &0) = if a IN s then b else &0`,
  REWRITE_TAC[SUM_DEF, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC bool_ss[ITERATE_DELTA, MONOIDAL_REAL_ADD]);

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

val PRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (PRODUCT (IMAGE f s) g = PRODUCT s (g o f))`,
  REWRITE_TAC[PRODUCT_DEF, GSYM NEUTRAL_REAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);

val PRODUCT_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (PRODUCT s f = PRODUCT s g)`,
  REWRITE_TAC[PRODUCT_DEF] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);

val PRODUCT_CLAUSES = prove
 (`(!f. PRODUCT {} f = &1) /\
   (!x f s. FINITE(s)
            ==> (PRODUCT (x INSERT s) f =
                 if x IN s then PRODUCT s f else f(x) * PRODUCT s f))`,
  REWRITE_TAC[PRODUCT_DEF, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC bool_ss[ITERATE_CLAUSES, MONOIDAL_REAL_MUL]);

val PRODUCT_EQ_0 = prove
 (`!f s. FINITE s ==> ((PRODUCT s f = &0) <=> ?x. x IN s /\ (f(x) = &0))`,
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[PRODUCT_CLAUSES, REAL_ENTIRE, IN_INSERT, NOT_IN_EMPTY, REAL_10] THEN
  PROVE_TAC[]);

val PRODUCT_EQ_0_COUNT = prove
 (`!f n. (PRODUCT (count n) f = &0) <=> ?x. x < n /\ (f(x) = &0)`,
  SIMP_TAC bool_ss[PRODUCT_EQ_0, FINITE_COUNT, IN_COUNT]);

val PRODUCT_EQ_0_NUMSEG = prove
 (`!f m n. (PRODUCT (count n DIFF count m) f = &0) <=> ?x. m <= x /\ x < n /\ (f(x) = &0)`,
  SIMP_TAC bool_ss[PRODUCT_EQ_0, FINITE_COUNT, FINITE_DIFF, IN_NUMSEG, GSYM CONJ_ASSOC]);

val PRODUCT_EQ_1 = prove
 (`!f s. (!x:'a. x IN s ==> (f(x) = &1)) ==> (PRODUCT s f = &1)`,
  REWRITE_TAC[PRODUCT_DEF, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC bool_ss[ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_MUL]);

val PRODUCT_EQ_1_COUNT = prove
 (`!f s. (!i. i < n ==> (f(i) = &1)) ==> (PRODUCT (count n) f = &1)`,
  SIMP_TAC bool_ss[PRODUCT_EQ_1, IN_COUNT]);

val PRODUCT_EQ_1_NUMSEG = prove
 (`!f s.
     (!i. m <= i /\ i < n ==> (f(i) = &1)) ==> 
               (PRODUCT (count n DIFF count m) f = &1)`,
  SIMP_TAC bool_ss[PRODUCT_EQ_1, IN_NUMSEG]);

(* ------------------------------------------------------------------------- *)
(* Permutations of index set for iterated operations.                        *)
(* ------------------------------------------------------------------------- *)

val ITERATE_PERMUTE = prove
 (`!op. MONOIDAL op
        ==> ! f:'a -> 'b p s. p PERMUTES s ==> (ITERATE op s f = ITERATE op s (f o p))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  PROVE_TAC[PERMUTES_DEF]);

val NSUM_PERMUTE = prove
 (`!f p s. p PERMUTES s ==> (NSUM s f = NSUM s (f o p))`,
  REWRITE_TAC[NSUM_DEF] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_PERMUTE_COUNT = prove
 (`!f p n. p PERMUTES (count n) ==> (NSUM (count n) f = NSUM (count n) (f o p))`,
  PROVE_TAC[NSUM_PERMUTE, FINITE_COUNT]);

val NSUM_PERMUTE_NUMSEG = prove
 (`!f p m n.
  p PERMUTES (count n DIFF count m) ==>
   (NSUM (count n DIFF count m) f = NSUM (count n DIFF count m) (f o p))`,
  PROVE_TAC[NSUM_PERMUTE, FINITE_COUNT, FINITE_DIFF]);

val SUM_PERMUTE = prove
 (`!f p s. p PERMUTES s ==> (SUM s f = SUM s (f o p))`,
  REWRITE_TAC[SUM_DEF] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_PERMUTE_COUNT = prove
 (`!f p n. p PERMUTES (count n) ==> (SUM (count n) f = SUM (count n) (f o p))`,
  PROVE_TAC[SUM_PERMUTE, FINITE_COUNT]);

val SUM_PERMUTE_NUMSEG = prove
 (`!f p m n.
  p PERMUTES (count n DIFF count m) ==> 
   (SUM (count n DIFF count m) f = SUM (count n DIFF count m) (f o p))`,
  PROVE_TAC[SUM_PERMUTE, FINITE_COUNT, FINITE_DIFF]);

val PRODUCT_PERMUTE = prove
 (`!f p s. p PERMUTES s ==> (PRODUCT s f = PRODUCT s (f o p))`,
  REWRITE_TAC[PRODUCT_DEF] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);

val PRODUCT_PERMUTE_COUNT = prove
 (`!f p n.
    p PERMUTES (count n) ==>(PRODUCT (count n) f = PRODUCT (count n) (f o p))`,
  PROVE_TAC[PRODUCT_PERMUTE, FINITE_COUNT]);

val PRODUCT_PERMUTE_NUMSEG = prove
 (`!f p m n. 
     p PERMUTES (count n DIFF count m) ==>
       (PRODUCT (count n DIFF count m) f = PRODUCT (count n DIFF count m) (f o p))`,
  PROVE_TAC[PRODUCT_PERMUTE, FINITE_COUNT, FINITE_DIFF]);


(* ------------------------------------------------------------------------- *)
(* Various combinations of transpositions with 2, 1 and 0 common elements.   *)
(* ------------------------------------------------------------------------- *)

val SWAP_COMMON = prove
 (`!a b c: 'a. ~(a = c) /\ ~(b = c)
             ==> (SWAP (a,b) o SWAP (a,c) = SWAP (b,c) o SWAP (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, SWAP_DEF, o_THM] THEN
  DISCH_TAC THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x: 'a = a`, `x: 'a = b`, `x: 'a = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[]);

val SWAP_COMMON' = prove
 (`!a b c:'a. ~(a = b) /\ ~(a = c)
             ==> (SWAP (a,c) o SWAP (b,c) = SWAP (b,c) o SWAP (a,b))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [SWAP_SYM] THEN
  ASM_SIMP_TAC std_ss[GSYM SWAP_COMMON] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) empty_rewrites [SWAP_SYM] THEN
  REFL_TAC);

val SWAP_INDEPENDENT = prove
 (`!a b c d:'a. ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d)
               ==> (SWAP (a,b) o SWAP (c,d) = SWAP (c,d) o SWAP (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, SWAP_DEF, o_THM]  THEN
  DISCH_TAC THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x: 'a = a`, `x: 'a = b`, `x: 'a = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Permutations as transposition sequences.                                  *)
(* ------------------------------------------------------------------------- *)

val (SWAPSEQ_RULES, SWAPSEQ_INDUCT, SWAPSEQ_CASES) =
       Hol_reln
          `(SWAPSEQ 0 I) /\
  (!a b p n. SWAPSEQ n p /\ ~(a = b) ==> SWAPSEQ (SUC n) (SWAP(a,b) o p))`;

val PERMUTATION_DEF = Define
 `PERMUTATION p = ?n. SWAPSEQ n p`;
(* ------------------------------------------------------------------------- *)
(* Some closure properties of the set of permutations, with lengths.         *)
(* ------------------------------------------------------------------------- *)

val SWAPSEQ_I = CONJUNCT1 SWAPSEQ_RULES;

val PERMUTATION_I = prove
 (`PERMUTATION I`,
  REWRITE_TAC[PERMUTATION_DEF] THEN PROVE_TAC[SWAPSEQ_I]);

val SWAPSEQ_SWAP = prove
 (`!a b. SWAPSEQ (if a = b then 0 else 1) (SWAP (a,b))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[num_CONV ``1:num``] THEN
  PROVE_TAC[SWAPSEQ_RULES, I_o_ID, SWAPSEQ_I, SWAP_REFL]);

val PERMUTATION_SWAP = prove
 (`!a b. PERMUTATION (SWAP (a,b))`,
  REWRITE_TAC[PERMUTATION_DEF] THEN PROVE_TAC[SWAPSEQ_SWAP]);

val SWAPSEQ_COMPOSE = prove
 (`!n p m q. SWAPSEQ n p /\ SWAPSEQ m q ==> SWAPSEQ (n + m) (p o q)`,
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM, GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC SWAPSEQ_INDUCT THEN
  REWRITE_TAC[ADD_CLAUSES, I_o_ID, GSYM o_ASSOC] THEN
  PROVE_TAC[SWAPSEQ_RULES]);

val PERMUTATION_COMPOSE = prove
 (`!p q. PERMUTATION p /\ PERMUTATION q ==> PERMUTATION (p o q)`,
  REWRITE_TAC[PERMUTATION_DEF] THEN PROVE_TAC[SWAPSEQ_COMPOSE]);

val SWAPSEQ_ENDSWAP = prove
 (`!n p a b:'a. SWAPSEQ n p /\ ~(a = b) ==> SWAPSEQ (SUC n) (p o SWAP (a,b))`,
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM, GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC SWAPSEQ_INDUCT THEN REWRITE_TAC[I_o_ID, GSYM o_ASSOC] THEN
  PROVE_TAC[o_ASSOC, SWAPSEQ_RULES, I_o_ID ]);

val SWAPSEQ_INVERSE_EXISTS = prove
 (`!n p:'a->'a. SWAPSEQ n p ==> ?q. SWAPSEQ n q /\ (p o q = I) /\ (q o p = I)`,
  HO_MATCH_MP_TAC SWAPSEQ_INDUCT THEN CONJ_TAC THENL
   [PROVE_TAC[I_o_ID, SWAPSEQ_RULES], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`, `q:'a->'a`, `a:'a`, `b:'a`] SWAPSEQ_ENDSWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(q:'a->'a) o SWAP(a,b)` THEN
  ASM_REWRITE_TAC[GSYM o_ASSOC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV) empty_rewrites [o_ASSOC] THEN
  ASM_REWRITE_TAC[SWAP_IDEMPOTENT, I_o_ID]);

val SWAPSEQ_INVERSE = prove
 (`!n p. SWAPSEQ n p ==> SWAPSEQ n (INVERSE p)`,
  PROVE_TAC[SWAPSEQ_INVERSE_EXISTS, INVERSE_UNIQUE_o]);

val PERMUTATION_INVERSE = prove
 (`!p. PERMUTATION p ==> PERMUTATION (INVERSE p)`,
  REWRITE_TAC[PERMUTATION_DEF] THEN PROVE_TAC[SWAPSEQ_INVERSE]);

(* ------------------------------------------------------------------------- *)
(* The identity map only has even transposition sequences.                   *)
(* ------------------------------------------------------------------------- *)

val SYMMETRY_LEMMA = prove
 (`(!a b c d:'a. P a b c d ==> P a b d c) /\
   (!a b c d. ~(a = b) /\ ~(c = d) /\
             ((a = c) /\ (b = d) \/ (a = c) /\ ~(b = d) \/ ~(a = c) /\ (b = d) \/
               ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d))
              ==> P a b c d)
   ==> (!a b c d. ~(a = b) /\ ~(c = d) ==> P a b c d)`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`a:'a = c`, `a:'a = d`, `b:'a = c`, `b:'a = d`] THEN
  PROVE_TAC[]);

val SWAP_GENERAL = prove
 (`!a b c d:'a.
        ~(a = b) /\ ~(c = d)
        ==> (SWAP (a,b) o SWAP (c,d) = I) \/
            ?x y z. ~(x = a) /\ ~(y = a) /\ ~(z = a) /\ ~(x = y) /\
                    (SWAP (a,b) o SWAP (c,d) = SWAP (x,y) o SWAP (a,z))`,
  HO_MATCH_MP_TAC SYMMETRY_LEMMA THEN CONJ_TAC THENL
   [SIMP_TAC std_ss[SWAP_SYM], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [PROVE_TAC[SWAP_IDEMPOTENT],
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`b:'a`, `d:'a`, `b:'a`] THEN
    PROVE_TAC[SWAP_COMMON],
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`c:'a`, `d:'a`, `c:'a`] THEN
    PROVE_TAC[SWAP_COMMON'],
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`c:'a`, `d:'a`, `b:'a`] THEN
PROVE_TAC[SWAP_INDEPENDENT]]);

val FIXING_SWAPSEQ_DECREASE = prove
 (`!n p a b:'a.
      SWAPSEQ n p /\ ~(a = b) /\ ((SWAP (a,b) o p) a = a)
      ==> ~(n = 0) /\ SWAPSEQ (n - 1) (SWAP (a,b) o p)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [SWAPSEQ_CASES] THEN
  REWRITE_TAC[SUC_NOT, GSYM SUC_NOT] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[I_THM, o_THM, SWAP_DEF] THEN PROVE_TAC[],
    ALL_TAC] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:'a`, `d:'a`, `q:'a->'a`, `m:num`] THEN
  REWRITE_TAC[ADD1,EQ_ADD_RCANCEL, GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[o_ASSOC] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:'a`, `b:'a`, `c:'a`, `d:'a`] SWAP_GENERAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[I_o_ID, ADD_SUB] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:'a`, `y:'a`, `z:'a`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`q:'a->'a`, `a:'a`, `z:'a`]) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    empty_rewrites [EQ_SYM_EQ] THEN ASM_REWRITE_TAC[] THEN
    Q.PAT_ASSUM `$= X Y` MP_TAC THEN
    REWRITE_TAC[GSYM o_ASSOC] THEN
    ABBREV_TAC `r:'a->'a = SWAP(a:'a,z) o q` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM, o_THM, SWAP_DEF] THEN PROVE_TAC[],
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUC_NOT, SUC_SUB1, GSYM o_ASSOC] THEN
PROVE_TAC[SWAPSEQ_RULES]]);

val SWAPSEQ_IDENTITY_EVEN = prove
 (`!n. SWAPSEQ n (I:'a->'a) ==> EVEN n`,
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [SWAPSEQ_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o CONJUNCT1) MP_TAC) THEN
  REWRITE_TAC[EVEN] THEN SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:'a`, `b:'a`, `p:'a->'a`, `m:num`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(SPECL [`m:num`, `p:'a->'a`, `a:'a`, `b:'a`]
    FIXING_SWAPSEQ_DECREASE) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    empty_rewrites [EQ_SYM_EQ] THEN ASM_REWRITE_TAC[I_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``(m - 1):num``) THEN
  UNDISCH_THEN `SUC m = n` (SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[DECIDE ``m - 1 < SUC m``] THEN UNDISCH_TAC `~(m = 0)` THEN
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[SUC_SUB1, EVEN]);

(* ------------------------------------------------------------------------- *)
(* Therefore we have a welldefined notion of parity.                         *)
(* ------------------------------------------------------------------------- *)

val EVENPERM_DEF = Define `EVENPERM p = EVEN(@n. SWAPSEQ n p)`;

val SWAPSEQ_EVEN_EVEN = prove
 (`!m n p:'a->'a. SWAPSEQ m p /\ SWAPSEQ n p ==> (EVEN m <=> EVEN n)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``SWAPSEQ (n + m) :('a->'a)->bool``) THEN
  ASM_SIMP_TAC bool_ss[SWAPSEQ_COMPOSE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SWAPSEQ_IDENTITY_EVEN) THEN
  SIMP_TAC bool_ss[EVEN_ADD]);

val EVENPERM_UNIQUE = prove
 (`!n p b. SWAPSEQ n p /\ (EVEN n = b) ==> (EVENPERM p = b)`,
  REWRITE_TAC[EVENPERM_DEF] THEN METIS_TAC[SWAPSEQ_EVEN_EVEN]);

(* ------------------------------------------------------------------------- *)
(* And it has the expected composition properties.                           *)
(* ------------------------------------------------------------------------- *)

val EVENPERM_I = prove
 (`EVENPERM I = T`,
  MATCH_MP_TAC EVENPERM_UNIQUE THEN PROVE_TAC[SWAPSEQ_RULES, EVEN]);

val EVENPERM_SWAP = prove
 (`!a b:'a. EVENPERM (SWAP(a,b)) = (a = b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EVENPERM_UNIQUE THEN
  METIS_TAC[SWAPSEQ_SWAP, EVEN, num_CONV ``1:num``]);

val EVENPERM_COMPOSE = prove
 (`!p q. PERMUTATION p /\ PERMUTATION q
         ==> (EVENPERM (p o q) = (EVENPERM p = EVENPERM q))`,
  REWRITE_TAC[PERMUTATION_DEF] THEN
  SIMP_TAC bool_ss[GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN
               ASSUME_TAC(MATCH_MP SWAPSEQ_COMPOSE th)) THEN
  METIS_TAC[EVENPERM_UNIQUE, SWAPSEQ_COMPOSE, EVEN_ADD]);

val EVENPERM_INVERSE = prove
 (`!p. PERMUTATION p ==>(EVENPERM (INVERSE p) = EVENPERM p)`,
  REWRITE_TAC[PERMUTATION_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EVENPERM_UNIQUE THEN
  METIS_TAC[SWAPSEQ_INVERSE, EVENPERM_UNIQUE]);

(* ------------------------------------------------------------------------- *)
(* A more abstract characterization of permutations.                         *)
(* ------------------------------------------------------------------------- *)

val PERMUTATION_BIJECTIVE = prove
 (`!p. PERMUTATION p ==> !y. ?!x. p(x) = y`,
  REWRITE_TAC[PERMUTATION_DEF] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  SIMP_TAC bool_ss[FUN_EQ_THM, I_THM, o_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  METIS_TAC[]);

val PERMUTATION_FINITE_SUPPORT = prove
 (`!p. PERMUTATION p ==> FINITE {x:'a| ~(p x = x)}`,
  SIMP_TAC bool_ss[PERMUTATION_DEF, GSYM LEFT_FORALL_IMP_THM] THEN
  CONV_TAC SWAP_VARS_CONV THEN HO_MATCH_MP_TAC SWAPSEQ_INDUCT THEN
  REWRITE_TAC[I_THM, FINITE_RULES,
              prove (`{x | F} = {}`,REWRITE_TAC[EXTENSION] THEN
              CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN 
              REWRITE_TAC[NOT_IN_EMPTY])] THEN
  MAP_EVERY X_GEN_TAC [`a:'a`, `b:'a`, `p:'a->'a`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_FINITE_I THEN
  EXISTS_TAC `(a:'a) INSERT b INSERT {x | ~(p x = x)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT, SUBSET_DEF, IN_INSERT] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[o_THM, SWAP_DEF] THEN PROVE_TAC[]);

val PERMUTATION_LEMMA = prove
 (`!s p:'a->'a.
       FINITE s /\
       (!y. ?!x. p(x) = y) /\ (!x. ~(x IN s) ==> (p x = x))
       ==> PERMUTATION p`,
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p:'a->'a = I` (fn th => REWRITE_TAC[th, PERMUTATION_I]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM, I_THM],
    ALL_TAC] THEN
  X_GEN_TAC `s:'a->bool` THEN STRIP_TAC THEN X_GEN_TAC `a:'a` THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `PERMUTATION ((SWAP(a,p(a)) o SWAP(a,p(a))) o (p:'a->'a))`
  MP_TAC THENL [ALL_TAC, REWRITE_TAC[SWAP_IDEMPOTENT, I_o_ID]] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN MATCH_MP_TAC PERMUTATION_COMPOSE THEN
  REWRITE_TAC[PERMUTATION_SWAP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `!y. ?!x. (p:'a->'a) x = y` THEN
    SIMP_TAC bool_ss[EXISTS_UNIQUE_THM, SWAP_DEF, o_THM] THEN
    ASM_CASES_TAC `(p:'a->'a) a = a` THEN ASM_REWRITE_TAC[] THENL
     [PROVE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[prove(
     `((if p then x else y) = a) <=> if p then x = a else y = a`,PROVE_TAC[])] THEN
    REWRITE_TAC[TAUT `(if p then x else y) <=> p /\ x \/ ~p /\ y`] THEN
    PROVE_TAC[],
    REWRITE_TAC[SWAP_DEF, o_THM] THEN
    ASM_CASES_TAC `(p:'a->'a) a = a` THEN ASM_REWRITE_TAC[] THEN
    PROVE_TAC[]]);

val PERMUTATION = prove
 (`!p. PERMUTATION p <=> (!y. ?!x. p(x) = y) /\ FINITE {x:'a| ~(p(x) = x)}`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC bool_ss[PERMUTATION_BIJECTIVE, PERMUTATION_FINITE_SUPPORT] THEN
  STRIP_TAC THEN MATCH_MP_TAC PERMUTATION_LEMMA THEN
  EXISTS_TAC `{x:'a| ~(p x = x)}` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  ASM_REWRITE_TAC[]);

val PERMUTATION_INVERSE_WORKS = prove
 (`!p. PERMUTATION p ==> (INVERSE p o p = I) /\ (p o INVERSE p = I)`,
  PROVE_TAC[PERMUTATION_BIJECTIVE, SURJECTIVE_INVERSE_o,
            INJECTIVE_INVERSE_o]);

val PERMUTATION_INVERSE_COMPOSE = prove
 (`!p q. PERMUTATION p /\ PERMUTATION q
         ==> (INVERSE (p o q) = INVERSE q o INVERSE p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTATION_INVERSE_WORKS)) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [o_ASSOC] THEN
  ASM_REWRITE_TAC[I_o_ID]);

(* ------------------------------------------------------------------------- *)
(* Relation to "permutes".                                                   *)
(* ------------------------------------------------------------------------- *)

val PERMUTATION_PERMUTES = prove
 (`!p:'a->'a. PERMUTATION p <=> ?s. FINITE s /\ p PERMUTES s`,
  GEN_TAC THEN REWRITE_TAC[PERMUTATION, PERMUTES_DEF] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `{x:'a | ~(p x = x)}` THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC SUBSET_FINITE_I THEN EXISTS_TAC `s:'a->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DEF] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]]);

(* ------------------------------------------------------------------------- *)
(* Hence a sort of induction principle composing by swaps.                   *)
(* ------------------------------------------------------------------------- *)

val PERMUTES_INDUCT = prove
 (`!P s. FINITE s /\
         P I /\
         (!a b:'a p. a IN s /\ b IN s /\ P p /\ PERMUTATION p
                    ==> P (SWAP(a,b) o p))
         ==> (!p. p PERMUTES s ==> P p)`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a ==> c ==> d`] THEN
  SIMP_TAC std_ss[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_REWRITE_TAC[PERMUTES_EMPTY, IN_INSERT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p = SWAP(e,p e) o SWAP(e,p e) o (p:'a->'a)` SUBST1_TAC THENL
   [REWRITE_TAC[o_ASSOC, SWAP_IDEMPOTENT, I_o_ID], ALL_TAC] THEN
  Q.PAT_ASSUM `$==> X Y` MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN
  DISCH_THEN(fn th => FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_INSERT, PERMUTES_INSERT_LEMMA,
                PERMUTATION_PERMUTES, FINITE_INSERT, PERMUTATION_COMPOSE,
                PERMUTATION_SWAP]);

(* ------------------------------------------------------------------------- *)
(* Sign of a permutation as a real number.                                   *)
(* ------------------------------------------------------------------------- *)

val SIGN_DEF = Define
 `(SIGN p):real = if EVENPERM p then &1 else - &1`;

val SIGN_NZ = prove
 (`!p. ~(SIGN p = &0)`,
  REWRITE_TAC[SIGN_DEF] THEN GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);

val SIGN_I = prove
 (`SIGN I = &1`,
  REWRITE_TAC[SIGN_DEF, EVENPERM_I]);

val SIGN_INVERSE = prove
 (`!p. PERMUTATION p ==> (SIGN (INVERSE p) = SIGN p)`,
  SIMP_TAC bool_ss[SIGN_DEF, EVENPERM_INVERSE]);

val SIGN_COMPOSE = prove
 (`!p q. PERMUTATION p /\ PERMUTATION q ==> (SIGN (p o q) = SIGN (p) * SIGN (q))`,
  SIMP_TAC bool_ss[SIGN_DEF, EVENPERM_COMPOSE] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`EVENPERM p`, `EVENPERM q`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);

val SIGN_SWAP = prove
 (`!a b. SIGN (SWAP (a,b)) = if a = b then &1 else - &1`,
  REWRITE_TAC[SIGN_DEF, EVENPERM_SWAP]);

val SIGN_IDEMPOTENT = prove
 (`!p. SIGN (p) * SIGN (p) = &1`,
  GEN_TAC THEN REWRITE_TAC[SIGN_DEF] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);

val REAL_ABS_SIGN = prove
 (`!p. abs(SIGN p) = &1`,
  REWRITE_TAC[SIGN_DEF] THEN REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* More lemmas about permutations.                                           *)
(* ------------------------------------------------------------------------- *)

val PERMUTES_NUMSET_LE = prove
 (`!p s:num->bool. p PERMUTES s /\ (!i. i IN s ==> p(i) <= i) ==> (p = I)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, I_THM] THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC COMPLETE_INDUCTION THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(n:num) IN s` THENL [ALL_TAC, PROVE_TAC[PERMUTES_DEF]] THEN
  ASM_SIMP_TAC bool_ss[EQ_LESS_EQ] THEN REWRITE_TAC[GSYM NOT_LESS] THEN
  PROVE_TAC[PERMUTES_INJECTIVE, LESS_EQ_REFL,NOT_LESS]);

val PERMUTES_NUMSET_GE = prove
 (`!p s:num->bool. p PERMUTES s /\ (!i. i IN s ==> i <= p(i)) ==> (p = I)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`INVERSE(p:num->num)`, `s:num->bool`] PERMUTES_NUMSET_LE) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [PROVE_TAC[PERMUTES_INVERSE, PERMUTES_INVERSES, PERMUTES_IN_IMAGE],
    PROVE_TAC[PERMUTES_INVERSE_INVERSE, INVERSE_I]]);

val IMAGE_INVERSE_PERMUTATIONS = prove
 (`!s:'a->bool. {INVERSE p | p PERMUTES s} = {p | p PERMUTES s}`,
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[PERMUTES_INVERSE_INVERSE, PERMUTES_INVERSE]);

val IMAGE_COMPOSE_PERMUTATIONS_L = prove
 (`!s q:'a->'a. q PERMUTES s ==> ({q o p | p PERMUTES s} = {p | p PERMUTES s})`,
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:'a->'a` THEN EQ_TAC THENL
   [PROVE_TAC[PERMUTES_COMPOSE],
    DISCH_TAC THEN EXISTS_TAC `INVERSE (q:'a->'a) o (p:'a->'a)` THEN
    ASM_SIMP_TAC bool_ss[o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
    PROVE_TAC [PERMUTES_INVERSES_o, I_o_ID]]);

val IMAGE_COMPOSE_PERMUTATIONS_R = prove
 (`!s q:'a->'a. q PERMUTES s ==> ({p o q | p PERMUTES s} = {p | p PERMUTES s})`,
  REWRITE_TAC[EXTENSION] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:'a->'a` THEN EQ_TAC THENL
   [PROVE_TAC[PERMUTES_COMPOSE],
    DISCH_TAC THEN EXISTS_TAC `(p:'a->'a) o INVERSE (q:'a->'a)` THEN
    ASM_SIMP_TAC bool_ss[GSYM o_ASSOC, PERMUTES_INVERSE, PERMUTES_COMPOSE] THEN
    PROVE_TAC [PERMUTES_INVERSES_o, I_o_ID]]);

val PERMUTES_IN_COUNT = prove
 (`!p n i. p PERMUTES count n /\ i IN count n ==>  p(i) < n`,
  REWRITE_TAC[PERMUTES_DEF, IN_COUNT] THEN PROVE_TAC[]);

val PERMUTES_IN_NUMSEG = prove
 (`!p n i.
   p PERMUTES (count n DIFF count m) /\ i IN (count n DIFF count m) ==>
       p(i) < n`,
  REWRITE_TAC[PERMUTES_DEF, IN_NUMSEG] THEN PROVE_TAC[]);

val SUM_PERMUTATIONS_INVERSE = prove
 (`!f m n. SUM {p | p PERMUTES count n } f =
           SUM {p | p PERMUTES count n } (\p. f(INVERSE p))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM IMAGE_INVERSE_PERMUTATIONS] THEN
  SIMP_TAC bool_ss
   [Once (prove(`{f x | p x} = IMAGE f {x | p x}`, 
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM o_DEF] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[PERMUTES_INVERSE_INVERSE]);

val SUM_PERMUTATIONS_COMPOSE_L = prove
 (`!f s q.
        q PERMUTES s
        ==> (SUM {p | p PERMUTES s} f =
            SUM {p | p PERMUTES s} (\p. f(q o p)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  SIMP_TAC bool_ss
   [Once (prove(`{f x | p x} = IMAGE f {x | p x}`, 
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[GSYM o_DEF, ETA_THM] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:'a-> 'a. INVERSE(q:'a-> 'a) o p``) THEN
  BETA_TAC THEN REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]);

val SUM_PERMUTATIONS_COMPOSE_L_COUNT = prove
 (`!f n q.
        q PERMUTES count n
        ==> (SUM {p | p PERMUTES count n} f =
            SUM {p | p PERMUTES count n} (\p. f(q o p)))`,
  REWRITE_TAC[SUM_PERMUTATIONS_COMPOSE_L]);

val SUM_PERMUTATIONS_COMPOSE_L_NUMSEG = prove
 (`!f m n q.
        q PERMUTES (count n DIFF count m)
        ==> (SUM {p | p PERMUTES (count n DIFF count m)} f =
            SUM {p | p PERMUTES (count n DIFF count m)} (\p. f(q o p)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  SIMP_TAC bool_ss
   [Once (prove(`{f x | p x} = IMAGE f {x | p x}`, 
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[GSYM o_DEF, ETA_THM] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:num-> num. INVERSE(q:num-> num) o p``) THEN
  BETA_TAC THEN REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]);

val SUM_PERMUTATIONS_COMPOSE_R = prove
  (`!f s q.
        q PERMUTES s
        ==> (SUM {p | p PERMUTES s} f =
            SUM {p | p PERMUTES s} (\p. f(p o q)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  SIMP_TAC bool_ss
   [Once (prove(`{f x | p x} = IMAGE f {x | p x}`, 
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  SIMP_TAC bool_ss[GSYM o_ABS_R] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:'a-> 'a. p o INVERSE(q:'a-> 'a)``) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]);

val SUM_PERMUTATIONS_COMPOSE_R_COUNT = prove
 (`!f n q.
        q PERMUTES count n
        ==> (SUM {p | p PERMUTES count n} f =
            SUM {p | p PERMUTES count n} (\p. f(p o q)))`,
  REWRITE_TAC[SUM_PERMUTATIONS_COMPOSE_R]);

val SUM_PERMUTATIONS_COMPOSE_R_NUMSEG = prove
 (`!f m n q.
        q PERMUTES (count n DIFF count m)
        ==> (SUM {p | p PERMUTES (count n DIFF count m)} f =
            SUM {p | p PERMUTES (count n DIFF count m)} (\p. f(p o q)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  SIMP_TAC bool_ss
   [Once (prove(`{f x | p x} = IMAGE f {x | p x}`, 
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  SIMP_TAC bool_ss[GSYM o_ABS_R] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:num-> num. p o INVERSE(q:num-> num)``) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]);




