(*
   Development of a theory of numerals, including rewrite theorems for
   the basic arithmetic operations and relations.

       Michael Norrish, December 1998

   Inspired by a similar development done by John Harrison for his
   HOL Light theorem prover.
 *)

(* for interactive development of this theory; evaluate the following
   commands before trying to evaluate the ML that follows *)
(* fun mload s = (print ("Loading "^s^"\n"); load s);
   app mload ["simpLib", "boolSimps", "arithmeticTheory", "QLib",
              "primWFTheory", "Rsyntax", "mesonLib"] *)

open HolKernel basicHol90Lib arithmeticTheory simpLib Parse;
infix THEN THENL THENC ++ |->;

val _ = new_theory "numeral";

val bool_ss = boolSimps.bool_ss;

val INV_SUC_EQ    = prim_recTheory.INV_SUC_EQ
and LESS_REFL     = prim_recTheory.LESS_REFL
and SUC_LESS      = prim_recTheory.SUC_LESS
and NOT_LESS_0    = prim_recTheory.NOT_LESS_0
and LESS_MONO     = prim_recTheory.LESS_MONO
and LESS_SUC_REFL = prim_recTheory.LESS_SUC_REFL
and LESS_SUC      = prim_recTheory.LESS_SUC
and LESS_THM      = prim_recTheory.LESS_THM
and LESS_SUC_IMP  = prim_recTheory.LESS_SUC_IMP
and LESS_0        = prim_recTheory.LESS_0
and EQ_LESS       = prim_recTheory.EQ_LESS
and SUC_ID        = prim_recTheory.SUC_ID
and NOT_LESS_EQ   = prim_recTheory.NOT_LESS_EQ
and LESS_NOT_EQ   = prim_recTheory.LESS_NOT_EQ
and LESS_SUC_SUC  = prim_recTheory.LESS_SUC_SUC
and PRE           = prim_recTheory.PRE;

val NOT_SUC     = numTheory.NOT_SUC
and INV_SUC     = numTheory.INV_SUC
and INDUCTION   = numTheory.INDUCTION
and NUMERAL_DEF = arithmeticTheory.NUMERAL_DEF;

val INDUCT_TAC = INDUCT_THEN INDUCTION ASSUME_TAC

val _ = print "Developing rewrites for numeral addition\n"

val PRE_ADD = prove(
  --`!n m. PRE (n + SUC m) = n + m`--,
  INDUCT_TAC THEN SIMP_TAC bool_ss [ADD_CLAUSES, PRE]);

val numeral_suc = store_thm(
  "numeral_suc",
  Term `(SUC ALT_ZERO = NUMERAL_BIT1 ALT_ZERO) /\
        (!n. SUC (NUMERAL_BIT1 n) = NUMERAL_BIT2 n) /\
        (!n. SUC (NUMERAL_BIT2 n) = NUMERAL_BIT1 (SUC n))`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, ALT_ZERO, ADD_CLAUSES]);

(* internal markers *)
(* throughout this theory, we will be using various internal markers
   that represent some intermediate result within an algorithm.  All
   such markers are constants with names that have leading i's *)
val iZ = new_definition("iZ", --`iZ (x:num) = x`--);
val iiSUC = new_definition("iiSUC", --`iiSUC n = SUC (SUC n)`--);

val numeral_distrib = store_thm(
  "numeral_distrib", Term
  `(!n. 0 + n = n) /\ (!n. n + 0 = n) /\
   (!n m. NUMERAL n + NUMERAL m = NUMERAL (iZ (n + m))) /\
   (!n. 0 * n = 0) /\ (!n. n * 0 = 0) /\
   (!n m. NUMERAL n * NUMERAL m = NUMERAL (n * m)) /\
   (!n. 0 - n = 0) /\ (!n. n - 0 = n) /\
   (!n m. NUMERAL n - NUMERAL m = NUMERAL (n - m)) /\
   (!n. 0 EXP (NUMERAL (NUMERAL_BIT1 n)) = 0) /\
   (!n. 0 EXP (NUMERAL (NUMERAL_BIT2 n)) = 0) /\
   (!n. n EXP 0 = 1) /\
   (!n m. (NUMERAL n) EXP (NUMERAL m) = NUMERAL (n EXP m)) /\
   (SUC 0 = 1) /\
   (!n. SUC(NUMERAL n) = NUMERAL (SUC n)) /\
   (PRE 0 = 0) /\
   (!n. PRE(NUMERAL n) = NUMERAL (PRE n)) /\
   (!n. (NUMERAL n = 0) = (n = ALT_ZERO)) /\
   (!n. (0 = NUMERAL n) = (n = ALT_ZERO)) /\
   (!n m. (NUMERAL n = NUMERAL m) = (n=m)) /\
   (!n. n < 0 = F) /\ (!n. 0 < NUMERAL n = ALT_ZERO < n) /\
   (!n m. NUMERAL n < NUMERAL m  = n<m)  /\
   (!n. 0 > n = F) /\ (!n. NUMERAL n > 0 = ALT_ZERO < n) /\
   (!n m. NUMERAL n > NUMERAL m  = m<n)  /\
   (!n. 0 <= n = T) /\ (!n. NUMERAL n <= 0 = n <= ALT_ZERO) /\
   (!n m. NUMERAL n <= NUMERAL m = n<=m) /\
   (!n. n >= 0 = T) /\ (!n. NUMERAL n >= 0 = ALT_ZERO <= n) /\
   (!n m. NUMERAL n >= NUMERAL m = m <= n)`,
  SIMP_TAC bool_ss [NUMERAL_DEF, GREATER_DEF, iZ, GREATER_OR_EQ,
                    LESS_OR_EQ, EQ_IMP_THM, DISJ_IMP_THM, ADD_CLAUSES,
                    ALT_ZERO, MULT_CLAUSES, EXP, PRE, NOT_LESS_0, SUB_0,
                    NUMERAL_BIT1, NUMERAL_BIT2] THEN
  mesonLib.MESON_TAC [LESS_0_CASES]);

val numeral_iisuc = store_thm(
  "numeral_iisuc", Term
  `(iiSUC ALT_ZERO = NUMERAL_BIT2 ALT_ZERO) /\
   (iiSUC (NUMERAL_BIT1 n) = NUMERAL_BIT1 (SUC n)) /\
   (iiSUC (NUMERAL_BIT2 n) = NUMERAL_BIT2 (SUC n))`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, iiSUC, ALT_ZERO,
                    ADD_CLAUSES]);

(* the following addition algorithm makes use of internal markers iZ and
   iiSUC.

   iZ is used to mark the place where the algorithm is currently working.
   Without a rule such as the fourth below would give the rewriter a chance
   to rewrite away an addition under a SUC, which we don't want.

   SUC is used as an internal marker to represent carrying one, while
   iiSUC is used to represent carrying two (necessary with our
   formulation of numerals).
*)
val numeral_add = store_thm(
  "numeral_add",
  Term
  `!n m.
   (iZ (ALT_ZERO + n) = n) /\ (iZ (n + ALT_ZERO) = n) /\
   (iZ (NUMERAL_BIT1 n + NUMERAL_BIT1 m) = NUMERAL_BIT2 (iZ (n + m))) /\
   (iZ (NUMERAL_BIT1 n + NUMERAL_BIT2 m) = NUMERAL_BIT1 (SUC (n + m))) /\
   (iZ (NUMERAL_BIT2 n + NUMERAL_BIT1 m) = NUMERAL_BIT1 (SUC (n + m))) /\
   (iZ (NUMERAL_BIT2 n + NUMERAL_BIT2 m) = NUMERAL_BIT2 (SUC (n + m))) /\
   (SUC (ALT_ZERO + n) = SUC n) /\ (SUC (n + ALT_ZERO) = SUC n) /\
   (SUC (NUMERAL_BIT1 n + NUMERAL_BIT1 m) = NUMERAL_BIT1 (SUC (n + m))) /\
   (SUC (NUMERAL_BIT1 n + NUMERAL_BIT2 m) = NUMERAL_BIT2 (SUC (n + m))) /\
   (SUC (NUMERAL_BIT2 n + NUMERAL_BIT1 m) = NUMERAL_BIT2 (SUC (n + m))) /\
   (SUC (NUMERAL_BIT2 n + NUMERAL_BIT2 m) = NUMERAL_BIT1 (iiSUC (n + m))) /\
   (iiSUC (ALT_ZERO + n) = iiSUC n) /\ (iiSUC (n + ALT_ZERO) = iiSUC n) /\
   (iiSUC (NUMERAL_BIT1 n + NUMERAL_BIT1 m) =
      NUMERAL_BIT2 (SUC (n + m))) /\
   (iiSUC (NUMERAL_BIT1 n + NUMERAL_BIT2 m) =
      NUMERAL_BIT1 (iiSUC (n + m))) /\
   (iiSUC (NUMERAL_BIT2 n + NUMERAL_BIT1 m) =
      NUMERAL_BIT1 (iiSUC (n + m))) /\
   (iiSUC (NUMERAL_BIT2 n + NUMERAL_BIT2 m) =
      NUMERAL_BIT2 (iiSUC (n + m)))`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, iZ, iiSUC,
                    ADD_CLAUSES, INV_SUC_EQ, ALT_ZERO] THEN
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV(ADD_ASSOC, ADD_SYM)));

(* rewrites needed for addition *)
val add_rwts = [numeral_distrib, numeral_add, numeral_suc, numeral_iisuc]

val numeral_proof_rwts = [NUMERAL_BIT1, NUMERAL_BIT2, INV_SUC_EQ,
                          NUMERAL_DEF, iZ, iiSUC, ADD_CLAUSES, NOT_SUC,
                          SUC_NOT, LESS_0, NOT_LESS_0, ALT_ZERO]

val double_add_not_SUC = prove(Term
`!n m.
   ~(SUC (n + n) = m + m) /\ ~(m + m = SUC (n + n))`,
  INDUCT_TAC THEN SIMP_TAC bool_ss numeral_proof_rwts THEN
  INDUCT_TAC THEN ASM_SIMP_TAC bool_ss numeral_proof_rwts);

val _ = print "Developing numeral rewrites for relations\n"

val numeral_eq = store_thm(
  "numeral_eq",
  Term`!n m.
    ((ALT_ZERO = NUMERAL_BIT1 n) = F) /\ ((NUMERAL_BIT1 n = ALT_ZERO) = F) /\
    ((ALT_ZERO = NUMERAL_BIT2 n) = F) /\ ((NUMERAL_BIT2 n = ALT_ZERO) = F) /\
    ((NUMERAL_BIT1 n = NUMERAL_BIT2 m) = F) /\
    ((NUMERAL_BIT2 n = NUMERAL_BIT1 m) = F) /\
    ((NUMERAL_BIT1 n = NUMERAL_BIT1 m) = (n = m)) /\
    ((NUMERAL_BIT2 n = NUMERAL_BIT2 m) = (n = m))`,
  SIMP_TAC bool_ss numeral_proof_rwts THEN
  INDUCT_TAC THEN
  SIMP_TAC bool_ss (double_add_not_SUC::numeral_proof_rwts) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC bool_ss numeral_proof_rwts);

val mk_var = Psyntax.mk_var
fun ncases str n0 =
  DISJ_CASES_THEN2 SUBST_ALL_TAC
                   (X_CHOOSE_THEN (mk_var(n0, (==`:num`==))) SUBST_ALL_TAC)
                   (SPEC (mk_var(str, (==`:num`==))) num_CASES)

val double_less = prove(Term
  `!n m. (n + n < m + m = n < m) /\ (n + n <= m + m = n <= m)`,
  INDUCT_TAC THEN GEN_TAC THEN ncases "m" "m0" THEN
  ASM_SIMP_TAC bool_ss [ADD_CLAUSES, NOT_LESS_0, LESS_0, LESS_MONO_EQ,
                        ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_EQ_MONO]);


val double_1suc_less = prove(Term
  `!x y. (SUC(x + x) < y + y = x < y) /\
         (SUC(x + x) <= y + y = x < y) /\
         (x + x < SUC(y + y) = ~(y < x)) /\
         (x + x <= SUC(y + y) = ~(y < x))`,
  INDUCT_TAC THEN GEN_TAC THEN ncases "y" "y0" THEN
  ASM_SIMP_TAC bool_ss [ADD_CLAUSES, LESS_EQ_MONO, NOT_LESS_0,
                        ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, LESS_0,
                        LESS_MONO_EQ]);

val double_2suc_less = prove(Term
`!n m. (n + n < SUC (SUC (m + m)) = n < SUC m) /\
       (SUC (SUC (m + m)) < n + n = SUC m < n) /\
       (n + n <= SUC (SUC (m + m)) = n <= SUC m) /\
       (SUC (SUC (m + m)) <= n + n = SUC m <= n)`,
ONCE_REWRITE_TAC [GSYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
ONCE_REWRITE_TAC [GSYM (el 3 (CONJUNCTS ADD_CLAUSES))] THEN
REWRITE_TAC [double_less]);

val DOUBLE_FACTS = LIST_CONJ [double_less, double_1suc_less, double_2suc_less]


val numeral_lt = store_thm(
  "numeral_lt",
  Term
  `!n m.
    (ALT_ZERO < NUMERAL_BIT1 n = T) /\ (ALT_ZERO < NUMERAL_BIT2 n = T) /\
    (n < ALT_ZERO = F) /\
    (NUMERAL_BIT1 n < NUMERAL_BIT1 m = n < m) /\
    (NUMERAL_BIT2 n < NUMERAL_BIT2 m = n < m) /\
    (NUMERAL_BIT1 n < NUMERAL_BIT2 m = ~(m < n)) /\
    (NUMERAL_BIT2 n < NUMERAL_BIT1 m = n < m)`,
  SIMP_TAC bool_ss (DOUBLE_FACTS::LESS_MONO_EQ::numeral_proof_rwts));

(* I've kept this rewrite entirely independent of the above.  I don't if
   this is a good idea or not. *)

val numeral_lte = store_thm(
  "numeral_lte", Term
  `!n m. (ALT_ZERO <= n = T) /\
         (NUMERAL_BIT1 n <= ALT_ZERO = F) /\ (NUMERAL_BIT2 n <= ALT_ZERO = F) /\
         (NUMERAL_BIT1 n <= NUMERAL_BIT1 m = n <= m) /\
         (NUMERAL_BIT1 n <= NUMERAL_BIT2 m = n <= m) /\
         (NUMERAL_BIT2 n <= NUMERAL_BIT1 m = ~(m <= n)) /\
         (NUMERAL_BIT2 n <= NUMERAL_BIT2 m = n <= m)`,
  SIMP_TAC bool_ss ([DOUBLE_FACTS, LESS_MONO_EQ, LESS_EQ_MONO] @
                    (map (REWRITE_RULE [NUMERAL_DEF])
                         [ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, NOT_LESS]) @
                    numeral_proof_rwts) THEN
  SIMP_TAC bool_ss [GSYM NOT_LESS]);

val _ = print "Developing numeral rewrites for subtraction\n"
val _ = print "   (includes initiality theorem for bit functions)\n"

val numeral_pre = store_thm(
  "numeral_pre",
  --`(PRE ALT_ZERO = ALT_ZERO) /\
     (PRE (NUMERAL_BIT1 ALT_ZERO) = ALT_ZERO) /\
     (!n. PRE (NUMERAL_BIT1 (NUMERAL_BIT1 n)) =
          NUMERAL_BIT2 (PRE (NUMERAL_BIT1 n))) /\
     (!n. PRE (NUMERAL_BIT1 (NUMERAL_BIT2 n)) =
          NUMERAL_BIT2 (NUMERAL_BIT1 n)) /\
     (!n. PRE (NUMERAL_BIT2 n) = NUMERAL_BIT1 n)`--,
  SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, PRE, PRE_ADD,
                    ADD_CLAUSES, ADD_ASSOC, PRE, ALT_ZERO]);

(* we could just go on and prove similar rewrites for subtraction, but
   they get a bit inefficient because every iteration of the rewriting
   ends up checking whether or not x < y.  To get around this, we prove
   initiality for our BIT functions and ZERO, and then define a function
   which implements bitwise subtraction for x and y, assuming that x is
   at least as big as y. *)

(* first initiality *)

(* this proof is taken from the WF theory in Konrad Slind's tfl library.
   The rest of the WF theory is a bit dependent on the rest of arithmetic,
   but this result isn't, so we can just appropriate it without having
   to suck in all of WF as well. *)
val WF_LESS = store_thm(
  "WF_LESS",
  --`WF $<`--,
  REWRITE_TAC[primWFTheory.WF_DEF] THEN GEN_TAC THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN (fn th1 =>
       SUBGOAL_THEN (--`^(concl th1) ==> !i j. j<i ==> ~B j`--)
                    (fn th => MP_TAC (MP th th1))) THEN
  CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THENL [
    INDUCT_THEN numTheory.INDUCTION STRIP_ASSUME_TAC THEN GEN_TAC THEN
    REWRITE_TAC [prim_recTheory.NOT_LESS_0,
                 prim_recTheory.LESS_THM] THEN
    DISCH_THEN (DISJ_CASES_THENL [SUBST1_TAC, ASSUME_TAC]) THEN
    STRIP_TAC THEN RES_TAC,
    GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC (--`SUC w`--) THEN
    MATCH_ACCEPT_TAC prim_recTheory.LESS_SUC_REFL
  ]);

(* our measure function *)
val our_M =
 --`\f a. (a = ALT_ZERO)
          => (zf:'a)
          |  (?n. (a = NUMERAL_BIT1 n))
             => (b1f:'a->num->'a) (f (@n. a = NUMERAL_BIT1 n))
                                  (@n. a = NUMERAL_BIT1 n)
             |  b2f (f (@n. a = NUMERAL_BIT2 n)) (@n. a = NUMERAL_BIT2 n)`--

fun AP_TAC (asl, g) =
  let open Psyntax
      val _ = is_eq g orelse raise Fail "Goal not an equality"
      val (lhs, rhs) = dest_eq g
      val (lf, la) = dest_comb lhs handle _ =>
                       raise Fail "lhs must be an application"
      val (rf, ra) = dest_comb rhs handle _ =>
                       raise Fail "rhs must be an application"
  in
      if (lf = rf) then AP_TERM_TAC (asl, g) else
      if (la = ra) then AP_THM_TAC (asl, g) else
      raise Fail "One of function or argument must be equal"
  end
val APn_TAC = REPEAT AP_TAC;


val bit_initiality0 = prove(Term
  `!zf b1f b2f.
      ?f.
        (f ALT_ZERO = zf) /\
        (!n. f (NUMERAL_BIT1 n) = b1f (f n) n) /\
        (!n. f (NUMERAL_BIT2 n) = b2f (f n) n)`,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC
    (MP (INST_TYPE [Type`:'b` |-> Type`:'a`]
           (ISPEC (--`$<`--) primWFTheory.WF_RECURSION_THM))
        WF_LESS) THEN
  POP_ASSUM (STRIP_ASSUME_TAC o CONJUNCT1 o
             SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] o
             ISPEC our_M) THEN
  Q.EXISTS_TAC `f` THEN REPEAT CONJ_TAC THENL [
    ASM_SIMP_TAC bool_ss [],
    GEN_TAC THEN
    FIRST_ASSUM
      (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (REWR_CONV th)))) THEN
    SIMP_TAC bool_ss [numeral_eq] THEN AP_TAC THEN AP_TAC THEN
    SIMP_TAC bool_ss [primWFTheory.RESTRICT_DEF, NUMERAL_BIT1] THEN
    ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC],
    GEN_TAC THEN
    FIRST_ASSUM
      (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (REWR_CONV th)))) THEN
    SIMP_TAC bool_ss [numeral_eq] THEN AP_TAC THEN AP_TAC THEN
    SIMP_TAC bool_ss [primWFTheory.RESTRICT_DEF, NUMERAL_BIT2] THEN
    ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC]
  ]);

val bit_cases = prove(Term
  `!n. (n = ALT_ZERO) \/ (?b1. n = NUMERAL_BIT1 b1) \/
       (?b2. n = NUMERAL_BIT2 b2)`,
INDUCT_TAC THENL [
  SIMP_TAC bool_ss [ALT_ZERO],
  POP_ASSUM (STRIP_ASSUME_TAC) THEN POP_ASSUM SUBST_ALL_TAC THENL [
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC (Term`ALT_ZERO`) THEN
    REWRITE_TAC [numeral_suc],
    DISJ2_TAC THEN DISJ2_TAC THEN Q.EXISTS_TAC `b1` THEN
    SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, ADD_CLAUSES],
    DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `SUC b2` THEN
    SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, ADD_CLAUSES]
  ]
]);

val bit_initiality = prove(Term
  `!zf b1f b2f.
      ?!f.
        (f ALT_ZERO = zf) /\
        (!n. f (NUMERAL_BIT1 n) = b1f (f n) n) /\
        (!n. f (NUMERAL_BIT2 n) = b2f (f n) n)`,
  REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL [
    MATCH_ACCEPT_TAC bit_initiality0,
    REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    INDUCT_THEN (MATCH_MP primWFTheory.WF_INDUCTION_THM WF_LESS)
                STRIP_ASSUME_TAC THEN
    (* now do numeral cases on n *)
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (SPEC_ALL bit_cases) THENL [
      ASM_SIMP_TAC bool_ss [],
      ASM_SIMP_TAC bool_ss [] THEN AP_TAC THEN AP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC bool_ss [NUMERAL_BIT1] THEN
      ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC],
      ASM_SIMP_TAC bool_ss [] THEN AP_TAC THEN AP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC bool_ss [NUMERAL_BIT2] THEN
      ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC]
    ]
  ]);


(* now with bit initiality we can define our subtraction helper
   function.  However, before doing this it's nice to have a cases
   function for the bit structure. *)
val iBIT_cases = new_recursive_definition {
  def = Term`(iBIT_cases ALT_ZERO zf bf1 bf2 = zf) /\
             (iBIT_cases (NUMERAL_BIT1 n) zf bf1 bf2 = bf1 n) /\
             (iBIT_cases (NUMERAL_BIT2 n) zf bf1 bf2 = bf2 n)`,
  fixity = Prefix,
  name = "iBIT_cases",
  rec_axiom = bit_initiality};

(* another internal marker, this one represents a zero digit.  We can't
   avoid using this with subtraction because of the fact that when you
   subtract two big numbers that are close together, you will end up
   with a result that has a whole pile of leading zeroes.  (The
   alternative is to construct an algorithm that stops whenever it
   notices that the two arguments are equal.  This "looking ahead" would
   require a conditional rewrite, and this is not very appealing.) *)
val iDUB = new_definition("iDUB", Term`iDUB x = x + x`);

(* iSUB implements subtraction.  When the first argument (a boolean) is
   true, it corresponds to simple subtraction, when it's false, it
   corresponds to subtraction and then less another one (i.e., with a
   one being carried.  Note that iSUB's results include iDUB "zero
   digits"; these will be eliminated in a final phase of rewriting.) *)
val iSUB_DEF = new_recursive_definition {
  def = Term`
    (iSUB b ALT_ZERO x = ALT_ZERO) /\
    (iSUB b (NUMERAL_BIT1 n) x =
       (b
        => iBIT_cases x (NUMERAL_BIT1 n)
           (* BIT1 m *) (\m. iDUB (iSUB T n m))
           (* BIT2 m *) (\m. NUMERAL_BIT1 (iSUB F n m))
        |  iBIT_cases x (iDUB n)
           (* BIT1 m *) (\m. NUMERAL_BIT1 (iSUB F n m))
           (* BIT2 m *) (\m. iDUB (iSUB F n m)))) /\
    (iSUB b (NUMERAL_BIT2 n) x =
       (b
        => iBIT_cases x (NUMERAL_BIT2 n)
           (* BIT1 m *) (\m. NUMERAL_BIT1 (iSUB T n m))
           (* BIT2 m *) (\m. iDUB (iSUB T n m))
        |  iBIT_cases x (NUMERAL_BIT1 n)
           (* BIT1 m *) (\m. iDUB (iSUB T n m))
           (* BIT2 m *) (\m. NUMERAL_BIT1 (iSUB F n m))))`,
  fixity = Prefix,
  name = "iSUB_DEF",
  rec_axiom = bit_initiality};
val bit_induction = Prim_rec.prove_induction_thm bit_initiality;

val iSUB_ZERO = prove(
  Term`(!n b. iSUB b ALT_ZERO n = ALT_ZERO) /\ (!n. iSUB T n ALT_ZERO = n)`,
  SIMP_TAC bool_ss [iSUB_DEF] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `n` bit_cases) THEN
  SIMP_TAC bool_ss [iSUB_DEF, iBIT_cases]);

(* an equivalent form to the definition that doesn't need the cases
   theorem, and can thus be used by REWRITE_TAC.  To get the other to
   work you need the simplifier because it needs to do beta-reduction
   of the arguments to iBIT_cases.  Alternatively, the form of the
   arguments in iSUB_THM could be simply expressed as function composition
   without a lambda x present at all. *)
val iSUB_THM = store_thm(
  "iSUB_THM",
  Term
  `!b n m. (iSUB b ALT_ZERO x = ALT_ZERO) /\ (iSUB T n ALT_ZERO = n) /\
           (iSUB F (NUMERAL_BIT1 n) ALT_ZERO = iDUB n) /\
           (iSUB T (NUMERAL_BIT1 n) (NUMERAL_BIT1 m) =
              iDUB (iSUB T n m)) /\
           (iSUB F (NUMERAL_BIT1 n) (NUMERAL_BIT1 m) =
              NUMERAL_BIT1 (iSUB F n m)) /\
           (iSUB T (NUMERAL_BIT1 n) (NUMERAL_BIT2 m) =
              NUMERAL_BIT1 (iSUB F n m)) /\
           (iSUB F (NUMERAL_BIT1 n) (NUMERAL_BIT2 m) =
              iDUB (iSUB F n m)) /\

           (iSUB F (NUMERAL_BIT2 n) ALT_ZERO = NUMERAL_BIT1 n) /\
           (iSUB T (NUMERAL_BIT2 n) (NUMERAL_BIT1 m) =
              NUMERAL_BIT1 (iSUB T n m)) /\
           (iSUB F (NUMERAL_BIT2 n) (NUMERAL_BIT1 m) =
              iDUB (iSUB T n m)) /\
           (iSUB T (NUMERAL_BIT2 n) (NUMERAL_BIT2 m) =
              iDUB (iSUB T n m)) /\
           (iSUB F (NUMERAL_BIT2 n) (NUMERAL_BIT2 m) =
              NUMERAL_BIT1 (iSUB F n m))`,
  SIMP_TAC bool_ss [iSUB_DEF, iBIT_cases, iSUB_ZERO]);

(* rewrites for relational expressions that can be used under
   the guards of conditional operators. *)
val less_less_eqs = prove(
  Term`!n m. (n < m ==> ~(m <= n) /\ (m <= SUC n = (m = SUC n)) /\
                        ~(m + m <= n)) /\
             (n <= m ==> ~(m < n) /\ (m <= n = (m = n)) /\
                         ~(SUC m <= n))`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [
    STRIP_TAC THEN MAP_EVERY IMP_RES_TAC [LESS_LESS_EQ_TRANS, LESS_REFL],
    EQ_TAC THEN SIMP_TAC bool_ss [LESS_OR_EQ] THEN STRIP_TAC THEN
    IMP_RES_TAC LESS_LESS_SUC,
    POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`m:num`, `m`) THEN INDUCT_TAC THENL [
      SIMP_TAC bool_ss [NOT_LESS_0],
      SIMP_TAC bool_ss [GSYM NOT_LESS] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LESS_TRANS THEN Q.EXISTS_TAC `SUC m` THEN
      ASM_SIMP_TAC bool_ss [LESS_ADD_SUC]
    ],
    STRIP_TAC THEN MAP_EVERY IMP_RES_TAC [LESS_LESS_EQ_TRANS, LESS_REFL],
    EQ_TAC THEN SIMP_TAC bool_ss [LESS_EQ_REFL] THEN STRIP_TAC THEN
    IMP_RES_TAC LESS_EQUAL_ANTISYM,
    SIMP_TAC bool_ss [GSYM NOT_LESS] THEN
    ASM_SIMP_TAC bool_ss [LESS_EQ, LESS_EQ_MONO]
  ]);


val sub_facts = prove(Term
`!m. (SUC (SUC m) - m = SUC (SUC 0)) /\
     (SUC m - m = SUC 0) /\
     (m - m = 0)`,
INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [SUB_MONO_EQ, SUB_0, SUB_EQUAL_0]);

val COND_OUT_THMS = CONJ COND_RAND COND_RATOR

val SUB_elim = prove(Term
  `!n m. (n + m) - m = n`,
  GEN_TAC THEN INDUCT_THEN numTheory.INDUCTION ASSUME_TAC THEN
  ASM_SIMP_TAC bool_ss [ADD_CLAUSES, SUB_0, SUB_MONO_EQ])

(* induction over the bit structure to demonstrate that the iSUB
   function does actually implement subtraction, if the arguments are
   the "right way round" *)
val iSUB_correct = prove(
  Term`!n m. (m <= n ==> (iSUB T n m = n - m)) /\
             (m < n ==>  (iSUB F n m = n - SUC m))`,
  INDUCT_THEN bit_induction ASSUME_TAC THENL [
    SIMP_TAC bool_ss [SUB, iSUB_ZERO, ALT_ZERO],
    SIMP_TAC bool_ss [iSUB_DEF] THEN GEN_TAC THEN
    STRUCT_CASES_TAC (Q.SPEC `m` bit_cases) THENL [
      SIMP_TAC bool_ss [SUB_0, iBIT_cases, iDUB, NUMERAL_BIT1, ALT_ZERO] THEN
      SIMP_TAC bool_ss [ADD_ASSOC, SUB_elim],
      SIMP_TAC bool_ss [iBIT_cases, numeral_lt, numeral_lte] THEN
      ASM_SIMP_TAC bool_ss [NUMERAL_BIT2, NUMERAL_BIT1, PRE_SUB,
        SUB_LEFT_SUC, SUB_MONO_EQ, SUB_LEFT_ADD, SUB_RIGHT_ADD, SUB_RIGHT_SUB,
        ADD_CLAUSES, less_less_eqs, LESS_MONO_EQ, GSYM LESS_OR_EQ, iDUB,
        DOUBLE_FACTS] THEN CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts],
      ASM_SIMP_TAC bool_ss [iBIT_cases, numeral_lt, NUMERAL_BIT1,
        NUMERAL_BIT2, PRE_SUB, SUB_LEFT_SUC, SUB_MONO_EQ, SUB_LEFT_ADD,
        SUB_RIGHT_ADD, SUB_RIGHT_SUB, ADD_CLAUSES, less_less_eqs, iDUB,
        DOUBLE_FACTS, LESS_EQ_MONO] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [ADD_CLAUSES, sub_facts, COND_OUT_THMS]
    ],
    GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `m` bit_cases) THEN
    ASM_SIMP_TAC bool_ss [iBIT_cases, numeral_lte, numeral_lt, ALT_ZERO,
                          iSUB_DEF, SUB_0] THENL [
      SIMP_TAC bool_ss [sub_facts, NUMERAL_BIT2, NUMERAL_BIT1, ADD_CLAUSES,
                        SUB_MONO_EQ, SUB_0],
      ASM_SIMP_TAC bool_ss [NOT_LESS, NUMERAL_BIT1, NUMERAL_BIT2, iDUB,
        ADD_CLAUSES, SUB_MONO_EQ, INV_SUC_EQ, SUB_LEFT_SUC, SUB_RIGHT_SUB,
        SUB_LEFT_SUB, SUB_LEFT_ADD, SUB_RIGHT_ADD, less_less_eqs] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts, NUMERAL_DEF],
      ASM_SIMP_TAC bool_ss [NOT_LESS, NUMERAL_BIT1, NUMERAL_BIT2, iDUB,
        ADD_CLAUSES, SUB_MONO_EQ, INV_SUC_EQ, SUB_LEFT_SUC, SUB_RIGHT_SUB,
        SUB_LEFT_SUB, SUB_LEFT_ADD, SUB_RIGHT_ADD, less_less_eqs] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts, NUMERAL_DEF]
    ]
  ]);

val numeral_sub = store_thm(
  "numeral_sub",
  Term
  `!n m. NUMERAL (n - m) = (m < n => NUMERAL (iSUB T n m) | ZERO)`,
  SIMP_TAC bool_ss [iSUB_correct, COND_OUT_THMS,
                    REWRITE_RULE [NUMERAL_DEF] SUB_EQ_0, LESS_EQ_CASES,
                    NUMERAL_DEF, LESS_IMP_LESS_OR_EQ, GSYM NOT_LESS]);

val NOT_ZERO = prove(Term
  `!n. ~(n = 0) = (0 < n)`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC (Q.SPEC `n` (GSYM LESS_0_CASES)) THEN
  FULL_SIMP_TAC bool_ss [LESS_REFL]);

val iDUB_removal = store_thm(
  "iDUB_removal",
  Term`!n. (iDUB (NUMERAL_BIT1 n) = NUMERAL_BIT2 (iDUB n)) /\
           (iDUB (NUMERAL_BIT2 n) = NUMERAL_BIT2 (NUMERAL_BIT1 n)) /\
           (iDUB ALT_ZERO = ALT_ZERO)`,
  SIMP_TAC bool_ss [iDUB, NUMERAL_BIT2, NUMERAL_BIT1, PRE_SUB1,
                    ADD_CLAUSES, ALT_ZERO]);

(* rewriting for multiplication *)
val _ = print "Developing numeral rewrites for multiplication\n"

val numeral_mult = store_thm(
  "numeral_mult", Term
  `!n m.
     (ALT_ZERO * n = ALT_ZERO) /\ (n * ALT_ZERO = ALT_ZERO) /\
     (NUMERAL_BIT1 n * m = iZ (iDUB (n * m) + m)) /\
     (NUMERAL_BIT2 n * m = iDUB (iZ (n * m + m)))`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, iDUB, RIGHT_ADD_DISTRIB, iZ,
                    MULT_CLAUSES, ADD_CLAUSES, ALT_ZERO] THEN
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (ADD_ASSOC, ADD_SYM)));

(* numeral treatment of exponentiation *)
val _ = print "Developing numeral treatment of exponentiation\n";

(* in order to do efficient exponentiation, we need to define the
   operation of squaring.  (We can't just rewrite to n * n, because simple
   rewriting would then rewrite both arms of the multiplication independently,
   thereby doing twice as much work as necessary.) *)

val iSQR = new_definition("iSQR", Term`iSQR x = x * x`);

val numeral_exp = store_thm(
  "numeral_exp", Term
  `(!n. n EXP ALT_ZERO = NUMERAL_BIT1 ALT_ZERO) /\
   (!n m. n EXP (NUMERAL_BIT1 m) = n * iSQR (n EXP m)) /\
   (!n m. n EXP (NUMERAL_BIT2 m) = iSQR n * iSQR (n EXP m))`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, iSQR, NUMERAL_BIT2, EXP_ADD, EXP,
                    ADD_CLAUSES, ALT_ZERO, NUMERAL_DEF] THEN
  REPEAT STRIP_TAC THEN CONV_TAC (AC_CONV(MULT_ASSOC, MULT_SYM)));

(*
val _ = print "Developing numeral rewrites for division\n"

val iLOG_DEF = new_recursive_definition{
  def = Term
    `(iLOG b (NUMERAL_BIT1 n) =
      iBIT_cases n (b => 1 | 0) (\k. SUC (iLOG b n)) (\k. SUC (iLOG b n))) /\
     (iLOG b (NUMERAL_BIT2 n) =
      iBIT_cases n 1 (\k. SUC (iLOG T n)) (\k. SUC (iLOG T n)))`,
  fixity = Prefix,
  name = "iLOG_DEF",
  rec_axiom = bit_initiality};

val iLOG_THM = store_thm(
  "iLOG_THM", Term
  `(iLOG F (NUMERAL_BIT1 ALT_ZERO) = 0) /\
   (iLOG T (NUMERAL_BIT1 ALT_ZERO) = 1) /\
   (!b. iLOG b (NUMERAL_BIT2 ALT_ZERO) = 1) /\
   (!n b. iLOG b (NUMERAL_BIT1 (NUMERAL_BIT1 n)) =
          SUC (iLOG b (NUMERAL_BIT1 n))) /\
   (!n b. iLOG b (NUMERAL_BIT1 (NUMERAL_BIT2 n)) =
          SUC (iLOG b (NUMERAL_BIT2 n))) /\
   (!n b. iLOG b (NUMERAL_BIT2 (NUMERAL_BIT1 n)) =
          SUC (iLOG T (NUMERAL_BIT1 n))) /\
   (!n b. iLOG b (NUMERAL_BIT2 (NUMERAL_BIT2 n)) =
          SUC (iLOG T (NUMERAL_BIT2 n)))`,
  SIMP_TAC bool_ss [iLOG_DEF, iBIT_cases]);

fun bcases n =
  REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC [QUOTE n] bit_cases)

val iALL_ONES = new_recursive_definition {
  def = Term`(iALL_ONES ALT_ZERO = T) /\
             (iALL_ONES (NUMERAL_BIT1 n) = iALL_ONES n) /\
             (iALL_ONES (NUMERAL_BIT2 n) = F)`,
  fixity = Prefix,
  name = "iALL_ONEs",
  rec_axiom = bit_initiality};

val not_bit_0 = Q.prove
  `!n. ~(NUMERAL_BIT1 n = 0) /\ ~(NUMERAL_BIT2 n = 0)`
  (REWRITE_TAC [NUMERAL_DEF, numeral_eq]);
val LHS_CONV = RATOR_CONV o RAND_CONV

val one = prove(
  Term`1 = SUC 0`,
  REWRITE_TAC [NUMERAL_DEF, NUMERAL_BIT1, ADD_CLAUSES]);
val two = prove(
  Term`2 = SUC 1`,
  REWRITE_TAC [NUMERAL_DEF, NUMERAL_BIT2, one, ADD_CLAUSES, NUMERAL_BIT1])
(* don't use the following as a rewrite; it loops!! *)
val numbits_mult = Q.prove
  `(!n. NUMERAL_BIT1 n = 2 * n + 1) /\
   (!n. NUMERAL_BIT2 n = 2 * n + 2)`
  (SIMP_TAC bool_ss [MULT_CLAUSES, ADD_CLAUSES, two, one] THEN
   SIMP_TAC bool_ss [NUMERAL_BIT1, NUMERAL_BIT2, ADD_CLAUSES])


val MULT_LE = Q.prove
  `!n k. k * n <= k = (n = 0) \/ (n = 1) \/ (k = 0)`
  (REPEAT GEN_TAC THEN ncases "n" "n0" THEN
   SIMP_TAC bool_ss [MULT_CLAUSES, ZERO_LESS_EQ, SUC_NOT, one,
                     INV_SUC_EQ] THEN
   EQ_TAC THENL [
     CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV (GSYM ADD_0)))) THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     SIMP_TAC bool_ss [LESS_EQ_MONO_ADD_EQ, LESS_EQ_0, MULT_EQ_0] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
     STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
     SIMP_TAC bool_ss [ADD_CLAUSES, MULT_CLAUSES, LESS_EQ_REFL]
   ])

val iALL_ONES_characterised = store_thm(
  "iALL_ONES_characterised", Term
  `!n. iALL_ONES n /\ ~(n = 0) ==> (n = 2 EXP (iLOG T n) - 1)`,
  INDUCT_THEN bit_induction STRIP_ASSUME_TAC THENL [
    SIMP_TAC bool_ss [NUMERAL_DEF],
    bcases "n" THENL [
      SIMP_TAC bool_ss ([iLOG_THM, iALL_ONES, numeral_eq] @
                        exp_rwts @ sub_rwts) THEN
      REWRITE_TAC [NUMERAL_DEF],
      FULL_SIMP_TAC bool_ss [iLOG_THM, iALL_ONES, EXP', not_bit_0] THEN
      DISCH_THEN (fn iALL_ONESb1 =>
        POP_ASSUM (fn imp_thm => let
          val result = MP imp_thm iALL_ONESb1
        in
          CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV result)))
        end)) THEN
      CONV_TAC (LHS_CONV (REWR_CONV (CONJUNCT1 numbits_mult))) THEN
      SIMP_TAC bool_ss [LEFT_SUB_DISTRIB, MULT_CLAUSES, SUB_RIGHT_ADD] THEN
      SIMP_TAC bool_ss [
        GSYM (REWRITE_RULE ([COND_RAND, COND_RATOR, COND_EXPAND,
                             numeral_lte] @ sub_rwts)
              (GEN_ALL (Q.SPECL [`m`, `2`, `1`] SUB_LEFT_SUB))),
        COND_RAND, COND_RATOR, MULT_LE, numeral_distrib, numeral_eq] THEN
      STRIP_TAC THENL [
        FULL_SIMP_TAC bool_ss [two, NOT_EXP_0],
        POP_ASSUM SUBST_ALL_TAC THEN
        SIMP_TAC bool_ss (mult_rwts @ sub_rwts)
      ],
      SIMP_TAC bool_ss [iALL_ONES]
    ],
    SIMP_TAC bool_ss [iALL_ONES]
  ]);

val zero = Q.prove `0 = ZERO`  (REWRITE_TAC [NUMERAL_DEF])

val iALL_ONES_iLOG = store_thm(
  "NOT_iALL_ONES", Term
  `!n. (iALL_ONES n /\ ~(n = 0) ==> (iLOG T n = iLOG F n + 1)) /\
       (~(iALL_ONES n) ==> (iLOG T n = iLOG F n))`,
  INDUCT_THEN bit_induction STRIP_ASSUME_TAC THEN
  SIMP_TAC bool_ss [iALL_ONES, iLOG_THM, zero] THENL [
    bcases "n" THEN
    FULL_SIMP_TAC bool_ss [iALL_ONES, iLOG_THM, not_bit_0] THENL [
      SIMP_TAC bool_ss (add_rwts @ [NUMERAL_DEF, numeral_eq]),
      STRIP_TAC THEN SIMP_TAC bool_ss [ADD_CLAUSES]
    ],
    bcases "n" THEN
    FULL_SIMP_TAC bool_ss [iALL_ONES, iLOG_THM, not_bit_0]
  ]);

val lt_thm = Q.prove `!m n k c. m <= n ==> k * m <= k * n + c`
  (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
     SIMP_TAC bool_ss [MULT_CLAUSES, ZERO_LESS_EQ],
     REWRITE_TAC [MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
     REWRITE_TAC [GSYM ADD_ASSOC] THEN
     CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [ADD_SYM]))) THEN
     REWRITE_TAC [ADD_ASSOC] THEN MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO THEN
     ASM_SIMP_TAC bool_ss []
   ])

val num_less = prove(
  Term`!n. n < NUMERAL_BIT1 n /\ n < NUMERAL_BIT2 n /\
           ~(NUMERAL_BIT1 n < n) /\ ~(NUMERAL_BIT2 n < n) /\
           ~(NUMERAL_BIT1 n = n) /\ ~(NUMERAL_BIT2 n = n) /\
           ~(n = NUMERAL_BIT1 n) /\ ~(n = NUMERAL_BIT2 n)`,
  INDUCT_THEN bit_induction STRIP_ASSUME_TAC THEN
  ASM_SIMP_TAC bool_ss [numeral_lt, numeral_eq] THEN STRIP_TAC THEN
  IMP_RES_TAC LESS_ANTISYM);

fun C f x y = f y x

val COND_EXPAND' = prove(
  Term`!P Q R. (P => Q | R) = (P ==> Q) /\ (~P ==> R)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC []);
val TWO_EXP_NOT_0 = prove(
  Term`!n. ~(2 EXP n = 0)`,
  SIMP_TAC bool_ss [two, NOT_EXP_0])

val sub_cancel = prove(
  Term`!n m. (n + m) - m = n`,
  INDUCT_TAC THEN
  ASM_SIMP_TAC bool_ss [ADD_CLAUSES, SUB_EQUAL_0, SUB, COND_RAND,
                        COND_RATOR, GSYM NOT_SUC, NOT_LESS] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [LESS_EQ_ADD])

val TWO_iLOG_NOT_TOO_BIG = store_thm(
  "TWO_ILOG_NOT_TOO_BIG", Term
  `!n. 0 < n ==> 2 EXP (iLOG F n) <= n`,
  Ho_resolve.MATCH_MP_TAC COMPLETE_INDUCTION THEN REPEAT STRIP_TAC THEN
  bcases "n" THENL [
    POP_ASSUM MP_TAC THEN SIMP_TAC bool_ss [NUMERAL_DEF, LESS_REFL],
    POP_ASSUM (MP_TAC o SIMP_RULE bool_ss [NUMERAL_DEF, numeral_lt]) THEN
    bcases "b1" THENL [
      REWRITE_TAC [iLOG_THM, EXP', NUMERAL_DEF, numeral_lte],
      SIMP_TAC bool_ss [EXP, iLOG_THM] THEN
      POP_ASSUM (STRIP_ASSUME_TAC o
                 SIMP_RULE bool_ss [zero, numeral_lt, num_less] o
                 Q.SPEC `NUMERAL_BIT1 b1'`) THEN
      CONV_TAC (RAND_CONV (REWR_CONV (CONJUNCT1 numbits_mult))) THEN
      MATCH_MP_TAC lt_thm THEN ASM_REWRITE_TAC [],
      SIMP_TAC bool_ss [EXP, iLOG_THM] THEN
      POP_ASSUM (STRIP_ASSUME_TAC o
                 SIMP_RULE bool_ss [zero, numeral_lt, num_less] o
                 Q.SPEC `NUMERAL_BIT2 b2`) THEN
      CONV_TAC (RAND_CONV (REWR_CONV (CONJUNCT1 numbits_mult))) THEN
      MATCH_MP_TAC lt_thm THEN ASM_REWRITE_TAC []
    ],
    POP_ASSUM (MP_TAC o SIMP_RULE bool_ss [NUMERAL_DEF, numeral_lt]) THEN
    bcases "b2" THEN REWRITE_TAC [] THENL [
      SIMP_TAC bool_ss ([iLOG_THM, NUMERAL_DEF, numeral_lte] @ exp_rwts),
      SIMP_TAC bool_ss [iLOG_THM, EXP] THEN
      CONV_TAC (RAND_CONV (REWR_CONV (CONJUNCT2 numbits_mult))) THEN
      POP_ASSUM (STRIP_ASSUME_TAC o
                 SIMP_RULE bool_ss [zero, numeral_lt, num_less] o
                 Q.SPEC `NUMERAL_BIT1 b1`) THEN
      ASM_CASES_TAC (Term`iALL_ONES b1`) THENL [
        ((ASSUME_TAC o C MP (Q.ASSUME `iALL_ONES b1`) o
          SIMP_RULE bool_ss [iALL_ONES, not_bit_0] o
          Q.SPEC `NUMERAL_BIT1 b1`) iALL_ONES_characterised) THEN
        POP_ASSUM (CONV_TAC o RAND_CONV o LHS_CONV o RAND_CONV o
                   REWR_CONV) THEN
        SIMP_TAC bool_ss [LEFT_SUB_DISTRIB] THEN
        REWRITE_TAC mult_rwts THEN SIMP_TAC bool_ss [SUB_RIGHT_ADD] THEN
        SIMP_TAC bool_ss [MULT_LE, COND_EXPAND', COND_RAND, COND_RATOR] THEN
        SIMP_TAC bool_ss [numeral_distrib, numeral_eq, TWO_EXP_NOT_0,
                          sub_cancel, LESS_EQ_REFL],
        ASM_SIMP_TAC bool_ss [iALL_ONES_iLOG, iALL_ONES] THEN
        MATCH_MP_TAC LESS_EQ_TRANS THEN
        Q.EXISTS_TAC `2 * NUMERAL_BIT1 b1` THEN
        SIMP_TAC bool_ss [LESS_EQ_ADD] THEN
        CONV_TAC (LHS_CONV (LHS_CONV (REWR_CONV two)) THENC
                  RAND_CONV (LHS_CONV (REWR_CONV two))) THEN
        ASM_REWRITE_TAC [GSYM MULT_LESS_EQ_SUC]
      ],
      SIMP_TAC bool_ss [EXP, iLOG_THM, iALL_ONES_iLOG, iALL_ONES] THEN
      CONV_TAC (RAND_CONV (REWR_CONV (CONJUNCT2 numbits_mult))) THEN
      MATCH_MP_TAC LESS_EQ_TRANS THEN
      Q.EXISTS_TAC `2 * NUMERAL_BIT2 b2'` THEN
      SIMP_TAC bool_ss [LESS_EQ_ADD] THEN
      CONV_TAC (LHS_CONV (LHS_CONV (REWR_CONV two)) THENC
                RAND_CONV (LHS_CONV (REWR_CONV two))) THEN
      REWRITE_TAC [GSYM MULT_LESS_EQ_SUC] THEN
      POP_ASSUM (STRIP_ASSUME_TAC o
                 REWRITE_RULE [numeral_distrib, numeral_lt, zero, num_less] o
                 Q.SPEC `NUMERAL_BIT2 b2'`)
    ]
  ]);

val ONE_MOD = prove(
  Term`!p. 0 < p ==> (1 MOD p = ((p = 1) => 0 | 1))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [
    POP_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC bool_ss [MOD_ONE, one],
    STRIP_ASSUME_TAC
      (GSYM (Q.SPEC `1` (MATCH_MP DIVISION (Q.ASSUME `0 < p`)))) THEN
    FULL_SIMP_TAC bool_ss [ADD_EQ_1, MULT_EQ_1] THEN RES_TAC
  ]);

val MOD_ZERO = GEN_ALL (SIMP_RULE bool_ss [ADD_CLAUSES,
                                           GSYM RIGHT_FORALL_IMP_THM]
                        (Q.SPECL [`n`, `0`] MOD_MULT))

val PRE_SUC = prove(
  Term`!n. 0 < n ==> (SUC (PRE n) = n)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC PRE_SUC_EQ THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC);


val SIMP_ERR = HOL_ERR {message = "", origin_function = "",
                        origin_structure = ""}
val DIV_subtract_progress = prove(
  Term`!n m p. 0 < m /\ p * m <= n ==> (n DIV m = p + (n - p * m) DIV m)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQUAL_ADD THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC (GSYM (Q.SPEC `p * m + p'`
                          (MATCH_MP DIVISION (Q.ASSUME `0 < m`)))) THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] SUB_elim] THEN
  RULE_ASSUM_TAC
    (ONCE_REWRITE_RULE [GSYM (MATCH_MP MOD_PLUS (Q.ASSUME `0 < m`))]) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE [MATCH_MP MOD_ZERO (Q.ASSUME `0 < m`), ADD_CLAUSES,
                   MATCH_MP MOD_MOD (Q.ASSUME `0 < m`)]) THEN
  MATCH_MP_TAC (SIMP_RULE bool_ss [EQ_IMP_THM] MULT_MONO_EQ) THEN
  Q.EXISTS_TAC `PRE m` THEN ASM_SIMP_TAC bool_ss [PRE_SUC] THEN
  CONV_TAC (LHS_CONV (REWR_CONV MULT_SYM)) THEN
  MATCH_MP_TAC (SIMP_RULE bool_ss [EQ_IMP_THM] EQ_MONO_ADD_EQ) THEN
  Q.EXISTS_TAC `p' MOD m` THEN
  ASM_SIMP_TAC bool_ss [LEFT_ADD_DISTRIB, GSYM ADD_ASSOC] THEN
  CONV_TAC (LHS_CONV (LHS_CONV (REWR_CONV MULT_SYM))) THEN
  CONV_TAC (LHS_CONV (REWR_CONV ADD_SYM) THENC
            RAND_CONV (REWR_CONV ADD_SYM)) THEN
  SIMP_TAC bool_ss [EQ_MONO_ADD_EQ] THEN
  STRIP_ASSUME_TAC (Q.SPEC `p'`
                    (MATCH_MP DIVISION (Q.ASSUME `0 < m`))) THEN
  CONV_TAC (RAND_CONV (LHS_CONV (REWR_CONV MULT_SYM))) THEN
  FIRST_ASSUM ACCEPT_TAC);

(* val numeral_div = store_thm(
  "numeral_div", Term
  `!n m. 0 < m ==>
         (n DIV m = (n < m
                     => 0
                     |  let v = iLOG F n - iLOG F m in
                        let expv = 2 EXP v in
                        m * expv <= n
                        => expv + ((n - m * expv) DIV m)
                        |  let v' = v - 1 in
                           let expv' = 2 EXP v' in
                           (expv' + (n - m * expv') DIV m)))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [
    STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (Q.ASSUME `0 < m`))) THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC (Q.SPEC `n DIV m` num_CASES)
    THENL [
      REFL_TAC,
      FULL_SIMP_TAC bool_ss [NOT_SUC, MULT_CLAUSES] THEN
      Q.SUBGOAL_THEN `~(n < m)` (fn th => ASSUME_TAC th THEN RES_TAC) THEN
      SIMP_TAC bool_ss [NOT_LESS] THEN FIRST_ASSUM SUBST_ALL_TAC THEN
      CONV_TAC (RAND_CONV (LHS_CONV (REWR_CONV ADD_SYM))) THEN
      REWRITE_TAC [GSYM ADD_ASSOC, LESS_EQ_ADD]
    ],
    SIMP_TAC bool_ss [LET_DEF] THEN COND_CASES_TAC THENL [
      ASM_SIMP_TAC bool_ss [ONCE_REWRITE_RULE [MULT_SYM]
                            DIV_subtract_progress],
      ALL_TAC
    ]
  ]); *)


*)

val _ = export_theory();
