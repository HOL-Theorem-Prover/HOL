(*---------------------------------------------------------------------------

   Development of a theory of numerals, including rewrite theorems for
   the basic arithmetic operations and relations.

       Michael Norrish, December 1998

   Inspired by a similar development done by John Harrison for his
   HOL Light theorem prover.

 ---------------------------------------------------------------------------*)


(* for interactive development of this theory; evaluate the following
   commands before trying to evaluate the ML that follows.

   fun mload s = (print ("Loading "^s^"\n"); load s);
   app mload ["simpLib", "boolSimps", "arithmeticTheory", "QLib",
              "Rsyntax", "mesonLib"];
*)

open HolKernel boolLib arithmeticTheory simpLib Parse Prim_rec;

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
and PRE           = prim_recTheory.PRE
and WF_LESS       = prim_recTheory.WF_LESS;

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
   (!n. n >= 0 = T) /\ (!n. 0 >= n = (n = 0)) /\
   (!n m. NUMERAL n >= NUMERAL m = m <= n) /\
   (!n. ODD (NUMERAL n) = ODD n) /\ (!n. EVEN (NUMERAL n) = EVEN n) /\
   ~ODD 0 /\ EVEN 0`,
  SIMP_TAC bool_ss [NUMERAL_DEF, GREATER_DEF, iZ, GREATER_OR_EQ,
                    LESS_OR_EQ, EQ_IMP_THM, DISJ_IMP_THM, ADD_CLAUSES,
                    ALT_ZERO, MULT_CLAUSES, EXP, PRE, NOT_LESS_0, SUB_0,
                    NUMERAL_BIT1, NUMERAL_BIT2, ODD, EVEN] THEN
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
    (ALT_ZERO < NUMERAL_BIT1 n = T) /\ 
    (ALT_ZERO < NUMERAL_BIT2 n = T) /\
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
         (NUMERAL_BIT1 n <= ALT_ZERO = F) /\ 
         (NUMERAL_BIT2 n <= ALT_ZERO = F) /\
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

(* our measure function *)
val our_M = Term
 `\f a. if a = ALT_ZERO then (zf:'a) else
        if (?n. (a = NUMERAL_BIT1 n))
          then (b1f:num->'a->'a)
                  (@n. a = NUMERAL_BIT1 n) (f (@n. a = NUMERAL_BIT1 n))
          else b2f  (@n. a = NUMERAL_BIT2 n) (f (@n. a = NUMERAL_BIT2 n))`;


fun AP_TAC (asl, g) =
  let val _ = is_eq g orelse raise Fail "Goal not an equality"
      val (lhs, rhs) = dest_eq g
      val (lf, la) = dest_comb lhs handle _ =>
                       raise Fail "lhs must be an application"
      val (rf, ra) = dest_comb rhs handle _ =>
                       raise Fail "rhs must be an application"
  in
      if (term_eq lf rf) then AP_TERM_TAC (asl, g) else
      if (term_eq la ra) then AP_THM_TAC (asl, g) else
      raise Fail "One of function or argument must be equal"
  end

val APn_TAC = REPEAT AP_TAC;


val bit_initiality = store_thm(
  "bit_initiality",
  Term
  `!zf b1f b2f.
      ?f.
        (f ALT_ZERO = zf) /\
        (!n. f (NUMERAL_BIT1 n) = b1f n (f n)) /\
        (!n. f (NUMERAL_BIT2 n) = b2f n (f n))`,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC
    (MP (INST_TYPE [Type.beta |-> Type.alpha]
           (ISPEC (--`$<`--) relationTheory.WF_RECURSION_THM))
        WF_LESS) THEN
  POP_ASSUM (STRIP_ASSUME_TAC o CONJUNCT1 o
             SIMP_RULE bool_ss [EXISTS_UNIQUE_DEF] o
             ISPEC our_M) THEN
  Q.EXISTS_TAC `f` THEN REPEAT CONJ_TAC THENL [
    ASM_SIMP_TAC bool_ss [],
    GEN_TAC THEN
    FIRST_ASSUM (fn th => CONV_TAC (LHS_CONV (REWR_CONV th))) THEN
    SIMP_TAC bool_ss [numeral_eq] THEN AP_TAC THEN
    SIMP_TAC bool_ss [relationTheory.RESTRICT_DEF, NUMERAL_BIT1] THEN
    ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC],
    GEN_TAC THEN
    FIRST_ASSUM (fn th => CONV_TAC (LHS_CONV (REWR_CONV th))) THEN
    SIMP_TAC bool_ss [numeral_eq] THEN AP_TAC THEN
    SIMP_TAC bool_ss [relationTheory.RESTRICT_DEF, NUMERAL_BIT2] THEN
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

val old_style_bit_initiality = prove(Term
  `!zf b1f b2f.
      ?!f.
        (f ALT_ZERO = zf) /\
        (!n. f (NUMERAL_BIT1 n) = b1f (f n) n) /\
        (!n. f (NUMERAL_BIT2 n) = b2f (f n) n)`,
  REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL [
    STRIP_ASSUME_TAC
      (Q.SPECL [`zf`, `\n a. b1f a n`, `\n a. b2f a n`] bit_initiality) THEN
    RULE_ASSUM_TAC BETA_RULE THEN mesonLib.ASM_MESON_TAC [],
    REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    INDUCT_THEN (MATCH_MP relationTheory.WF_INDUCTION_THM WF_LESS)
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
  name = "iSUB_DEF",
  rec_axiom = bit_initiality};

val bit_induction = save_thm
  ("bit_induction", Prim_rec.prove_induction_thm old_style_bit_initiality);

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
  `!n m. NUMERAL (n - m) = (m < n => NUMERAL (iSUB T n m) | 0)`,
  SIMP_TAC bool_ss [iSUB_correct, COND_OUT_THMS,
                    REWRITE_RULE [NUMERAL_DEF] SUB_EQ_0, LESS_EQ_CASES,
                    NUMERAL_DEF, LESS_IMP_LESS_OR_EQ, GSYM NOT_LESS]);

val NOT_ZERO = arithmeticTheory.NOT_ZERO_LT_ZERO;

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

val _ = print "Even-ness and odd-ness of numerals\n"

val numeral_evenodd = store_thm(
  "numeral_evenodd",
  Term`!n. EVEN ALT_ZERO /\ EVEN (NUMERAL_BIT2 n) /\ ~EVEN (NUMERAL_BIT1 n) /\
           ~ODD ALT_ZERO /\ ~ODD (NUMERAL_BIT2 n) /\ ODD (NUMERAL_BIT1 n)`,
  SIMP_TAC bool_ss [NUMERAL_BIT1, ALT_ZERO, NUMERAL_BIT2, ADD_CLAUSES,
                    EVEN, ODD, EVEN_ADD, ODD_ADD]);


val numeral_fact = store_thm(
  "numeral_fact",
  Term `(FACT 0 = 1) /\
        (!n. FACT (NUMERAL (NUMERAL_BIT1 n)) =
                  (NUMERAL (NUMERAL_BIT1 n)) *
                  FACT (PRE (NUMERAL (NUMERAL_BIT1 n)))) /\
        (!n. FACT (NUMERAL (NUMERAL_BIT2 n)) =
                  (NUMERAL (NUMERAL_BIT2 n)) *
                  FACT (NUMERAL (NUMERAL_BIT1 n)))`,
 REPEAT STRIP_TAC THEN REWRITE_TAC [FACT] THEN
 (STRIP_ASSUME_TAC (SPEC (Term`n:num`) num_CASES) THENL [
    ALL_TAC,
    POP_ASSUM SUBST_ALL_TAC
  ] THEN ASM_REWRITE_TAC[FACT,PRE,NOT_SUC, NUMERAL_DEF,
                         NUMERAL_BIT1, NUMERAL_BIT2, ADD_CLAUSES]));


val numeral_funpow = store_thm(
  "numeral_funpow",
  Term `(FUNPOW f 0 x = x) /\
        (FUNPOW f (NUMERAL (NUMERAL_BIT1 n)) x =
          FUNPOW f (PRE (NUMERAL (NUMERAL_BIT1 n))) (f x)) /\
        (FUNPOW f (NUMERAL (NUMERAL_BIT2 n)) x =
          FUNPOW f (NUMERAL (NUMERAL_BIT1 n)) (f x))`,
 REPEAT STRIP_TAC THEN REWRITE_TAC [FUNPOW] THEN
 (STRIP_ASSUME_TAC (SPEC (Term`n:num`) num_CASES) THENL [
    ALL_TAC,
    POP_ASSUM SUBST_ALL_TAC
  ] THEN  ASM_REWRITE_TAC[FUNPOW,PRE,ADD_CLAUSES, NUMERAL_DEF,
                          NUMERAL_BIT1, NUMERAL_BIT2]));

val numeral_MIN = store_thm(
  "numeral_MIN",
  ``(MIN 0 x = 0) /\
    (MIN x 0 = 0) /\
    (MIN (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then x else y))``,
  REWRITE_TAC [MIN_0] THEN
  REWRITE_TAC [MIN_DEF, NUMERAL_DEF]);

val numeral_MAX = store_thm(
  "numeral_MAX",
  ``(MAX 0 x = x) /\
    (MAX x 0 = x) /\
    (MAX (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then y else x))``,
  REWRITE_TAC [MAX_0] THEN
  REWRITE_TAC [MAX_DEF, NUMERAL_DEF]);

val _ = export_theory();
