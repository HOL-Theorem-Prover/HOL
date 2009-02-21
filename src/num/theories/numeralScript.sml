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
   app mload ["simpLib", "boolSimps", "arithmeticTheory", "Q",
              "mesonLib", "metisLib", "whileTheory",
              "pairSyntax", "combinSyntax"];
*)

open HolKernel boolLib arithmeticTheory simpLib Parse Prim_rec metisLib
     BasicProvers;

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
  Term `(SUC ZERO = BIT1 ZERO) /\
        (!n. SUC (BIT1 n) = BIT2 n) /\
        (!n. SUC (BIT2 n) = BIT1 (SUC n))`,
  SIMP_TAC bool_ss [BIT1, BIT2, ALT_ZERO, ADD_CLAUSES]);


(*---------------------------------------------------------------------------*)
(* Internal markers. Throughout this theory, we will be using various        *)
(* internal markers that represent some intermediate result within an        *)
(* algorithm.  All such markers are constants with names that have           *)
(* leading i's                                                               *)
(*---------------------------------------------------------------------------*)

val iZ = new_definition("iZ", ``iZ (x:num) = x``);

val iiSUC = new_definition("iiSUC", ``iiSUC n = SUC (SUC n)``);

val numeral_distrib = store_thm(
  "numeral_distrib", Term
  `(!n. 0 + n = n) /\ (!n. n + 0 = n) /\
   (!n m. NUMERAL n + NUMERAL m = NUMERAL (iZ (n + m))) /\
   (!n. 0 * n = 0) /\ (!n. n * 0 = 0) /\
   (!n m. NUMERAL n * NUMERAL m = NUMERAL (n * m)) /\
   (!n. 0 - n = 0) /\ (!n. n - 0 = n) /\
   (!n m. NUMERAL n - NUMERAL m = NUMERAL (n - m)) /\
   (!n. 0 EXP (NUMERAL (BIT1 n)) = 0) /\
   (!n. 0 EXP (NUMERAL (BIT2 n)) = 0) /\
   (!n. n EXP 0 = 1) /\
   (!n m. (NUMERAL n) EXP (NUMERAL m) = NUMERAL (n EXP m)) /\
   (SUC 0 = 1) /\
   (!n. SUC(NUMERAL n) = NUMERAL (SUC n)) /\
   (PRE 0 = 0) /\
   (!n. PRE(NUMERAL n) = NUMERAL (PRE n)) /\
   (!n. (NUMERAL n = 0) = (n = ZERO)) /\
   (!n. (0 = NUMERAL n) = (n = ZERO)) /\
   (!n m. (NUMERAL n = NUMERAL m) = (n=m)) /\
   (!n. n < 0 = F) /\ (!n. 0 < NUMERAL n = ZERO < n) /\
   (!n m. NUMERAL n < NUMERAL m  = n<m)  /\
   (!n. 0 > n = F) /\ (!n. NUMERAL n > 0 = ZERO < n) /\
   (!n m. NUMERAL n > NUMERAL m  = m<n)  /\
   (!n. 0 <= n = T) /\ (!n. NUMERAL n <= 0 = n <= ZERO) /\
   (!n m. NUMERAL n <= NUMERAL m = n<=m) /\
   (!n. n >= 0 = T) /\ (!n. 0 >= n = (n = 0)) /\
   (!n m. NUMERAL n >= NUMERAL m = m <= n) /\
   (!n. ODD (NUMERAL n) = ODD n) /\ (!n. EVEN (NUMERAL n) = EVEN n) /\
   ~ODD 0 /\ EVEN 0`,
  SIMP_TAC bool_ss [NUMERAL_DEF, GREATER_DEF, iZ, GREATER_OR_EQ,
                    LESS_OR_EQ, EQ_IMP_THM, DISJ_IMP_THM, ADD_CLAUSES,
                    ALT_ZERO, MULT_CLAUSES, EXP, PRE, NOT_LESS_0, SUB_0,
                    BIT1, BIT2, ODD, EVEN] THEN
  mesonLib.MESON_TAC [LESS_0_CASES]);

val numeral_iisuc = store_thm(
  "numeral_iisuc", Term
  `(iiSUC ZERO = BIT2 ZERO) /\
   (iiSUC (BIT1 n) = BIT1 (SUC n)) /\
   (iiSUC (BIT2 n) = BIT2 (SUC n))`,
  SIMP_TAC bool_ss [BIT1, BIT2, iiSUC, ALT_ZERO, ADD_CLAUSES]);


(*---------------------------------------------------------------------------*)
(* The following addition algorithm makes use of internal markers iZ and     *)
(* iiSUC.                                                                    *)
(*                                                                           *)
(* iZ is used to mark the place where the algorithm is currently working.    *)
(* Without a rule such as the fourth below would give the rewriter a chance  *)
(* to rewrite away an addition under a SUC, which we don't want.             *)
(*                                                                           *)
(* SUC is used as an internal marker to represent carrying one, while        *)
(* iiSUC is used to represent carrying two (necessary with our               *)
(* formulation of numerals).                                                 *)
(*---------------------------------------------------------------------------*)

val numeral_add = store_thm(
  "numeral_add",
  Term
  `!n m.
   (iZ (ZERO + n) = n) /\
   (iZ (n + ZERO) = n) /\
   (iZ (BIT1 n + BIT1 m) = BIT2 (iZ (n + m))) /\
   (iZ (BIT1 n + BIT2 m) = BIT1 (SUC (n + m))) /\
   (iZ (BIT2 n + BIT1 m) = BIT1 (SUC (n + m))) /\
   (iZ (BIT2 n + BIT2 m) = BIT2 (SUC (n + m))) /\
   (SUC (ZERO + n) = SUC n) /\
   (SUC (n + ZERO) = SUC n) /\
   (SUC (BIT1 n + BIT1 m) = BIT1 (SUC (n + m))) /\
   (SUC (BIT1 n + BIT2 m) = BIT2 (SUC (n + m))) /\
   (SUC (BIT2 n + BIT1 m) = BIT2 (SUC (n + m))) /\
   (SUC (BIT2 n + BIT2 m) = BIT1 (iiSUC (n + m))) /\
   (iiSUC (ZERO + n) = iiSUC n) /\
   (iiSUC (n + ZERO) = iiSUC n) /\
   (iiSUC (BIT1 n + BIT1 m) = BIT2 (SUC (n + m))) /\
   (iiSUC (BIT1 n + BIT2 m) = BIT1 (iiSUC (n + m))) /\
   (iiSUC (BIT2 n + BIT1 m) = BIT1 (iiSUC (n + m))) /\
   (iiSUC (BIT2 n + BIT2 m) = BIT2 (iiSUC (n + m)))`,
  SIMP_TAC bool_ss [BIT1, BIT2, iZ, iiSUC,ADD_CLAUSES, INV_SUC_EQ, ALT_ZERO] THEN
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV(ADD_ASSOC, ADD_SYM)));

(*---------------------------------------------------------------------------*)
(* rewrites needed for addition                                              *)
(*---------------------------------------------------------------------------*)

val add_rwts = [numeral_distrib, numeral_add, numeral_suc, numeral_iisuc]

val numeral_proof_rwts = [BIT1, BIT2, INV_SUC_EQ,
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
    ((ZERO = BIT1 n) = F) /\
    ((BIT1 n = ZERO) = F) /\
    ((ZERO = BIT2 n) = F) /\
    ((BIT2 n = ZERO) = F) /\
    ((BIT1 n = BIT2 m) = F) /\
    ((BIT2 n = BIT1 m) = F) /\
    ((BIT1 n = BIT1 m) = (n = m)) /\
    ((BIT2 n = BIT2 m) = (n = m))`,
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
    (ZERO < BIT1 n = T) /\
    (ZERO < BIT2 n = T) /\
    (n < ZERO = F) /\
    (BIT1 n < BIT1 m = n < m) /\
    (BIT2 n < BIT2 m = n < m) /\
    (BIT1 n < BIT2 m = ~(m < n)) /\
    (BIT2 n < BIT1 m = n < m)`,
  SIMP_TAC bool_ss (DOUBLE_FACTS::LESS_MONO_EQ::numeral_proof_rwts));

(*---------------------------------------------------------------------------*)
(* I've kept this rewrite entirely independent of the above.  I don't if     *)
(* this is a good idea or not.                                               *)
(*---------------------------------------------------------------------------*)

val numeral_lte = store_thm(
  "numeral_lte", Term
  `!n m. (ZERO <= n = T) /\
         (BIT1 n <= ZERO = F) /\
         (BIT2 n <= ZERO = F) /\
         (BIT1 n <= BIT1 m = n <= m) /\
         (BIT1 n <= BIT2 m = n <= m) /\
         (BIT2 n <= BIT1 m = ~(m <= n)) /\
         (BIT2 n <= BIT2 m = n <= m)`,
  SIMP_TAC bool_ss ([DOUBLE_FACTS, LESS_MONO_EQ, LESS_EQ_MONO] @
                    (map (REWRITE_RULE [NUMERAL_DEF])
                         [ZERO_LESS_EQ, NOT_SUC_LESS_EQ_0, NOT_LESS]) @
                    numeral_proof_rwts) THEN
  SIMP_TAC bool_ss [GSYM NOT_LESS]);

val _ = print "Developing numeral rewrites for subtraction\n";
val _ = print "   (includes initiality theorem for bit functions)\n";

val numeral_pre = store_thm(
  "numeral_pre",
  --`(PRE ZERO = ZERO) /\
     (PRE (BIT1 ZERO) = ZERO) /\
     (!n. PRE (BIT1 (BIT1 n)) = BIT2 (PRE (BIT1 n))) /\
     (!n. PRE (BIT1 (BIT2 n)) = BIT2 (BIT1 n)) /\
     (!n. PRE (BIT2 n) = BIT1 n)`--,
  SIMP_TAC bool_ss [BIT1, BIT2, PRE, PRE_ADD,
                    ADD_CLAUSES, ADD_ASSOC, PRE, ALT_ZERO]);

(*---------------------------------------------------------------------------*)
(* We could just go on and prove similar rewrites for subtraction, but       *)
(* they get a bit inefficient because every iteration of the rewriting       *)
(* ends up checking whether or not x < y.  To get around this, we prove      *)
(* initiality for our BIT functions and ZERO, and then define a function     *)
(* which implements bitwise subtraction for x and y, assuming that x is      *)
(* at least as big as y.                                                     *)
(*---------------------------------------------------------------------------*)

(* Measure function for WF recursion construction *)
val our_M = Term
 `\f a. if a = ZERO then (zf:'a) else
        if (?n. (a = BIT1 n))
          then (b1f:num->'a->'a)
                  (@n. a = BIT1 n) (f (@n. a = BIT1 n))
          else b2f  (@n. a = BIT2 n) (f (@n. a = BIT2 n))`;


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
        (f ZERO = zf) /\
        (!n. f (BIT1 n) = b1f n (f n)) /\
        (!n. f (BIT2 n) = b2f n (f n))`,
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
    SIMP_TAC bool_ss [relationTheory.RESTRICT_DEF, BIT1] THEN
    ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC],
    GEN_TAC THEN
    FIRST_ASSUM (fn th => CONV_TAC (LHS_CONV (REWR_CONV th))) THEN
    SIMP_TAC bool_ss [numeral_eq] THEN AP_TAC THEN
    SIMP_TAC bool_ss [relationTheory.RESTRICT_DEF, BIT2] THEN
    ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC]
  ]);

val bit_cases = prove(Term
  `!n. (n = ZERO) \/ (?b1. n = BIT1 b1) \/ (?b2. n = BIT2 b2)`,
INDUCT_TAC THENL [
  SIMP_TAC bool_ss [ALT_ZERO],
  POP_ASSUM (STRIP_ASSUME_TAC) THEN POP_ASSUM SUBST_ALL_TAC THENL [
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC (Term`ZERO`) THEN
    REWRITE_TAC [numeral_suc],
    DISJ2_TAC THEN DISJ2_TAC THEN Q.EXISTS_TAC `b1` THEN
    SIMP_TAC bool_ss [BIT1, BIT2, ADD_CLAUSES],
    DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `SUC b2` THEN
    SIMP_TAC bool_ss [BIT1, BIT2, ADD_CLAUSES]
  ]
]);

val old_style_bit_initiality = prove(Term
  `!zf b1f b2f.
      ?!f.
        (f ZERO = zf) /\
        (!n. f (BIT1 n) = b1f (f n) n) /\
        (!n. f (BIT2 n) = b2f (f n) n)`,
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
      FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC bool_ss [BIT1] THEN
      ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC],
      ASM_SIMP_TAC bool_ss [] THEN AP_TAC THEN AP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN SIMP_TAC bool_ss [BIT2] THEN
      ONCE_REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [LESS_ADD_SUC]
    ]
  ]);


(*---------------------------------------------------------------------------*)
(* Now with bit initiality we can define our subtraction helper              *)
(* function.  However, before doing this it's nice to have a cases           *)
(* function for the bit structure.                                           *)
(*---------------------------------------------------------------------------*)

val iBIT_cases = new_recursive_definition {
  def = Term`(iBIT_cases ZERO zf bf1 bf2 = zf) /\
             (iBIT_cases (BIT1 n) zf bf1 bf2 = bf1 n) /\
             (iBIT_cases (BIT2 n) zf bf1 bf2 = bf2 n)`,
  name = "iBIT_cases",
  rec_axiom = bit_initiality};

(*---------------------------------------------------------------------------*)
(* Another internal marker, this one represents a zero digit.  We can't      *)
(* avoid using this with subtraction because of the fact that when you       *)
(* subtract two big numbers that are close together, you will end up         *)
(*   with a result that has a whole pile of leading zeroes.  (The            *)
(*   alternative is to construct an algorithm that stops whenever it         *)
(*   notices that the two arguments are equal.  This "looking ahead" would   *)
(*   require a conditional rewrite, and this is not very appealing.)         *)
(*---------------------------------------------------------------------------*)

val iDUB = new_definition("iDUB", Term`iDUB x = x + x`);

(*---------------------------------------------------------------------------*)
(* iSUB implements subtraction.  When the first argument (a boolean) is      *)
(* true, it corresponds to simple subtraction, when it's false, it           *)
(* corresponds to subtraction and then less another one (i.e., with a        *)
(* one being carried.  Note that iSUB's results include iDUB "zero           *)
(* digits"; these will be eliminated in a final phase of rewriting.)         *)
(*---------------------------------------------------------------------------*)

val iSUB_DEF = new_recursive_definition {
  def = Term`
    (iSUB b ZERO x = ZERO) /\
    (iSUB b (BIT1 n) x =
       if b
        then iBIT_cases x (BIT1 n)
             (* BIT1 m *) (\m. iDUB (iSUB T n m))
             (* BIT2 m *) (\m. BIT1 (iSUB F n m))
        else iBIT_cases x (iDUB n)
             (* BIT1 m *) (\m. BIT1 (iSUB F n m))
             (* BIT2 m *) (\m. iDUB (iSUB F n m))) /\
    (iSUB b (BIT2 n) x =
       if b
        then iBIT_cases x (BIT2 n)
             (* BIT1 m *) (\m. BIT1 (iSUB T n m))
             (* BIT2 m *) (\m. iDUB (iSUB T n m))
        else iBIT_cases x (BIT1 n)
             (* BIT1 m *) (\m. iDUB (iSUB T n m))
             (* BIT2 m *) (\m. BIT1 (iSUB F n m)))`,
  name = "iSUB_DEF",
  rec_axiom = bit_initiality};

val bit_induction = save_thm
  ("bit_induction",
   Prim_rec.prove_induction_thm old_style_bit_initiality);

val iSUB_ZERO = prove(
  Term`(!n b. iSUB b ZERO n = ZERO) /\
       (!n.   iSUB T n ZERO = n)`,
  SIMP_TAC bool_ss [iSUB_DEF] THEN GEN_TAC THEN
  STRUCT_CASES_TAC (Q.SPEC `n` bit_cases) THEN
  SIMP_TAC bool_ss [iSUB_DEF, iBIT_cases]);

(*---------------------------------------------------------------------------*)
(* An equivalent form to the definition that doesn't need the cases theorem, *)
(* and can thus be used by REWRITE_TAC.  To get the other to work you need   *)
(* the simplifier because it needs to do beta-reduction of the arguments to  *)
(* iBIT_cases.  Alternatively, the form of the arguments in iSUB_THM could   *)
(* be simply expressed as function composition without a lambda x present    *)
(* at all.                                                                   *)
(*---------------------------------------------------------------------------*)

val iSUB_THM = store_thm(
  "iSUB_THM",
  Term
  `!b n m. (iSUB b ZERO x = ZERO) /\
           (iSUB T n ZERO = n) /\
           (iSUB F (BIT1 n) ZERO = iDUB n) /\
           (iSUB T (BIT1 n) (BIT1 m) = iDUB (iSUB T n m)) /\
           (iSUB F (BIT1 n) (BIT1 m) = BIT1 (iSUB F n m)) /\
           (iSUB T (BIT1 n) (BIT2 m) = BIT1 (iSUB F n m)) /\
           (iSUB F (BIT1 n) (BIT2 m) = iDUB (iSUB F n m)) /\

           (iSUB F (BIT2 n) ZERO = BIT1 n) /\
           (iSUB T (BIT2 n) (BIT1 m) = BIT1 (iSUB T n m)) /\
           (iSUB F (BIT2 n) (BIT1 m) = iDUB (iSUB T n m)) /\
           (iSUB T (BIT2 n) (BIT2 m) = iDUB (iSUB T n m)) /\
           (iSUB F (BIT2 n) (BIT2 m) = BIT1 (iSUB F n m))`,
  SIMP_TAC bool_ss [iSUB_DEF, iBIT_cases, iSUB_ZERO]);

(*---------------------------------------------------------------------------*)
(* Rewrites for relational expressions that can be used under the guards of  *)
(* conditional operators.                                                    *)
(*---------------------------------------------------------------------------*)

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

(*---------------------------------------------------------------------------*)
(* Induction over the bit structure to demonstrate that the iSUB function    *)
(* does actually implement subtraction, if the arguments are the             *)
(* "right way round"                                                         *)
(*---------------------------------------------------------------------------*)

val iSUB_correct = prove(
  Term`!n m. (m <= n ==> (iSUB T n m = n - m)) /\
             (m < n ==>  (iSUB F n m = n - SUC m))`,
  INDUCT_THEN bit_induction ASSUME_TAC THENL [
    SIMP_TAC bool_ss [SUB, iSUB_ZERO, ALT_ZERO],
    SIMP_TAC bool_ss [iSUB_DEF] THEN GEN_TAC THEN
    STRUCT_CASES_TAC (Q.SPEC `m` bit_cases) THENL [
      SIMP_TAC bool_ss [SUB_0, iBIT_cases, iDUB, BIT1, ALT_ZERO] THEN
      SIMP_TAC bool_ss [ADD_ASSOC, SUB_elim],
      SIMP_TAC bool_ss [iBIT_cases, numeral_lt, numeral_lte] THEN
      ASM_SIMP_TAC bool_ss [BIT2, BIT1, PRE_SUB,
        SUB_LEFT_SUC, SUB_MONO_EQ, SUB_LEFT_ADD, SUB_RIGHT_ADD, SUB_RIGHT_SUB,
        ADD_CLAUSES, less_less_eqs, LESS_MONO_EQ, GSYM LESS_OR_EQ, iDUB,
        DOUBLE_FACTS] THEN CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts],
      ASM_SIMP_TAC bool_ss [iBIT_cases, numeral_lt, BIT1,
        BIT2, PRE_SUB, SUB_LEFT_SUC, SUB_MONO_EQ, SUB_LEFT_ADD,
        SUB_RIGHT_ADD, SUB_RIGHT_SUB, ADD_CLAUSES, less_less_eqs, iDUB,
        DOUBLE_FACTS, LESS_EQ_MONO] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [ADD_CLAUSES, sub_facts, COND_OUT_THMS]
    ],
    GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `m` bit_cases) THEN
    ASM_SIMP_TAC bool_ss [iBIT_cases, numeral_lte, numeral_lt, ALT_ZERO,
                          iSUB_DEF, SUB_0] THENL [
      SIMP_TAC bool_ss [sub_facts, BIT2, BIT1, ADD_CLAUSES,
                        SUB_MONO_EQ, SUB_0],
      ASM_SIMP_TAC bool_ss [NOT_LESS, BIT1, BIT2, iDUB,
        ADD_CLAUSES, SUB_MONO_EQ, INV_SUC_EQ, SUB_LEFT_SUC, SUB_RIGHT_SUB,
        SUB_LEFT_SUB, SUB_LEFT_ADD, SUB_RIGHT_ADD, less_less_eqs] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts, NUMERAL_DEF],
      ASM_SIMP_TAC bool_ss [NOT_LESS, BIT1, BIT2, iDUB,
        ADD_CLAUSES, SUB_MONO_EQ, INV_SUC_EQ, SUB_LEFT_SUC, SUB_RIGHT_SUB,
        SUB_LEFT_SUB, SUB_LEFT_ADD, SUB_RIGHT_ADD, less_less_eqs] THEN
      CONJ_TAC THEN
      SIMP_TAC bool_ss [COND_OUT_THMS, ADD_CLAUSES, sub_facts, NUMERAL_DEF]
    ]
  ]);

val numeral_sub = store_thm(
  "numeral_sub",
  Term
  `!n m. NUMERAL (n - m) = if m < n then NUMERAL (iSUB T n m) else 0`,
  SIMP_TAC bool_ss [iSUB_correct, COND_OUT_THMS,
                    REWRITE_RULE [NUMERAL_DEF] SUB_EQ_0, LESS_EQ_CASES,
                    NUMERAL_DEF, LESS_IMP_LESS_OR_EQ, GSYM NOT_LESS]);

val NOT_ZERO = arithmeticTheory.NOT_ZERO_LT_ZERO;

val iDUB_removal = store_thm(
  "iDUB_removal",
  Term`!n. (iDUB (BIT1 n) = BIT2 (iDUB n)) /\
           (iDUB (BIT2 n) = BIT2 (BIT1 n)) /\
           (iDUB ZERO = ZERO)`,
  SIMP_TAC bool_ss [iDUB, BIT2, BIT1, PRE_SUB1,
                    ADD_CLAUSES, ALT_ZERO]);

val _ = print "Developing numeral rewrites for multiplication\n"

val numeral_mult = store_thm(
  "numeral_mult", Term
  `!n m.
     (ZERO * n = ZERO) /\
     (n * ZERO = ZERO) /\
     (BIT1 n * m = iZ (iDUB (n * m) + m)) /\
     (BIT2 n * m = iDUB (iZ (n * m + m)))`,
  SIMP_TAC bool_ss [BIT1, BIT2, iDUB, RIGHT_ADD_DISTRIB, iZ,
                    MULT_CLAUSES, ADD_CLAUSES, ALT_ZERO] THEN
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (ADD_ASSOC, ADD_SYM)));


val _ = print "Developing numeral treatment of exponentiation\n";

(*---------------------------------------------------------------------------*)
(* In order to do efficient exponentiation, we need to define the operation  *)
(* of squaring.  (We can't just rewrite to n * n, because simple rewriting   *)
(* would then rewrite both arms of the multiplication independently, thereby *)
(* doing twice as much work as necessary.)                                   *)
(*---------------------------------------------------------------------------*)

val iSQR = new_definition("iSQR", Term`iSQR x = x * x`);

val numeral_exp = store_thm(
  "numeral_exp", Term
  `(!n. n EXP ZERO = BIT1 ZERO) /\
   (!n m. n EXP (BIT1 m) = n * iSQR (n EXP m)) /\
   (!n m. n EXP (BIT2 m) = iSQR n * iSQR (n EXP m))`,
  SIMP_TAC bool_ss [BIT1, iSQR, BIT2, EXP_ADD, EXP,
                    ADD_CLAUSES, ALT_ZERO, NUMERAL_DEF] THEN
  REPEAT STRIP_TAC THEN CONV_TAC (AC_CONV(MULT_ASSOC, MULT_SYM)));

val _ = print "Even-ness and odd-ness of numerals\n"

val numeral_evenodd = store_thm(
  "numeral_evenodd",
  Term`!n. EVEN ZERO /\ EVEN (BIT2 n) /\ ~EVEN (BIT1 n) /\
           ~ODD ZERO /\ ~ODD (BIT2 n) /\ ODD (BIT1 n)`,
  SIMP_TAC bool_ss [BIT1, ALT_ZERO, BIT2, ADD_CLAUSES,
                    EVEN, ODD, EVEN_ADD, ODD_ADD]);

val _ = print "Factorial for numerals\n"

val numeral_fact = store_thm
("numeral_fact",
  Term `(FACT 0 = 1)
  /\  (!n. FACT (NUMERAL (BIT1 n)) = NUMERAL (BIT1 n) * FACT (PRE(NUMERAL(BIT1 n))))
  /\  (!n. FACT (NUMERAL (BIT2 n)) = NUMERAL (BIT2 n) * FACT (NUMERAL (BIT1 n)))`,
 REPEAT STRIP_TAC THEN REWRITE_TAC [FACT] THEN
 (STRIP_ASSUME_TAC (SPEC (Term`n:num`) num_CASES) THENL [
    ALL_TAC,
    POP_ASSUM SUBST_ALL_TAC
  ] THEN ASM_REWRITE_TAC[FACT,PRE,NOT_SUC, NUMERAL_DEF,
                         BIT1, BIT2, ADD_CLAUSES]));

val _ = print "funpow for numerals\n"

val numeral_funpow = store_thm(
  "numeral_funpow",
  Term `(FUNPOW f 0 x = x) /\
        (FUNPOW f (NUMERAL (BIT1 n)) x = FUNPOW f (PRE (NUMERAL (BIT1 n))) (f x)) /\
        (FUNPOW f (NUMERAL (BIT2 n)) x = FUNPOW f (NUMERAL (BIT1 n)) (f x))`,
 REPEAT STRIP_TAC THEN REWRITE_TAC [FUNPOW] THEN
 (STRIP_ASSUME_TAC (SPEC (Term`n:num`) num_CASES) THENL [
    ALL_TAC,
    POP_ASSUM SUBST_ALL_TAC
  ] THEN  ASM_REWRITE_TAC[FUNPOW,PRE,ADD_CLAUSES, NUMERAL_DEF,
                          BIT1, BIT2]));

val _ = print "min and max for numerals\n"

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


val _ = print "DIVMOD for numerals\n"

(*---------------------------------------------------------------------------*)
(* For calculation                                                           *)
(*---------------------------------------------------------------------------*)

val DIVMOD_POS = Q.store_thm
("divmod_POS",
 `!n. 0<n ==>
    (DIVMOD (a,m,n) =
      if m < n then
             (a,m)
           else
             (let q = findq (1,m,n) in DIVMOD (a + q,m - n * q,n)))`,
 RW_TAC bool_ss [Once DIVMOD_THM,NOT_ZERO_LT_ZERO,prim_recTheory.LESS_REFL])

val DIVMOD_NUMERAL_CALC = Q.store_thm
("DIVMOD_NUMERAL_CALC",
 `(!m n. m DIV (BIT1 n) = FST(DIVMOD (ZERO,m,BIT1 n))) /\
  (!m n. m DIV (BIT2 n) = FST(DIVMOD (ZERO,m,BIT2 n))) /\
  (!m n. m MOD (BIT1 n) = SND(DIVMOD (ZERO,m,BIT1 n))) /\
  (!m n. m MOD (BIT2 n) = SND(DIVMOD (ZERO,m,BIT2 n)))`,
 METIS_TAC [DIVMOD_CALC,numeral_lt,ALT_ZERO]);

val numeral_div2 = Q.store_thm("numeral_div2",
   `(DIV2 0 = 0) /\
     (!n. DIV2 (NUMERAL (BIT1 n)) = NUMERAL n) /\
     (!n. DIV2 (NUMERAL (BIT2 n)) = NUMERAL (SUC n))`,
  RW_TAC bool_ss [ALT_ZERO, NUMERAL_DEF, BIT1, BIT2]
    THEN REWRITE_TAC [DIV2_def, ADD_ASSOC, GSYM TIMES2]
    THEN METIS_TAC [ZERO_DIV, ALT_ZERO, NUMERAL_DEF, DIVMOD_ID, ADD_CLAUSES,
                    MULT_COMM, ADD_DIV_ADD_DIV, LESS_DIV_EQ_ZERO,
                    numeral_lt, numeral_suc]);

val BIT1n =
  METIS_PROVE [ONE, ADD_ASSOC, BIT1, TIMES2] ``!n. BIT1 n = 2 * n + 1``;

val BIT2n =
  METIS_PROVE [ADD_ASSOC,ADD1,ADD,BIT2,TIMES2] ``!n. BIT2 n = 2 * (SUC n)``;

val ZERO_LT_TWO = METIS_PROVE [TWO, LESS_0] ``0 < 2``;
val ONE_LT_TWO = METIS_PROVE [ONE, TWO, LESS_SUC_REFL] ``1 < 2``;

val ZERO_LT_TWOEXP =
  (GEN_ALL o REWRITE_RULE [GSYM TWO] o Q.SPECL [`n`,`1`]) ZERO_LESS_EXP;

val ONE_LT_TWOEXP =
  METIS_PROVE [EXP_BASE_LT_MONO,EXP,ONE_LT_TWO,LESS_0] ``!n. 1 < 2 ** SUC n``;

val DOUBLE_LT_COR = METIS_PROVE [DOUBLE_LT, LT_MULT_LCANCEL, ZERO_LT_TWO]
    ``!a b. a < b ==> 2 * a + 1 < 2 * b``;

val NUMERAL_MOD_2EXP = Q.prove(
  `(!n. MOD_2EXP 0 n = ZERO) /\
   (!x n. MOD_2EXP x ZERO = ZERO) /\
   (!x n. MOD_2EXP (SUC x) (BIT1 n) = BIT1 (MOD_2EXP x n)) /\
   (!x n. MOD_2EXP (SUC x) (BIT2 n) = iDUB (MOD_2EXP x (SUC n)))`,
  RW_TAC bool_ss [MOD_2EXP_def,iDUB,GSYM DIV2_def,EXP,MOD_1,GSYM TIMES2,
    REWRITE_RULE [SYM ALT_ZERO,NUMERAL_DEF,ADD1] numeral_div2] THENL
     [REWRITE_TAC [ALT_ZERO],
      METIS_TAC [ALT_ZERO,ZERO_MOD,ZERO_LT_TWOEXP],
      STRIP_ASSUME_TAC (Q.SPEC `x` num_CASES)
        THENL [
          ASM_REWRITE_TAC [EXP, MULT_RIGHT_1, MOD_1]
            THEN SUBST1_TAC (Q.SPEC `n` BIT1n)
            THEN SIMP_TAC bool_ss [ONE_LT_TWO, MOD_MULT,Q.SPEC `0` BIT1n,
                   ONCE_REWRITE_RULE [GSYM MULT_COMM] MOD_MULT,MULT_0,ADD],
          POP_ASSUM SUBST1_TAC
            THEN SUBST1_TAC (Q.SPEC `n` BIT1n)
            THEN SIMP_TAC bool_ss
                   [Once (GSYM MOD_PLUS), ZERO_LT_TWOEXP, GSYM EXP]
            THEN SIMP_TAC bool_ss [Once EXP, GSYM MOD_COMMON_FACTOR,
                    ZERO_LT_TWOEXP, ZERO_LT_TWO]
            THEN SIMP_TAC bool_ss [LESS_MOD, ONE_LT_TWOEXP]
            THEN METIS_TAC [BIT1n, DOUBLE_LT_COR, LESS_MOD, EXP,
                            DIVISION, ZERO_LT_TWOEXP]],
      Q.SPEC_THEN `n` SUBST1_TAC BIT2n
        THEN METIS_TAC [MOD_COMMON_FACTOR,TWO,LESS_0,ZERO_LT_TWOEXP]]);

val iMOD_2EXP = new_definition("iMOD_2EXP", ``iMOD_2EXP = MOD_2EXP``);

val BIT1n = REWRITE_RULE [GSYM ADD1] BIT1n;

val numeral_imod_2exp = Q.store_thm("numeral_imod_2exp",
  `(!n. iMOD_2EXP 0 n = ZERO) /\ (!x n. iMOD_2EXP x ZERO = ZERO) /\
       (!x n. iMOD_2EXP (NUMERAL (BIT1 x)) (BIT1 n) =
          BIT1 (iMOD_2EXP (NUMERAL (BIT1 x) - 1) n)) /\
       (!x n. iMOD_2EXP (NUMERAL (BIT2 x)) (BIT1 n) =
          BIT1 (iMOD_2EXP (NUMERAL (BIT1 x)) n)) /\
       (!x n. iMOD_2EXP (NUMERAL (BIT1 x)) (BIT2 n) =
          iDUB (iMOD_2EXP (NUMERAL (BIT1 x) - 1) (SUC n))) /\
        !x n. iMOD_2EXP (NUMERAL (BIT2 x)) (BIT2 n) =
          iDUB (iMOD_2EXP (NUMERAL (BIT1 x)) (SUC n))`,
  RW_TAC bool_ss [iMOD_2EXP, NUMERAL_MOD_2EXP]
    THEN SUBST1_TAC (Q.SPEC `BIT1 x` NUMERAL_DEF)
    THEN SUBST1_TAC (Q.SPEC `BIT2 x` NUMERAL_DEF)
    THEN SUBST1_TAC (Q.SPEC `x` BIT1n)
    THEN SUBST1_TAC (Q.SPEC `x` ((GSYM o hd o tl o CONJUNCTS) numeral_suc))
    THEN SIMP_TAC bool_ss [NUMERAL_MOD_2EXP, SUC_SUB1, GSYM BIT1n]);

val MOD_2EXP = save_thm("MOD_2EXP",
  CONJ (REWRITE_RULE [ALT_ZERO] (hd (tl (CONJUNCTS NUMERAL_MOD_2EXP))))
       (METIS_PROVE [NUMERAL_DEF,iMOD_2EXP]
         ``!x n. MOD_2EXP x (NUMERAL n) = NUMERAL (iMOD_2EXP x n)``));

val DIV_2EXP = Q.store_thm("DIV_2EXP",
  `!n x. DIV_2EXP n x = FUNPOW DIV2 n x`,
  INDUCT_TAC THEN ASM_SIMP_TAC bool_ss
          [DIV_2EXP_def, CONJUNCT1 FUNPOW, FUNPOW_SUC, CONJUNCT1 EXP, DIV_1]
    THEN POP_ASSUM (fn th => SIMP_TAC bool_ss [GSYM th, EXP_1, ADD1, EXP_ADD,
       DIV2_def, DIV_2EXP_def, DIV_DIV_DIV_MULT, ZERO_LT_TWO, ZERO_LT_TWOEXP]));

(* ----------------------------------------------------------------------
    Rewrites to optimise calculations with powers of 2
   ---------------------------------------------------------------------- *)

val texp_help_def = new_recursive_definition {
  name = "texp_help_def",
  def = ``(texp_help 0 acc = BIT2 acc) /\
          (texp_help (SUC n) acc = texp_help n (BIT1 acc))``,
  rec_axiom = TypeBase.axiom_of ``:num``};

val texp_help_thm = store_thm(
  "texp_help_thm",
  ``!n a. texp_help n a = (a + 1) * 2 EXP (n + 1)``,
  INDUCT_TAC THEN SRW_TAC [][texp_help_def] THENL [
    SRW_TAC [][EXP, MULT_CLAUSES, ONE, TWO, ADD_CLAUSES, BIT2],
    SRW_TAC [][EXP, ADD_CLAUSES] THEN
    Q.SUBGOAL_THEN `BIT1 a = 2 * a + 1` ASSUME_TAC THEN1
      SRW_TAC [][BIT1, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES] THEN
    SRW_TAC [][RIGHT_ADD_DISTRIB, MULT_CLAUSES, TIMES2, LEFT_ADD_DISTRIB,
               AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM]
  ]);

val texp_help0 = store_thm(
  "texp_help0",
  ``texp_help n 0 = 2 ** (n + 1)``,
  SRW_TAC [][texp_help_thm, ADD_CLAUSES, MULT_CLAUSES, EXP_ADD, EXP_1,
             MULT_COMM]);

val numeral_texp_help = store_thm(
  "numeral_texp_help",
  ``(texp_help ZERO acc = BIT2 acc) /\
    (texp_help (BIT1 n) acc = texp_help (PRE (BIT1 n)) (BIT1 acc)) /\
    (texp_help (BIT2 n) acc = texp_help (BIT1 n) (BIT1 acc))``,
  SRW_TAC [][texp_help_def, BIT1, BIT2, ADD_CLAUSES, PRE, ALT_ZERO]);

val TWO_EXP_THM = store_thm(
  "TWO_EXP_THM",
  ``(2 EXP 0 = 1) /\
    (2 EXP (NUMERAL (BIT1 n)) = NUMERAL (texp_help (PRE (BIT1 n)) ZERO)) /\
    (2 EXP (NUMERAL (BIT2 n)) = NUMERAL (texp_help (BIT1 n) ZERO))``,
  SRW_TAC [][texp_help0, EXP, ALT_ZERO] THEN
  SRW_TAC [][NUMERAL_DEF, EXP_BASE_INJECTIVE, numeral_lt] THEN
  SRW_TAC [][BIT1, BIT2, PRE, ADD_CLAUSES, ALT_ZERO]);

val onecount_def = new_specification(
  "onecount_def", ["onecount"],
  (BETA_RULE o
   ONCE_REWRITE_RULE [FUN_EQ_THM] o
   Q.SPECL [`\a. a:num`,
            `\ (n:num) (rf:num->num) (a:num). rf (SUC a)`,
            `\ (n:num) (rf:num->num) (a:num). ZERO`] o
   INST_TYPE [alpha |-> ``:num -> num``]) bit_initiality)
val onecount0 = SIMP_RULE (srw_ss()) [ALT_ZERO] (CONJUNCT1 onecount_def)

val exactlog_def = new_specification(
  "exactlog_def", ["exactlog"],
  (BETA_RULE o
   Q.SPECL [`ZERO`,
            `\ (n:num) (r:num). ZERO`,
            `\ (n:num) (r:num). let x = onecount n ZERO
                                in
                                  if x = ZERO then ZERO
                                  else BIT1 x`] o
   INST_TYPE [alpha |-> ``:num``]) bit_initiality)

val onecount_lemma1 = prove(
  ``!n a. 0 < onecount n a ==> a <= onecount n a``,
  HO_MATCH_MP_TAC bit_induction THEN
  SRW_TAC [][onecount_def, LESS_EQ_REFL, ALT_ZERO, LESS_REFL] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC `SUC a` THEN
  SRW_TAC [][LESS_EQ_SUC_REFL]);

val onecount_lemma2 = prove(
  ``!n. 0 < n ==> !a b. (onecount n a = 0) = (onecount n b = 0)``,
  HO_MATCH_MP_TAC bit_induction THEN
  SRW_TAC [][ALT_ZERO, LESS_REFL, onecount_def] THEN
  Q.SPEC_THEN `n` FULL_STRUCT_CASES_TAC num_CASES THENL [
    SRW_TAC [][onecount0, NOT_SUC, ALT_ZERO],
    SRW_TAC [][LESS_0]
  ]);

val sub_eq' = prove(
  ``(m - n = p) = if n <= m then m = p + n else (p = 0)``,
  SRW_TAC [][SUB_RIGHT_EQ, EQ_IMP_THM, ADD_COMM, LESS_EQ_REFL, ADD_CLAUSES]
  THENL [
    FULL_SIMP_TAC (srw_ss()) [LESS_EQ_0, LESS_EQUAL_ANTISYM, ADD_CLAUSES],
    FULL_SIMP_TAC (srw_ss()) [LESS_EQ_ADD],
    FULL_SIMP_TAC (srw_ss()) [LESS_EQ_0],
    FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQUAL, LESS_OR_EQ]
  ]);

val sub_add' = prove(
  ``m - n + p = if n <= m then m + p - n else p``,
  SRW_TAC [][SUB_RIGHT_ADD] THENL [
    Q.SUBGOAL_THEN `m = n` SUBST_ALL_TAC
      THEN1 SRW_TAC [][LESS_EQUAL_ANTISYM] THEN
    METIS_TAC [ADD_SUB, ADD_COMM],
    METIS_TAC [NOT_LESS_EQUAL, LESS_ANTISYM]
  ]);

val onecount_lemma3 = prove(
  ``!n a. 0 < onecount n (SUC a) ==>
          (onecount n (SUC a) = SUC (onecount n a))``,
  HO_MATCH_MP_TAC bit_induction THEN
  SRW_TAC [][onecount_def, ALT_ZERO, LESS_REFL]);

val onecount_characterisation = store_thm(
  "onecount_characterisation",
  ``!n a. 0 < onecount n a /\ 0 < n ==> (n = 2 EXP (onecount n a - a) - 1)``,
  HO_MATCH_MP_TAC bit_induction THEN
  SRW_TAC [][onecount_def] THENL [
    FULL_SIMP_TAC (srw_ss()) [ALT_ZERO, LESS_REFL],
    SRW_TAC [][onecount_lemma3, SUB, EXP] THENL [
      Q.SUBGOAL_THEN `0 < n` STRIP_ASSUME_TAC
        THEN1 (CCONTR_TAC THEN
               FULL_SIMP_TAC (srw_ss()) [NOT_LESS, LESS_EQ_0, onecount0,
                                         LESS_REFL]) THEN
      Q.SUBGOAL_THEN `0 < onecount n a` STRIP_ASSUME_TAC
        THEN1 METIS_TAC [onecount_lemma2, NOT_ZERO_LT_ZERO] THEN
      METIS_TAC [onecount_lemma1, LESS_EQ_ANTISYM],
      FULL_SIMP_TAC (srw_ss()) [NOT_LESS] THEN
      ASM_CASES_TAC ``0 < n`` THENL [
        Q.SUBGOAL_THEN `0 < onecount n a` STRIP_ASSUME_TAC
          THEN1 METIS_TAC [onecount_lemma2, NOT_ZERO_LT_ZERO] THEN
        Q.ABBREV_TAC `X = onecount n a - a` THEN
        Q_TAC SUFF_TAC `n = 2 ** X - 1` THENL [
          DISCH_THEN SUBST1_TAC THEN
          SRW_TAC [][Once BIT1, sub_add'] THENL [
            SRW_TAC [][SYM ONE, ADD_SUB, TIMES2],
            FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQUAL] THEN
            FULL_SIMP_TAC (srw_ss()) [ONE, LESS_THM, NOT_LESS_0, EXP_EQ_0] THEN
            FULL_SIMP_TAC (srw_ss()) [TWO, ONE, NOT_SUC]
          ],
          Q.UNABBREV_TAC `X` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          SRW_TAC [][]
        ],
        FULL_SIMP_TAC (srw_ss()) [NOT_LESS, LESS_EQ_0, onecount0, SUB_EQUAL_0,
                                  EXP, MULT_CLAUSES] THEN
        SRW_TAC [][TWO, ONE, BIT1, SUB, ADD_CLAUSES, LESS_REFL, LESS_SUC_REFL]
      ]
    ],
    FULL_SIMP_TAC (srw_ss()) [ALT_ZERO, LESS_REFL]
  ]);

val onecount_thm = SIMP_RULE (srw_ss()) [SUB_0]
                             (Q.SPECL [`n`, `0`] onecount_characterisation)

val bit_cases = hd (Prim_rec.prove_cases_thm bit_induction)

val exactlog_characterisation = store_thm(
  "exactlog_characterisation",
  ``!n m. (exactlog n = BIT1 m) ==> (n = 2 ** (m + 1))``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `n` STRUCT_CASES_TAC bit_cases THEN
  SRW_TAC [][exactlog_def, numeral_eq, LET_THM] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ALT_ZERO, NOT_ZERO_LT_ZERO]) THEN
  ASM_CASES_TAC ``0 < n'`` THENL [
    SIMP_TAC (srw_ss()) [Once BIT2] THEN
    POP_ASSUM (fn zln =>
                  POP_ASSUM
                      (fn zloc => ASSUME_TAC (MATCH_MP (GEN_ALL onecount_thm)
                                                       (CONJ zloc zln)))) THEN
    POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
    Q.ABBREV_TAC `X = onecount n' 0` THEN
    Q.SUBGOAL_THEN `onecount n' ZERO = X` SUBST_ALL_TAC THEN1
      SRW_TAC [][ALT_ZERO] THEN
    SRW_TAC [][sub_add', SUB_LEFT_ADD] THENL [
      FULL_SIMP_TAC (srw_ss()) [ADD_CLAUSES, ONE, LESS_EQ_MONO,
                                NOT_SUC_LESS_EQ_0],
      SRW_TAC [][ADD_CLAUSES, SUC_SUB1, EXP_ADD, EXP_1] THEN
      METIS_TAC [MULT_COMM, TIMES2],
      FULL_SIMP_TAC (srw_ss()) [NOT_LESS_EQUAL, ONE, LESS_THM, NOT_LESS_0,
                                EXP_EQ_0] THEN
      FULL_SIMP_TAC (srw_ss()) [TWO, ONE, NOT_SUC]
    ],
    FULL_SIMP_TAC (srw_ss()) [onecount0, NOT_LESS, LESS_EQ_0, LESS_REFL]
  ]);

val internal_mult_def = new_definition(
  "internal_mult_def",
  ``internal_mult = $*``);

val DIV2_BIT1 = store_thm(
  "DIV2_BIT1",
  ``DIV2 (BIT1 x) = x``,
  SRW_TAC [][REWRITE_RULE [NUMERAL_DEF] numeral_div2]);

val odd_lemma = prove(
  ``!n. ODD n ==> ?m. n = BIT1 m``,
  HO_MATCH_MP_TAC bit_induction THEN SRW_TAC [][numeral_evenodd, numeral_eq]);

val enhanced_numeral_mult = prove(
  ``x * y = if y = ZERO then ZERO
            else if x = ZERO then ZERO
            else
              let m = exactlog x in
              let n = exactlog y
              in
                if ODD m then texp_help (DIV2 m) (PRE y)
                else if ODD n then texp_help (DIV2 n) (PRE x)
                else internal_mult x y``,
  SRW_TAC [][internal_mult_def, MULT_CLAUSES, ALT_ZERO] THEN
  SRW_TAC [][] THENL [
    IMP_RES_TAC odd_lemma THEN markerLib.UNABBREV_ALL_TAC THEN
    SRW_TAC [][DIV2_BIT1, texp_help_thm] THEN
    Q.SPEC_THEN `y` FULL_STRUCT_CASES_TAC num_CASES THEN1
      FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][PRE, ADD1] THEN IMP_RES_TAC exactlog_characterisation THEN
    SRW_TAC [][AC MULT_ASSOC MULT_COMM],

    IMP_RES_TAC odd_lemma THEN markerLib.UNABBREV_ALL_TAC THEN
    SRW_TAC [][DIV2_BIT1, texp_help_thm] THEN
    Q.SPEC_THEN `x` FULL_STRUCT_CASES_TAC num_CASES THEN1
      FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][PRE, ADD1] THEN IMP_RES_TAC exactlog_characterisation THEN
    SRW_TAC [][AC MULT_ASSOC MULT_COMM]
  ]);

val sillylet = prove(``LET f ZERO = f ZERO``, REWRITE_TAC [LET_THM])
val silly_exactlog =
    prove(``exactlog (BIT1 x) = ZERO``, REWRITE_TAC [exactlog_def])

fun gen_case x y =
    SIMP_RULE bool_ss [numeral_eq, silly_exactlog, sillylet, numeral_evenodd]
              (Q.INST [`x` |-> x, `y` |-> y] enhanced_numeral_mult)


val enumeral_mult = save_thm(
  "enumeral_mult",
  LIST_CONJ (List.take(CONJUNCTS (SPEC_ALL numeral_mult), 2) @
             [gen_case `BIT1 x` `BIT1 y`,
              gen_case `BIT1 x` `BIT2 y`,
              gen_case `BIT2 x` `BIT1 y`,
              gen_case `BIT2 x` `BIT2 y`]))

val internal_mult_characterisation = save_thm(
  "internal_mult_characterisation",
  REWRITE_RULE [SYM internal_mult_def] numeral_mult);

(* ----------------------------------------------------------------------
    hide the internal constants from this theory so that later name-
    spaces are not contaminated.   Constants can still be found by using
    numeral$cname syntax.
   ---------------------------------------------------------------------- *)

val _ = app
          (fn s => remove_ovl_mapping s {Name = s, Thy = "numeral"})
          ["iZ", "iiSUC", "iDUB", "iSUB", "iMOD_2EXP", "iSQR", "texp_help",
           "onecount", "exactlog"]

val _ = export_theory();
