Theory normalizer[bare]
Ancestors
  arithmetic
Libs
  HolKernel Parse boolLib boolSimps simpLib tautLib mesonLib

(* from numLib.sml, not defined yet when compiling this file *)
val INDUCT_TAC = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC

fun is_comm t =
    let val (l,r) = dest_eq $ #2 $ strip_forall t
        val (f, xs) = strip_comb l
        val _ = length xs = 2 orelse raise mk_HOL_ERR "" "" ""
        val (g, ys) = strip_comb r
        val _ = length ys = 2 orelse raise mk_HOL_ERR "" "" ""
    in
      f ~~ g andalso el 1 xs ~~ el 2 ys andalso el 2 xs ~~ el 1 ys
    end handle HOL_ERR _ => false

Theorem SEMIRING_PTHS:
  (!(x:'a) y z. add x (add y z) = add (add x y) z) /\
  (!x y. add x y = add y x) /\
  (!x. add r0 x = x) /\
  (!x y z. mul x (mul y z) = mul (mul x y) z) /\
  (!x y. mul x y = mul y x) /\
  (!x. mul r1 x = x) /\
  (!x. mul r0 x = r0) /\
  (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
  (!x. pwr x 0 = r1) /\
  (!x n. pwr x (SUC n) = mul x (pwr x n))
  ==> (mul r1 x = x) /\
      (add (mul a m) (mul b m) = mul (add a b) m) /\
      (add (mul a m) m = mul (add a r1) m) /\
      (add m (mul a m) = mul (add a r1) m) /\
      (add m m = mul (add r1 r1) m) /\
      (mul r0 m = r0) /\
      (add r0 a = a) /\
      (add a r0 = a) /\
      (mul a b = mul b a) /\
      (mul (add a b) c = add (mul a c) (mul b c)) /\
      (mul r0 a = r0) /\
      (mul a r0 = r0) /\
      (mul r1 a = a) /\
      (mul a r1 = a) /\
      (mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)) /\
      (mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))) /\
      (mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)) /\
      (mul (mul lx ly) rx = mul (mul lx rx) ly) /\
      (mul (mul lx ly) rx = mul lx (mul ly rx)) /\
      (mul lx rx = mul rx lx) /\
      (mul lx (mul rx ry) = mul (mul lx rx) ry) /\
      (mul lx (mul rx ry) = mul rx (mul lx ry)) /\
      (add (add a b) (add c d) = add (add a c) (add b d)) /\
      (add (add a b) c = add a (add b c)) /\
      (add a (add c d) = add c (add a d)) /\
      (add (add a b) c = add (add a c) b) /\
      (add a c = add c a) /\
      (add a (add c d) = add (add a c) d) /\
      (mul (pwr x p) (pwr x q) = pwr x (p + q)) /\
      (mul x (pwr x q) = pwr x (SUC q)) /\
      (mul (pwr x q) x = pwr x (SUC q)) /\
      (mul x x = pwr x 2) /\
      (pwr (mul x y) q = mul (pwr x q) (pwr y q)) /\
      (pwr (pwr x p) q = pwr x (p * q)) /\
      (pwr x 0 = r1) /\
      (pwr x 1 = x) /\
      (mul x (add y z) = add (mul x y) (mul x z)) /\
      (pwr x (SUC q) = mul x (pwr x q))
Proof
  STRIP_TAC THEN
  SUBGOAL_THEN
    “(!m:'a n. add m n = add n m) /\
    (!m n p. add (add m n) p = add m (add n p)) /\
    (!m n p. add m (add n p) = add n (add m p)) /\
    (!x. add x r0 = x) /\
    (!m n. mul m n = mul n m) /\
    (!m n p. mul (mul m n) p = mul m (mul n p)) /\
    (!m n p. mul m (mul n p) = mul n (mul m p)) /\
    (!m n p. mul (add m n) p = add (mul m p) (mul n p)) /\
    (!x. mul x r1 = x) /\
    (!x. mul x r0 = r0)”
  MP_TAC
  >- (rpt strip_tac >>
      TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) >>
      FILTER_ASM_REWRITE_TAC (not o is_comm) [] >>
      rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
      TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) >>
      ONCE_ASM_REWRITE_TAC[] >>
      FILTER_ASM_REWRITE_TAC(not o is_comm)[] >>
      UNDISCH_THEN “!x:'a y. add x y :'a = add y x”
        (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
      UNDISCH_THEN “!x:'a y. mul x y :'a = mul y x”
        (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      REWRITE_TAC[]) >>
  MAP_EVERY (fn t => UNDISCH_THEN t (K ALL_TAC)) [
    “!(x:'a) y z. add x (add y z) = add (add x y) z”,
    “!(x:'a) y. add x y :'a = add y x”,
    “!(x:'a) y z. mul x (mul y z) = mul (mul x y) z”,
    “!(x:'a) y. mul x y :'a = mul y x”] THEN STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [ONE, TWO] THEN
  SUBGOAL_THEN “!m (n:num) (x:'a). pwr x (m + n) :'a = mul (pwr x m) (pwr x n)”
  ASSUME_TAC
  >- (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [ADD_CLAUSES]) \\
  SUBGOAL_THEN “!(x:'a) (y:'a) (n:num). pwr (mul x y) n = mul (pwr x n) (pwr y n)”
  ASSUME_TAC
  >- (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss []) \\
  FILTER_ASM_REWRITE_TAC (not o is_comm) [] >>
  ID_SPEC_TAC “q:num” THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss[MULT_CLAUSES]
QED

Triviality NUM_NORMALIZE_CONV_sth:
  (!x y z:num. x + (y + z) = (x + y) + z) /\
  (!x y:num. x + y = y + x) /\
  (!x:num. 0 + x = x) /\
  (!x y z:num. x * (y * z) = (x * y) * z) /\
  (!x y:num. x * y = y * x) /\
  (!x:num. 1 * x = x) /\
  (!x:num. 0 * x = 0) /\
  (!x y z:num. x * (y + z) = x * y + x * z) /\
  (!x. x EXP 0 = 1) /\
  (!x n. x EXP (SUC n) = x * x EXP n)
Proof
  REWRITE_TAC[EXP, MULT_CLAUSES, ADD_CLAUSES, LEFT_ADD_DISTRIB] THEN
  SIMP_TAC bool_ss [AC ADD_SYM ADD_ASSOC, AC MULT_SYM MULT_ASSOC]
QED

Theorem NUM_NORMALIZE_CONV_sth =
  MATCH_MP SEMIRING_PTHS NUM_NORMALIZE_CONV_sth;

Theorem RING_FINAL_pth = TAUT `(p ==> F) ==> (~q <=> p) ==> q`;
Theorem NOT_EVEN = GSYM ODD_EVEN;
Theorem NOT_ODD  = GSYM EVEN_ODD;
Theorem PRE_ELIM_THM'' =
  CONV_RULE (RAND_CONV normalForms.NNFD_CONV) PRE_ELIM_THM'; (* forall *)
Theorem SUB_ELIM_THM'' =
  CONV_RULE (RAND_CONV normalForms.NNFD_CONV) SUB_ELIM_THM'; (* forall *)
Theorem DIVMOD_ELIM_THM'' =
  CONV_RULE (RAND_CONV normalForms.NNFD_CONV) (SPEC_ALL DIVMOD_ELIM_THM);

Theorem RING_pth_step:
  !(add:'a->'a->'a) (mul:'a->'a->'a) (n0:'a).
    (!x. mul n0 x = n0) /\
    (!x y z. (add x y = add x z) <=> (y = z)) /\
    (!w x y z. (add (mul w y) (mul x z) = add (mul w z) (mul x y)) <=>
      (w = x) \/ (y = z))
    ==>
    (!a b c d. ~(a = b) /\ ~(c = d) <=>
      ~(add (mul a c) (mul b d) =
        add (mul a d) (mul b c))) /\
    (!n a b c d. ~(n = n0)
      ==> (a = b) /\ ~(c = d)
      ==> ~(add a (mul n c) = add b (mul n d)))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [“n0:'a”, “n:'a”, “d:'a”, “c:'a”]) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN ASM_SIMP_TAC bool_ss []
QED

Theorem NUM_SIMPLIFY_CONV_pth_evenodd:
  (EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
  (ODD(x) <=> (!y. ~(x = 2 * y))) /\
  (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
  (~ODD(x) <=> (!y. ~(x = SUC(2 * y))))
Proof
  rpt strip_tac >| [
    REWRITE_TAC[EVEN_ODD, ODD_EXISTS],
    REWRITE_TAC[ODD_EVEN, EVEN_EXISTS],
    REWRITE_TAC[EVEN_EXISTS],
    REWRITE_TAC[ODD_EXISTS]
  ] >> CONV_TAC (LAND_CONV NOT_EXISTS_CONV) >> REWRITE_TAC[]
QED

Theorem NUM_INTEGRAL_LEMMA:
  ((w :num) = x + d) /\ (y = z + e)
  ==> ((w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC [SIMP_PROVE bool_ss [AC ADD_SYM ADD_ASSOC]
    “(a :num) + b + (c + d) + e = a + c + (e + (b + d))”] THEN
  REWRITE_TAC[EQ_ADD_LCANCEL, ADD_INV_0_EQ, MULT_EQ_0]
QED

Theorem NUM_INTEGRAL:
  (!(x :num). 0 * x = 0) /\
  (!(x :num) y z. (x + y = x + z) <=> (y = z)) /\
  (!(w :num) x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
  REWRITE_TAC[MULT_CLAUSES, EQ_ADD_LCANCEL] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (SPECL [“w:num”, “x:num”] LE_CASES) THEN
  DISJ_CASES_TAC (SPECL [“y:num”, “z:num”] LE_CASES) THEN
  REPEAT (FIRST_X_ASSUM
    (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS])) THEN
  ASM_MESON_TAC [NUM_INTEGRAL_LEMMA, ADD_SYM, MULT_SYM]
QED

