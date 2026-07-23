Theory refute
Ancestors
  real sorting words rat
Libs
  EnumType

val _ = TypeBase.export [
  EnumType.enum_type_to_tyinfo ("rf1", ["rf1_1"]),
  EnumType.enum_type_to_tyinfo ("rf2", ["rf2_1", "rf2_2"]),
  EnumType.enum_type_to_tyinfo ("rf3", ["rf3_1", "rf3_2", "rf3_3"]),
  EnumType.enum_type_to_tyinfo ("rf4", ["rf4_1", "rf4_2", "rf4_3",
                                        "rf4_4"]),
  EnumType.enum_type_to_tyinfo ("rf5", ["rf5_1", "rf5_2", "rf5_3",
                                        "rf5_4", "rf5_5"]),
  EnumType.enum_type_to_tyinfo ("rf6", ["rf6_1", "rf6_2", "rf6_3",
                                        "rf6_4", "rf6_5", "rf6_6"])
]

val _ = ThmSetData.export_list {settype = "refute_simp", initial = []}
val _ = ThmSetData.export_list {settype = "refute_psimp", initial = []}
val _ = ThmSetData.export_list {settype = "refute_unfold", initial = []}

(* Part 2: the substrate-independent pseudo-random stream.  rand_below's
   caller must ensure n <= 2^32.  Multiply-shift has a bias of at most
   2^-32 per draw, which is immaterial for counterexample generation. *)
Definition rand_next_def:
  rand_next s =
    (6364136223846793005 * s + 1442695040888963407) MOD
      18446744073709551616
End

Definition rand_out_def:
  rand_out s = s DIV 4294967296
End

Definition rand_below_def:
  rand_below n s =
    let s' = rand_next s
    in ((rand_out s' * n) DIV 4294967296, s')
End

(* Part 3: static model-finder support.  These constants intentionally have
   no defining equations: the nut translation gives them their model-finder
   meaning.  In particular, asserting is_unknown unknown would add logical
   content that the source Nitpick theory does not have. *)
val _ = new_constant ("unknown", ``:'a``)
val _ = new_constant ("is_unknown", ``:'a -> bool``)
val _ = new_constant ("safe_The", ``:('a -> bool) -> 'a``)

Definition card'_def:
  card' (s : 'a set) =
    if FINITE s then
      LENGTH (@xs. set xs = s /\ ALL_DISTINCT xs)
    else
      0
End

Theorem Eps_psimp[refute_psimp]:
  P x ==> ~P y ==> ($@ P = y) ==> ($@ P = x)
Proof
  metis_tac [boolTheory.SELECT_AX]
QED

Theorem one_case_unfold[refute_unfold]:
  one_CASE (u : unit) (x : 'a) = x
Proof
  simp [oneTheory.one_case_def]
QED

Theorem num_case_unfold[refute_unfold]:
  num_CASE n (z : 'a) f = if n = 0 then z else f (n - 1)
Proof
  Cases_on `n` >> simp [arithmeticTheory.num_case_compute]
QED

(* RTC is presented to the model finder as reflexive closure of TC.  RC is
   then expanded to equality plus TC, leaving TC as the sole closure
   primitive that the nut translator must recognize. *)
Theorem RTC_unfold[refute_unfold]:
  RTC R = RC (TC R)
Proof
  metis_tac [relationTheory.TC_RC_EQNS]
QED

Theorem RC_unfold[refute_unfold]:
  RC R x y <=> x = y \/ R x y
Proof
  simp [relationTheory.RC_DEF]
QED

Theorem list_size_simp[refute_simp]:
  list_size f xs =
    if xs = [] then 0
    else SUC (f (HD xs) + list_size f (TL xs))
Proof
  Cases_on `xs` >> simp [listTheory.list_size_thm]
QED

(* Primitive recursion equations with SUC on their left-hand sides prevent
   the binary-integer encoding from matching them.  These equivalent forms
   keep the common arithmetic/list operations usable without such patterns. *)
Theorem num_pre_simp[refute_simp]:
  PRE n = if n = 0 then 0 else n - 1
Proof
  Cases_on `n` >> simp []
QED

Theorem list_length_simp[refute_simp]:
  LENGTH xs = if xs = [] then 0 else SUC (LENGTH (TL xs))
Proof
  Cases_on `xs` >> simp []
QED

Theorem list_take_simp[refute_simp]:
  TAKE n xs =
    if n = 0 \/ xs = [] then []
    else HD xs :: TAKE (n - 1) (TL xs)
Proof
  Cases_on `n` >> Cases_on `xs` >> simp []
QED

Theorem list_drop_simp[refute_simp]:
  DROP n xs =
    if n = 0 \/ xs = [] then xs
    else DROP (n - 1) (TL xs)
Proof
  Cases_on `n` >> Cases_on `xs` >> simp []
QED

(* Part 4: ordinary datatypes used by the boxing and binary-integer
   preprocessors.  Keeping these declarations static makes their TypeBase
   information available to the generic datatype pipeline without adding
   runtime theory content. *)
Datatype:
  funbox = FunBox ('a -> 'b)
End

Datatype:
  pairbox = PairBox 'a 'b
End

val _ = new_type ("unsigned_bit", 0)
val _ = new_type ("signed_bit", 0)

(* The codatatype model encoding interprets these declarations directly.
   They deliberately have no HOL defining equations. *)
val _ = new_type ("bisim_iterator", 0)
val _ = new_constant
  ("bisim", ``:bisim_iterator -> 'a -> 'a -> bool``)
val _ = new_constant
  ("bisim_iterator_max", ``:bisim_iterator``)
val _ = new_constant
  ("bisim_suc", ``:bisim_iterator -> bisim_iterator``)
val _ = new_constant ("bisim_zero", ``:bisim_iterator``)
val _ = new_constant ("Quot", ``:'a -> 'b``)

Datatype:
  bitword = Bitword ('a -> bool)
End

(* Part 5: alternative fractions for the model finder.

   Normalization faithfulness.  The raw HOL4 frac carrier only requires a
   positive denominator, but Frac selects the positive, coprime pairs.  Every
   frac-valued ersatz operation below calls frac, and frac calls norm_frac;
   hence every atom produced by an operation is in canonical reduced form.
   Canonical pairs are therefore in one-to-one correspondence with rationals,
   rather than exposing the many raw frac representatives of one rational. *)

(* integerTheory deliberately keeps abstract integer operations out of the
   default evaluator.  The ersatz suite is executable, so expose its existing
   numeral calculation rules to EVAL without introducing new arithmetic. *)
Theorem frac_int_eq_compute[compute] = integerTheory.INT_EQ_CALCULATE
Theorem frac_int_lt_compute[compute] = integerTheory.INT_LT_CALCULATE
Theorem frac_int_le_compute[compute] = integerTheory.INT_LE_CALCULATE
Theorem frac_int_add_compute[compute] = integerTheory.INT_ADD_CALCULATE
Theorem frac_int_mul_compute[compute] = integerTheory.INT_MUL_CALCULATE
Theorem frac_int_div_compute[compute] = integerTheory.INT_DIV_CALCULATE
Theorem frac_int_add_reduce[compute] = integerTheory.INT_ADD_REDUCE
Theorem frac_int_mul_reduce[compute] = integerTheory.INT_MUL_REDUCE
Theorem frac_int_div_reduce[compute] = integerTheory.INT_DIV_REDUCE
Theorem frac_int_eq_reduce[compute] = integerTheory.INT_EQ_REDUCE
Theorem frac_int_lt_reduce[compute] = integerTheory.INT_LT_REDUCE
Theorem frac_int_le_reduce[compute] = integerTheory.INT_LE_REDUCE
Theorem frac_int_negneg_compute[compute] = integerTheory.INT_NEGNEG

Definition nat_gcd_def:
  nat_gcd x y =
    if y = 0 then x else nat_gcd y (x MOD y)
Termination
  WF_REL_TAC `measure SND` >> simp []
End

Definition nat_lcm_def:
  nat_lcm x y = x * y DIV nat_gcd x y
End

Definition Frac_def:
  Frac (p : int # int) <=>
    integer$int_lt (integer$int_of_num 0) (SND p) /\
    nat_gcd (integer$Num (FST p)) (integer$Num (SND p)) = 1
End

Definition norm_frac_def:
  norm_frac (a : int) (b : int) =
    if a = integer$int_of_num 0 \/ b = integer$int_of_num 0 then
      (integer$int_of_num 0, integer$int_of_num 1)
    else
      let a' = if integer$int_lt b (integer$int_of_num 0)
               then integer$int_neg a else a;
          c = nat_gcd (integer$Num a) (integer$Num b);
          d = integer$Num b DIV c
      in
        (integer$int_div a' (integer$int_of_num c),
         integer$int_of_num (SUC (PRE d)))
End

Theorem norm_frac_dnm_pos:
  integer$int_lt (integer$int_of_num 0) (SND (norm_frac a b))
Proof
  rw [norm_frac_def] >> simp []
QED

Definition frac_def[nocompute]:
  frac a b = frac$abs_frac (norm_frac a b)
End

Definition zero_frac_def:
  zero_frac = frac (integer$int_of_num 0) (integer$int_of_num 1)
End

Definition one_frac_def:
  one_frac = frac (integer$int_of_num 1) (integer$int_of_num 1)
End

Definition num_def[nocompute]:
  num q = frac$frac_nmr q
End

Definition denom_def[nocompute]:
  denom q = frac$frac_dnm q
End

Theorem rep_frac_frac[compute]:
  frac$rep_frac (frac a b) = norm_frac a b
Proof
  rw [frac_def] >>
  irule (iffLR (Q.SPEC `norm_frac a b`
    (CONJUNCT2 fracTheory.frac_bij))) >>
  simp [norm_frac_dnm_pos]
QED

Theorem num_frac[compute]:
  num (frac a b) = FST (norm_frac a b)
Proof
  simp [num_def, fracTheory.frac_nmr_def, rep_frac_frac]
QED

Theorem denom_frac[compute]:
  denom (frac a b) = SND (norm_frac a b)
Proof
  simp [denom_def, fracTheory.frac_dnm_def, rep_frac_frac]
QED

Definition plus_frac_def:
  plus_frac q r =
    let d = integer$int_of_num
          (nat_lcm (integer$Num (denom q)) (integer$Num (denom r)))
    in frac
      (integer$int_add
        (integer$int_mul (num q) (integer$int_div d (denom q)))
        (integer$int_mul (num r) (integer$int_div d (denom r)))) d
End

Definition times_frac_def:
  times_frac q r =
    frac (integer$int_mul (num q) (num r))
      (integer$int_mul (denom q) (denom r))
End

Definition uminus_frac_def:
  uminus_frac q = frac (integer$int_neg (num q)) (denom q)
End

Definition subtract_frac_def:
  subtract_frac q r = plus_frac q (uminus_frac r)
End

Definition number_of_frac_def:
  number_of_frac n = frac n (integer$int_of_num 1)
End

Definition inverse_frac_def:
  inverse_frac q = frac (denom q) (num q)
End

Definition divide_frac_def:
  divide_frac q r = times_frac q (inverse_frac r)
End

Definition of_num_frac_def:
  of_num_frac n = frac (integer$int_of_num n) (integer$int_of_num 1)
End

Definition less_frac_def:
  less_frac q r <=>
    integer$int_lt (num (plus_frac q (uminus_frac r)))
      (integer$int_of_num 0)
End

Definition less_eq_frac_def:
  less_eq_frac q r <=>
    integer$int_le (num (plus_frac q (uminus_frac r)))
      (integer$int_of_num 0)
End

Definition of_frac_def:
  of_frac q = rat$abs_rat q
End

Theorem of_frac_frac[compute]:
  of_frac (frac a b) = rat$abs_rat (frac$abs_frac (norm_frac a b))
Proof
  simp [of_frac_def, frac_def]
QED

(* Part 5 continued: executable forms for bounded quantifiers.  Refute's
   preprocessing rewrites to these list combinators before checking for
   unexpanded binders. *)
Theorem bounded_forall_less:
  (∀n. n < e ⇒ P n) ⇔ EVERY P (COUNT_LIST e)
Proof
  simp [listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem bounded_exists_less:
  (∃n. n < e ∧ P n) ⇔ EXISTS P (COUNT_LIST e)
Proof
  simp [listTheory.EXISTS_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem bounded_forall_leq:
  (∀n. n ≤ e ⇒ P n) ⇔ EVERY P (COUNT_LIST (e + 1))
Proof
  simp [listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST,
        arithmeticTheory.ADD1, arithmeticTheory.LESS_EQ_IFF_LESS_SUC]
QED

Theorem bounded_exists_leq:
  (∃n. n ≤ e ∧ P n) ⇔ EXISTS P (COUNT_LIST (e + 1))
Proof
  simp [listTheory.EXISTS_MEM, rich_listTheory.MEM_COUNT_LIST,
        arithmeticTheory.ADD1, arithmeticTheory.LESS_EQ_IFF_LESS_SUC]
QED

Theorem bounded_forall_in_count:
  (∀n. n IN count e ⇒ P n) ⇔ EVERY P (COUNT_LIST e)
Proof
  simp [listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem bounded_exists_in_count:
  (∃n. n IN count e ∧ P n) ⇔ EXISTS P (COUNT_LIST e)
Proof
  simp [listTheory.EXISTS_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem bounded_forall_mem:
  (∀x. MEM x l ⇒ P x) ⇔ EVERY P l
Proof
  simp [listTheory.EVERY_MEM]
QED

Theorem bounded_exists_mem:
  (∃x. MEM x l ∧ P x) ⇔ EXISTS P l
Proof
  simp [listTheory.EXISTS_MEM]
QED

(* Part 6: narrowing represents function variables by finite update chains.
   The distinct constructor prefixes replace Isabelle's type-scoped
   Constant names.  These static datatypes are also available to TypeBase
   before any goal is processed. *)
Datatype:
  ffun = FConstant 'b | FUpdate 'a 'b ffun
End

Definition eval_ffun_def:
  (eval_ffun (FConstant c) x = c) /\
  (eval_ffun (FUpdate x' y f) x =
     if x = x' then y else eval_ffun f x)
End

Theorem eval_ffun_compute[compute] = eval_ffun_def

Datatype:
  cfun = CConstant 'b
End

Definition eval_cfun_def:
  eval_cfun (CConstant c) x = c
End

Theorem eval_cfun_compute[compute] = eval_cfun_def
