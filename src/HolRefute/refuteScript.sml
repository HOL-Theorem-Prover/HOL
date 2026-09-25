Theory refute
Ancestors
  real sorting words rat finite_map listRange
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

(* Part 2: static model-finder support.  These constants intentionally have
   no defining equations: the nut translation gives them their model-finder
   meaning.  In particular, asserting is_unknown unknown would add logical
   content that the source Nitpick theory does not have. *)
val _ = new_constant ("unknown", ``:'a``)
val _ = new_constant ("is_unknown", ``:'a -> bool``)
val _ = new_constant ("safe_The", ``:('a -> bool) -> 'a``)

(* CARD is a [new_specification] (pred_setScript.sml), pinned only at
   EMPTY and on FINITE INSERT -- past FINITE it is unconstrained, not 0,
   so card' <> CARD as full HOL4 functions.  Substitution is sound
   anyway, but liberally rather than faithfully.  card' (and sum' below,
   built the same way) reach every value through
   [$@ xs. set xs = s /\ ALL_DISTINCT xs], the identical Hilbert-choice
   shape unfold_defs_in_term's [min$@] branch (Refute_ModelFinder_HOL.sml)
   guards on every occurrence: [$@ P] becomes
   [if (?x. P x) then $@ P else unknown].  Where the model's scope is
   large enough to contain a list witnessing s's enumeration -- which
   the adaptive search reaches by growing, always eventually for a
   literal, explicitly-enumerated set -- card' reads it and agrees with
   CARD.  Below that scope -- as well as for an abstractly-quantified or
   too-large set -- the guard reports [unknown] instead of an arbitrary
   atom, so a divergence from CARD's true value can only ever weaken a
   verdict, the same sound/unsound problem pair every [unknown]
   occurrence gets (run_batch, Refute_ModelFinder.sml), never falsify a
   true goal.  The guard also fires unconditionally on this shape, so
   [choice_guard_inserted] is always set and no problem going through
   these rows can ever certify [NoCounterexample]
   (total_scope_search, Refute_ModelFinder.sml): the rows narrow a
   search, they do not close one. *)
Definition card'_def:
  card' (s : 'a set) =
    if FINITE s then
      LENGTH (@xs. set xs = s /\ ALL_DISTINCT xs)
    else
      0
End

(* Port of Nitpick.thy's sum': sum' f A = if finite A then
   sum_list (map f (SOME xs. set xs = A /\ distinct xs)) else 0, over the
   same finite-A distinct witness list as card' above -- same liberal
   substitution argument, see card'_def's comment.  pred_set$SUM_IMAGE is
   fixed at codomain num (its type is ('a -> num) -> ('a -> bool) ->
   num), so SUM below is listTheory's num-list summation, matching
   sum_list at that codomain exactly; xs itself, not MAP f xs, is the
   repetition-free enumeration of s, so MAP f xs lists f e once per
   element of s and SUM (MAP f xs) is order-independent because + is
   commutative and associative -- the same fact that makes SUM_IMAGE's
   ITSET fold well defined (COMMUTING_ITSET_RECURSES, pred_setScript.sml).
   SUM_IMAGE is itself ITSET-based ([FINITE s then ... else ARB]), so past
   FINITE it too is unconstrained rather than 0. *)
Definition sum'_def:
  sum' (f : 'a -> num) (s : 'a set) =
    if FINITE s then
      SUM (MAP f (@xs. set xs = s /\ ALL_DISTINCT xs))
    else
      0
End

(* Port of Nitpick.thy's wf': wf' r = acyclic r /\ (finite r \/ unknown),
   r a set of pairs.  HOL4 relations are curried, so acyclic becomes
   !x. ~TC R x x (the graph has no self-reachable point, matching
   relationTheory's WF_noloops) and the pair set is the graph
   \p. R (FST p) (SND p), directly usable as a ('a # 'a) set since HOL4
   sets are predicates.  FINITE unfolds to True only when R's element
   type is finite (MFH.is_finite_type; an uninstantiated type variable
   counts as finite) -- not when the model-finder scope is finite, which
   it always is regardless.  Over an intrinsically infinite element type
   such as num, FINITE instead lowers to a Kodkod formula that a
   positive-polarity sound problem forces False, so [unknown] genuinely
   participates and wf' only reaches Potential there. *)
Definition wf'_def:
  wf' (R : 'a -> 'a -> bool) <=>
    (!x. ~TC R x x) /\ (FINITE (\p. R (FST p) (SND p)) \/ unknown)
End

(* Port of Nitpick.thy's wf_wfrec'/wfrec', each with a [WF R] guard the
   upstream definitions lack (upstream's wf_wfrec' is the unconditional
   equation, and its wfrec' falls through to wfrec's own relational
   definition rather than to unknown): well-founded recursion made
   encodable by tying a literal recursive equation instead of unfolding
   HOL4's Hilbert-choice [the_fun] (relationScript.sml).  wf_wfrec is
   uninterpreted -- it exists only so the [refute$wf_wfrec ->
   refute$wf_wfrec'] ersatz row (Refute_ModelFinder_HOL.sml) rewrites its
   occurrence inside wf_wfrec'_def's own body back to wf_wfrec' itself,
   giving the model finder the genuine recursive equation
   [wf_wfrec' R Fn x =
    if wf' R then Fn (RESTRICT (wf_wfrec' R Fn) R x) x else unknown]
   rather than an unrolling over an unconstrained function.
   wf_wfrec' is a plain [Definition], so [is_equational_fun]
   (Refute_ModelFinder_HOL.sml) keeps it un-inlined, and the equation
   above is what unfolding hands on to add_axiom -- the same route
   SUM_SET's own equation takes (sum'_def's comment above).

   The recursion is guarded by [WF R], which the [relation$WF ->
   refute$wf'] row lowers to wf', because relation$WFREC_THM -- the only
   HOL fact wf_wfrec' ports -- is proved solely under that premise.
   Asserted for every R the knot is strictly stronger than HOL and can be
   outright unsatisfiable: at [R = \x y. T] and [Fn f b = ~ f b] over
   :bool it reads [v = ~v].  Every scope then goes UNSAT for a goal and
   its negation alike, and exhaustion answers NoCounterexample -- a total
   claim -- to both; dropping the guard here and probing
   [wf_wfrec' (\x y. T) (\f b. ~ f b) T] reproduces exactly that.  Off
   [WF R] the value is [unknown] instead, which is honest: WFREC_DEF picks
   a [the_fun] witness there that nothing characterizes.  A goal reaching
   this through WFREC is covered a second time, by the [unknown_value]
   veto on totality (Refute_ModelFinder_Kodkod.sml); wf_wfrec' has no
   wfrec' wrapper of its own, so only the guard covers it. *)
val _ = new_constant ("wf_wfrec",
  ``:('a -> 'a -> bool) -> (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b``)

Definition wf_wfrec'_def:
  wf_wfrec' (R : 'a -> 'a -> bool) (Fn : ('a -> 'b) -> 'a -> 'b) x =
    if WF R then Fn (RESTRICT (wf_wfrec R Fn) R x) x else unknown
End

(* wfrec' mirrors relation$WFREC_THM (relationScript.sml): under [WF R]
   it agrees with WFREC's own fixpoint characterization.  The
   [relation$WFREC -> refute$wfrec'] ersatz row (Refute_ModelFinder_HOL.
   sml) makes any goal that syntactically mentions WFREC route here
   instead of the_fun/[$@].  A function stays on its own clean STDEQNS
   equations, untouched by this row, only while
   DefnBase carries a live [userdef] presentation for it; that is
   [TotalDefn.Define]'s default, but a [notuserdef] definition, or one
   built by hand outside TotalDefn, registers none, and
   [raw_standard_props] (Refute_ModelFinder_HOL.sml) then falls through
   to its raw, WFREC-containing equation, which this row does reach.
   [relation$WFREC_DEF] itself is unconditional -- it
   picks a value via [the_fun] even when R is not well-founded -- but
   WFREC_THM's fixpoint equation, the only characterization wfrec' ports,
   is proved solely under [WF R]; outside that premise this port has
   nothing to agree or disagree with, so [unknown] is honest rather than
   an arbitrary guess at [the_fun]'s unconstrained choice.  wf_wfrec'
   carries the same guard for the same reason, so a goal naming
   refute$wf_wfrec directly is constrained no more strongly than HOL
   constrains WFREC.  Upstream's wfrec' instead falls through to
   THE y. wfrec_rel R (\f x. F (cut f R x) x) x y, wfrec's definitional
   body; HOL4 reaches WFREC's value only through the_fun, so there is no
   relational characterization to fall through to. *)
Definition wfrec'_def:
  wfrec' (R : 'a -> 'a -> bool) (Fn : ('a -> 'b) -> 'a -> 'b) x =
    if WF R then wf_wfrec' R Fn x else unknown
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

(* Part 3: ordinary datatypes used by the boxing and binary-integer
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

(* Part 4: alternative fractions for the model finder.

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

(* Part 4 continued: executable forms for bounded quantifiers.  Refute's
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

(* Part 4 continued: offset intervals.  [[lo <= n /\ n < hi]] compiles to
   [[listRangeLHI]] ([[lo ..< hi]]), and [[lo <= n /\ n <= hi]] to
   [[listRangeINC]] ([[lo .. hi]]) -- its natural fit, so a non-strict
   upper bound never needs a manufactured offset.  A strict bound folds
   into the endpoint instead ([[lo < n]] is [[lo + 1 <= n]]).
   [[AND_IMP_INTRO]] does not normalise conjunct order, and a generic
   commuting rewrite would ping-pong against its own reverse, so both
   guard orders get their own theorem rather than a shared swap rule. *)
Theorem bounded_forall_interval_leq_lt:
  (∀n. lo ≤ n ∧ n < hi ⇒ P n) ⇔ EVERY P [lo ..< hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeLHI]
QED

Theorem bounded_exists_interval_leq_lt:
  (∃n. lo ≤ n ∧ n < hi ∧ P n) ⇔ EXISTS P [lo ..< hi]
Proof
  metis_tac [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeLHI]
QED

Theorem bounded_forall_interval_leq_lt_swap:
  (∀n. n < hi ∧ lo ≤ n ⇒ P n) ⇔ EVERY P [lo ..< hi]
Proof
  metis_tac [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeLHI]
QED

Theorem bounded_exists_interval_leq_lt_swap:
  (∃n. n < hi ∧ lo ≤ n ∧ P n) ⇔ EXISTS P [lo ..< hi]
Proof
  metis_tac [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeLHI]
QED

Theorem bounded_forall_interval_leq_leq:
  (∀n. lo ≤ n ∧ n ≤ hi ⇒ P n) ⇔ EVERY P [lo .. hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeINC]
QED

Theorem bounded_exists_interval_leq_leq:
  (∃n. lo ≤ n ∧ n ≤ hi ∧ P n) ⇔ EXISTS P [lo .. hi]
Proof
  metis_tac [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeINC]
QED

Theorem bounded_forall_interval_leq_leq_swap:
  (∀n. n ≤ hi ∧ lo ≤ n ⇒ P n) ⇔ EVERY P [lo .. hi]
Proof
  metis_tac [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeINC]
QED

Theorem bounded_exists_interval_leq_leq_swap:
  (∃n. n ≤ hi ∧ lo ≤ n ∧ P n) ⇔ EXISTS P [lo .. hi]
Proof
  metis_tac [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeINC]
QED

(* The eight strict-lower-bound theorems below all reduce the same
   way; deciding it once keeps it off the build's critical path. *)
val lt_add1 = DECIDE “∀m n:num. m < n ⇔ m + 1 ≤ n”

Theorem bounded_forall_interval_lt_lt:
  (∀n. lo < n ∧ n < hi ⇒ P n) ⇔ EVERY P [lo + 1 ..< hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeLHI] >>
  metis_tac [lt_add1]
QED

Theorem bounded_exists_interval_lt_lt:
  (∃n. lo < n ∧ n < hi ∧ P n) ⇔ EXISTS P [lo + 1 ..< hi]
Proof
  simp [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeLHI] >>
  metis_tac [lt_add1]
QED

Theorem bounded_forall_interval_lt_lt_swap:
  (∀n. n < hi ∧ lo < n ⇒ P n) ⇔ EVERY P [lo + 1 ..< hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeLHI] >>
  metis_tac [lt_add1]
QED

Theorem bounded_exists_interval_lt_lt_swap:
  (∃n. n < hi ∧ lo < n ∧ P n) ⇔ EXISTS P [lo + 1 ..< hi]
Proof
  simp [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeLHI] >>
  metis_tac [lt_add1]
QED

Theorem bounded_forall_interval_lt_leq:
  (∀n. lo < n ∧ n ≤ hi ⇒ P n) ⇔ EVERY P [lo + 1 .. hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeINC] >>
  metis_tac [lt_add1]
QED

Theorem bounded_exists_interval_lt_leq:
  (∃n. lo < n ∧ n ≤ hi ∧ P n) ⇔ EXISTS P [lo + 1 .. hi]
Proof
  simp [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeINC] >>
  metis_tac [lt_add1]
QED

Theorem bounded_forall_interval_lt_leq_swap:
  (∀n. n ≤ hi ∧ lo < n ⇒ P n) ⇔ EVERY P [lo + 1 .. hi]
Proof
  simp [listTheory.EVERY_MEM, listRangeTheory.MEM_listRangeINC] >>
  metis_tac [lt_add1]
QED

Theorem bounded_exists_interval_lt_leq_swap:
  (∃n. n ≤ hi ∧ lo < n ∧ P n) ⇔ EXISTS P [lo + 1 .. hi]
Proof
  simp [listTheory.EXISTS_MEM, listRangeTheory.MEM_listRangeINC] >>
  metis_tac [lt_add1]
QED

(* Part 5: narrowing represents a function variable by a finite update
   chain, or by a constant when its domain is itself a function type.
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

(* Part 6: fmap's ersatz encoding for the model finder.

   fmap (finite_mapScript.sml) is [new_type_definition] over
   representation type 'a -> 'b + one, restricted by the inductively
   defined is_fmap; is_fmap's own well-foundedness proof does not go
   through automatically, so registering the genuine typedef leaves the
   model finder to unroll it -- an iterative-depth search stacked on an
   already large function-typed carrier, which a probed goal never
   finishes under adaptive defaults.  FUPDATE/FEMPTY/FAPPLY/FDOM are
   themselves [nocompute] and built directly from fmap_ABS/fmap_REP,
   which -- introduced by [define_new_type_bijections], not a
   [Definition] -- have no equation to unfold, so without a typedef
   registration recognizing them the model finder would see them as
   uninterpreted.

   is_fmap'/abs_fmap' below give the model finder its own [fmap]
   typedef, over representation type 'a -> 'b option instead: a plain
   function type, already well supported for scope-search exactness
   (Refute_ModelFinder_Scope.sml), unlike is_fmap's recursive one.
   is_fmap' carries the same FINITE-guarded [unknown] escape as wf'_def
   above, and for the same syntactic reason (FINITE is encoded against
   'a's own type, not against the Kodkod scope).  Measured: dropping the
   [\/ unknown] disjunct from is_fmap'_def (and, correspondingly,
   disj1_tac from is_fmap'_FLOOKUP's proof below) leaves the level-1
   selftest at 939 OK/0 failures, byte-identical to the pre-ablation
   baseline; no pin, including finite_map_model_finder_reaches_genuine,
   is sensitive to the escape's presence.  So the escape's necessity is
   not established by anything in this suite, and the previously stated
   reason for keeping it -- that dropping it "kills the search" over an
   infinite key type in a positive-polarity sound problem -- is refuted
   by that measurement and is not repeated here.  The escape is kept
   anyway, for the same reason wf'_def carries one: FLOOKUP a's domain
   is a HOL-level FINITE claim over 'a's own (possibly infinite) type,
   which the model finder has no general syntactic way to certify True
   at every instance and scope, so removing the escape would trade an
   unmeasured amount of scope-search coverage for no observed benefit;
   see [Refute_ModelFinder_HOL.sml]'s [synthetic_fmap_typedef] comment
   for how FLOOKUP/is_fmap' are actually dispatched at a typedef
   instance, which is the more likely reason no tested goal exercises
   this particular disjunct either way.

   abs_fmap' is Hilbert choice, so it is a real inverse of FLOOKUP only
   where a preimage exists; the theorems below say exactly that, and are
   precisely what a genuine (non-synthetic) HOL typedef would give
   [register_typedef] as its bijection theorem -- [FLOOKUP]/[abs_fmap']/
   [is_fmap'] are all genuine constants at every instance the model finder
   uses, unlike frac's [abs_frac]/[rep_frac], which [retype_constant]
   turns into reserved variables with no proof obligation to discharge
   (Refute_ModelFinder_HOL.sml).  [register_typedef] itself cannot accept
   this typedef: it requires the supplied representation type to match
   fmap's own kernel [fmap_TY_DEF] representation ['a -> 'b + one], and
   this route deliberately uses the simpler ['a -> 'b option] instead (see
   above).  [synthetic_fmap_typedef] (Refute_ModelFinder_HOL.sml) stays,
   but now consumes [abs_fmap'_FLOOKUP]/[FLOOKUP_abs_fmap'] as the
   typedef's inverse axioms, the same slot a validated typedef fills from
   its own bijection theorem.  [FLOOKUP_abs_fmap'] is stated as the full
   biconditional [FINITE {x | f x <> NONE} <=> FLOOKUP (abs_fmap' f) = f]
   rather than the one-way implication a HOL typedef's second bijection
   law states informally: [Refute_ModelFinder_HOL.sml]'s
   [guarded_inverse_axiom] pattern-matches this exact biconditional shape
   to also emit an [onto] surjectivity axiom, which an implication does
   not trigger -- see [guarded_inverse_axiom]'s own comment.  Both
   directions are genuine theorems here (forward: Hilbert choice finds a
   preimage when one exists; backward: [FLOOKUP]'s own range always has
   finite support, via [FDOM_FINITE]), so restating as a biconditional
   loses no generality.

   [is_fmap'_FLOOKUP] below is the fact [is_fmap'_def]'s own comment above
   needs: a typo in [is_fmap'_def] -- a dropped disjunct, [f x = NONE],
   the wrong set -- now fails this proof, exactly as a typo in
   [abs_fmap'_def] already failed [abs_fmap'_FLOOKUP]'s.  That alone pins
   [is_fmap'_def]'s statement, not its *use* as the typedef's [pred]:
   [Refute_ModelFinder_HOL.sml]'s [generic_fmap_typedef] additionally
   checks, at the generic instance every fmap type instantiates, that
   this theorem's instantiated conclusion is literally the membership
   term [pred (rep a)] the module would otherwise construct from
   separately-retyped [is_fmap']/[FLOOKUP] constants, raising if they
   diverge -- so a wiring bug that reassigns [pred] or [rep] to the
   wrong constant fails loudly at module load too, not only a typo
   caught by the theorem's own proof.

   Measured, no fmap-fact pin tried so far is actually load-bearing on
   the inverse axioms: emptying [inverse_axioms] in
   [synthetic_fmap_typedef] and rebuilding turns the level-1 selftest
   from 939 OK/0 failures to 938 OK/1 failure, and the one failure was a
   since-removed mechanism pin on the axiom emission itself, not a fmap
   fact.  Both FLOOKUP injectivity and the ersatz FDOM FEMPTY = {}
   still hold: [FLOOKUP] is dispatched structurally as the typedef's rep
   (constructor/selector encoding, [Refute_ModelFinder_HOL.sml]) and
   [abs_fmap'] unfolds to its own Hilbert-choice body (an ordinary
   [Definition], unlike a genuine typedef's kernel-introduced Abs), so
   [FLOOKUP (abs_fmap' f) = f] comes out true by construction for these
   goals without appeal to [FLOOKUP_abs_fmap'].  This is nonetheless the
   structurally correct thing to supply regardless of whether any one
   goal needs it -- in particular the [onto] half still states a
   coverage guarantee (the abstract carrier is pinned to exactly
   [is_fmap']'s extension, not some subset of it at a proper-subset
   scope) that the structural encoding does not supply by itself, even
   though no goal tried here has been found where dropping it changes a
   verdict; see [Refute_ModelFinder_HOL.sml]'s [synthetic_fmap_typedef]
   comment for the same point and the counts. *)
Definition is_fmap'_def:
  is_fmap' (f : 'a -> 'b option) =
    (FINITE {x | f x <> NONE} \/ unknown)
End

Definition abs_fmap'_def:
  abs_fmap' (f : 'a -> 'b option) = (@fm : 'a |-> 'b. FLOOKUP fm = f)
End

Theorem abs_fmap'_FLOOKUP:
  !fm. abs_fmap' (FLOOKUP fm) = fm
Proof
  simp [abs_fmap'_def, finite_mapTheory.FLOOKUP_EXT] >>
  metis_tac [boolTheory.SELECT_AX]
QED

Theorem FLOOKUP_abs_fmap':
  !f. FINITE {x | f x <> NONE} <=> (FLOOKUP (abs_fmap' f) = f)
Proof
  gen_tac >> eq_tac
  >- (strip_tac >> simp [abs_fmap'_def] >>
      `(\fm. FLOOKUP fm = f) (FUN_FMAP (THE o f) {x | f x <> NONE})` by
        (fs [boolTheory.FUN_EQ_THM, finite_mapTheory.FLOOKUP_FUN_FMAP,
             combinTheory.o_THM, pred_setTheory.GSPECIFICATION] >>
         gen_tac >> Cases_on `f x` >> fs []) >>
      metis_tac [boolTheory.SELECT_AX])
  >- (strip_tac >>
      `{x | f x <> NONE} = FDOM (abs_fmap' f)` by
        (simp [pred_setTheory.EXTENSION, finite_mapTheory.TO_FLOOKUP] >>
         metis_tac []) >>
      simp [finite_mapTheory.FDOM_FINITE])
QED

Theorem is_fmap'_FLOOKUP:
  !fm. is_fmap' (FLOOKUP fm)
Proof
  gen_tac >> simp [is_fmap'_def] >> disj1_tac >>
  `{x | FLOOKUP fm x <> NONE} = FDOM fm` by
    (simp [pred_setTheory.EXTENSION, finite_mapTheory.TO_FLOOKUP] >>
     metis_tac []) >>
  simp [finite_mapTheory.FDOM_FINITE]
QED

(* The [FUPDATE/FEMPTY/FAPPLY/FDOM -> fupdate'/fempty'/fapply'/fdom']
   ersatz rows (Refute_ModelFinder_HOL.sml) redirect fmap's primitives
   through FLOOKUP -- registered as [is_fmap'/abs_fmap']'s rep -- and
   combin$UPDATE/combin$K, both plain, already-unfolded definitions, so
   no operation here ever reaches fmap_ABS/fmap_REP.  FLOOKUP itself gets
   no row of its own: it is the registered rep, read directly by the
   typedef machinery, not reached by unfolding.  FCARD, FRANGE and
   SUBMAP -- checked, not just asserted -- reduce to these four (FCARD
   and SUBMAP to FDOM/FAPPLY, FRANGE to FDOM/FAPPLY via a set
   comprehension) by ordinary unfolding of their own [nocompute]
   equations; further finite_map constants are expected to do the same
   but have not all been checked, so treat this as a narrower claim than
   "every other constant". *)
Definition fupdate'_def:
  fupdate' (fm : 'a |-> 'b) (kv : 'a # 'b) =
    abs_fmap' ((FST kv =+ SOME (SND kv)) (FLOOKUP fm))
End

Definition fempty'_def:
  fempty' = abs_fmap' (K NONE : 'a -> 'b option)
End

Definition fapply'_def:
  fapply' (fm : 'a |-> 'b) k =
    case FLOOKUP fm k of SOME v => v | NONE => unknown
End

Definition fdom'_def:
  fdom' (fm : 'a |-> 'b) k = (FLOOKUP fm k <> NONE)
End
