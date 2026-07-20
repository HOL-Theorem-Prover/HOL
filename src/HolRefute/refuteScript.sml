Theory refute
Ancestors
  real sorting words
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

Datatype:
  bitword = Bitword ('a -> bool)
End
