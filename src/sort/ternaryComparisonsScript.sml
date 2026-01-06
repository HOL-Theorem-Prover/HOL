Theory ternaryComparisons

Datatype: ordering = LESS | EQUAL | GREATER
End

fun type_rws ty = #rewrs (TypeBase.simpls_of ty)

val thms =
  LIST_CONJ
    (INST_TYPE[Type.alpha |-> ``:ordering``] REFL_CLAUSE
     :: tl (type_rws ``:ordering``));

Theorem ordering_eq_dec =
  PURE_REWRITE_RULE[GSYM (hd (rev (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))] thms;

Definition bool_compare_def[simp]:
  (bool_compare T T = EQUAL) /\
  (bool_compare F F = EQUAL) /\
  (bool_compare T F = GREATER) /\
  (bool_compare F T = LESS)
End

(* Lifting comparison functions through various type operators *)
Definition pair_compare_def:
  pair_compare c1 c2 (a,b) (x,y) =
     case c1 a x of
        EQUAL => c2 b y
      | res => res
End

Definition option_compare_def[simp]:
  (option_compare c NONE NONE = EQUAL) /\
  (option_compare c NONE (SOME _) = LESS) /\
  (option_compare c (SOME _) NONE = GREATER) /\
  (option_compare c (SOME v1) (SOME v2) = c v1 v2)
End

Definition num_compare_def:
  num_compare n1 n2 =
    if n1 = n2 then
      EQUAL
    else if n1 < n2 then
      LESS
    else
      GREATER
End




(* General results on lists *)
Definition list_compare_def:
   (list_compare cmp [] [] = EQUAL)
/\ (list_compare cmp [] l2 = LESS)
/\ (list_compare cmp l1 [] = GREATER)
/\ (list_compare cmp (x::l1) (y::l2) =
     case cmp (x:'a) y of
       LESS => LESS
     | EQUAL => list_compare cmp l1 l2
     | GREATER => GREATER)
End

Theorem compare_equal:
   (!x y. (cmp x y = EQUAL) = (x = y)) ==>
   !l1 l2. (list_compare cmp l1 l2 = EQUAL) = (l1 = l2)
Proof
 DISCH_THEN (ASSUME_TAC o GSYM)
   THEN NTAC 2 (Induct THENL [ALL_TAC,GEN_TAC])
   THEN TRY (ASM_REWRITE_TAC[] THEN Cases_on `cmp h h'`)
   THEN RW_TAC bool_ss [list_compare_def]
QED

(* looks out of place *)
Definition list_merge_def:
   (list_merge a_lt l1 [] = l1)
/\ (list_merge a_lt [] l2 = l2)
/\ (list_merge a_lt (x:'a :: l1) (y::l2) =
      if a_lt x y
      then x::list_merge a_lt l1 (y::l2)
      else y::list_merge a_lt (x::l1) l2)
End

Definition invert_comparison_def[simp]:
  (invert_comparison GREATER = LESS) /\
  (invert_comparison LESS = GREATER) /\
  (invert_comparison EQUAL = EQUAL)
End

Theorem invert_eq_EQUAL[simp]:
    !x. (invert_comparison x = EQUAL) <=> (x = EQUAL)
Proof
  Cases >> simp[]
QED

val ordering_distinct = DB.fetch "-" "ordering_distinct";

(* below are 2 leaking assumptions when installing hol-ring *)
Theorem ordering_distinct1 :
  ~(EQUAL = LESS)
Proof
  PROVE_TAC [ordering_distinct]
QED

Theorem ordering_distinct2 :
  ~(GREATER = EQUAL)
Proof
  PROVE_TAC [ordering_distinct]
QED

