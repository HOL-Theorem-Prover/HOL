open HolKernel Parse basicHol90Lib
     TotalDefn Datatype BasicProvers SingleStep;

infix THEN THENL |->;

val _ = new_theory "prelim";


(* ternary comparisons *)
val _ = Hol_datatype ` ordering = LESS | EQUAL | GREATER `;

val _ = set_MLname "LESS" "LESS_def";
val _ = set_MLname "EQUAL" "EQUAL_def";
val _ = set_MLname "GREATER" "GREATER_def";

val compare_def = Define `
   (compare LESS    lt eq gt = lt)
/\ (compare EQUAL   lt eq gt = eq)
/\ (compare GREATER lt eq gt = gt) `

fun type_rws tyn = TypeBase.simpls_of (valOf (TypeBase.read tyn));

val thms =
  LIST_CONJ
    (INST_TYPE[Type.alpha |-> Type`:ordering`] REFL_CLAUSE
     :: tl (type_rws "ordering"));

val ordering_eq_dec = save_thm("ordering_eq_dec",
  PURE_REWRITE_RULE[GSYM (hd (rev (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))] thms);


(* General results on lists *)

val list_compare_def = Define `
   (list_compare cmp [] [] = EQUAL)
/\ (list_compare cmp [] l2 = LESS)
/\ (list_compare cmp l1 [] = GREATER)
/\ (list_compare cmp (x::l1) (y::l2) =
     compare (cmp (x:'a) y)
     (* x<y *) LESS
     (* x=y *) (list_compare cmp l1 l2)
     (* x>y *) GREATER) `;

val compare_equal = store_thm("compare_equal",
  --` (!x y. (cmp x y = EQUAL) = (x = y))
      ==> !l1 l2. (list_compare cmp l1 l2 = EQUAL) = (l1 = l2)`--,
DISCH_THEN (fn tha =>
(Induct THENL [ALL_TAC,GEN_TAC]) THEN
(Induct THENL [ALL_TAC,GEN_TAC]) THEN
TRY (REWRITE_TAC[GSYM tha] THEN Cases_on `(cmp (h:'a) (h':'a)):ordering`) THEN
RW_TAC bool_ss [list_compare_def, compare_def, GSYM tha, thms]));



val list_merge_def = Define `
   (list_merge a_lt l1 [] = l1)
/\ (list_merge a_lt [] l2 = l2)
/\ (list_merge a_lt (x:'a :: l1) (y::l2) =
      if a_lt x y
      then x::list_merge a_lt l1 (y::l2)
      else y::list_merge a_lt (x::l1) l2) `;


val _ = export_theory();
