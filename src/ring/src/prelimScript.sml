open HolKernel Parse boolLib listTheory
     TotalDefn Datatype BasicProvers;

infix THEN THENL |->;

val _ = new_theory "prelim";


(* ternary comparisons *)

val _ = Hol_datatype `ordering = LESS | EQUAL | GREATER`;

val _ = set_MLname "LESS" "LESS_def";
val _ = set_MLname "EQUAL" "EQUAL_def";
val _ = set_MLname "GREATER" "GREATER_def";

val compare_def = Define `
   (compare LESS    lt eq gt = lt)
/\ (compare EQUAL   lt eq gt = eq)
/\ (compare GREATER lt eq gt = gt) `

fun type_rws ty = #rewrs (TypeBase.simpls_of ty)

val thms =
  LIST_CONJ
    (INST_TYPE[Type.alpha |-> ``:ordering``] REFL_CLAUSE
     :: tl (type_rws ``:ordering``));

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
 DISCH_THEN (ASSUME_TAC o GSYM)
   THEN NTAC 2 (Induct THENL [ALL_TAC,GEN_TAC])
   THEN TRY (ASM_REWRITE_TAC[] THEN Cases_on `cmp h h'`)
   THEN RW_TAC bool_ss [list_compare_def, compare_def]);

val list_merge_def = Define `
   (list_merge a_lt l1 [] = l1)
/\ (list_merge a_lt [] l2 = l2)
/\ (list_merge a_lt (x:'a :: l1) (y::l2) =
      if a_lt x y
      then x::list_merge a_lt l1 (y::l2)
      else y::list_merge a_lt (x::l1) l2) `;


val _ = export_theory();
