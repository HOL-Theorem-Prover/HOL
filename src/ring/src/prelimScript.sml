
open HolKernel Parse basicHol90Lib bossLib;

infix THEN THENL;

val _ = new_theory "prelim";


(* ternary comparisons *)
val _ = Hol_datatype ` ordering = LESS | EQUAL | GREATER `;

val compare_def = Define `
   (compare LESS    lt eq gt = lt)
/\ (compare EQUAL   lt eq gt = eq)
/\ (compare GREATER lt eq gt = gt) `

val thms =
  LIST_CONJ
    (INST_TYPE[{redex= ==`:'a`==, residue= ==`:ordering`==}] REFL_CLAUSE
     :: tl (type_rws "ordering"));

val ordering_eq_dec = save_thm("ordering_eq_dec",
  PURE_REWRITE_RULE[GSYM (hd (rev (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))] thms);


(* General results on lists *)

val list_compare_def = Define `
   (list_compare cmp [] [] = EQUAL)
/\ (list_compare cmp [] l2 = LESS)
/\ (list_compare cmp l1 [] = GREATER)
/\ (list_compare cmp (CONS (x:'a) l1) (CONS (y:'a) l2) =
     compare (cmp x y)
     (* x<y *) LESS
     (* x=y *) (list_compare cmp l1 l2)
     (* x>y *) GREATER) `;

val compare_equal = store_thm("compare_equal",
  --` (!x y. (cmp x y = EQUAL) = x = y)
      ==> !l1 l2. (list_compare cmp l1 l2 = EQUAL) = l1 = l2 `--,
DISCH_THEN (fn tha =>
(Induct THENL [ALL_TAC,GEN_TAC]) THEN
(Induct THENL [ALL_TAC,GEN_TAC]) THEN
TRY (REWRITE_TAC[GSYM tha] THEN Cases_on `(cmp (h:'a) (h':'a)):ordering`) THEN
RW_TAC base_ss [list_compare_def, compare_def, GSYM tha, thms]));




val list_merge_def = Define `
   (list_merge a_lt l1 NIL = l1)
/\ (list_merge a_lt NIL l2 = l2)
/\ (list_merge a_lt (CONS (x:'a) l1) (CONS y l2) =
      if a_lt x y then CONS x (list_merge a_lt l1 (CONS y l2))
      else CONS y (list_merge a_lt (CONS x l1) l2)) `;


val _ = export_theory();
