(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)

(* Interactive mode:
  load "word8Lib";
*)
open HolKernel Parse boolLib bossLib word8Lib word8Theory

val _ = new_theory "word8Cases"

fun buildVar name t n = mk_var ((name ^ int_to_string n), t)

val word8Type = mk_type ("word8", [])
val alphaType = mk_vartype "'a"
val nums = upto 0 255
val vars = map (buildVar "w" alphaType) nums
val consts = map (fn n => ``n2w ^(numSyntax.term_of_int n)``) nums


local

val bound_thm = Q.prove (
`!x. ?y. y < 256 /\ (x = n2w y)`,
RW_TAC list_ss [] THEN Q.EXISTS_TAC `w2n x` THEN
RW_TAC arith_ss [fetch "arithmetic" "DIVISION",
                 w2n_ELIM, SIMP_RULE arith_ss [WL_def, HB_def] w2n_LT])

val lem = Q.prove (
 `!c.(0 < c /\ P (c - 1) /\ !n. n < c - 1 ==> P n) ==>(!n. n < c ==> P n)`,
RW_TAC arith_ss [arithmeticTheory.BOUNDED_FORALL_THM]);

in

fun CASES256 w x =
`?n. n < 256 /\ (^w = n2w n)` by RW_TAC std_ss [bound_thm] THEN
RW_TAC std_ss [] THEN (POP_ASSUM MP_TAC) THEN
Q.SPEC_TAC (`n`, `n`) THEN REPEAT (HO_MATCH_MP_TAC lem THEN x)

end

val cases = Q.prove (
`!x. ^(list_mk_disj (map (fn c => ``x = ^c``) (rev consts)))`,
STRIP_TAC THEN CASES256 ``x:word8``
 (CONJ_TAC THENL [RW_TAC arith_ss [], ALL_TAC] THEN
  CONJ_TAC THENL [DISJ1_TAC THEN WORD_TAC,
                  REPEAT STRIP_TAC THEN DISJ2_TAC THEN 
                   POP_ASSUM (MP_TAC o SIMP_RULE arith_ss []) THEN
                   Q.SPEC_TAC (`n`, `n`)]) THEN
Cases THEN RW_TAC arith_ss [])

local

val i_t = numSyntax.term_of_int

val pr_body_eqns = map2 (fn c => fn v => ``fn ^c = ^v``) 
                        consts vars
fun mk_witness low hi = 
  if low = hi then
    List.nth (vars, low)
  else
    let val mid = (hi + low) div 2 in
      mk_cond (``w2n x <= ^(i_t mid)``,
               mk_witness low mid,
               mk_witness (mid + 1) hi)
    end
val pr_witness = ``\x. ^(mk_witness 0 255)``

val use_top_assum = POP_ASSUM (fn thm => PURE_ONCE_REWRITE_TAC [GSYM thm])

val prim_rec = prove (
list_mk_forall (vars, ``?!fn. (\fn. ^(list_mk_conj pr_body_eqns)) fn``),
REPEAT GEN_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN BETA_TAC THEN
REPEAT STRIP_TAC
THENL
 [EXISTS_TAC pr_witness THEN REPEAT STRIP_TAC THEN BETA_TAC THEN WORD_TAC,
  ALL_TAC] THEN
NTAC 256 (POP_ASSUM MP_TAC) THEN
NTAC 256 use_top_assum THEN
REPEAT STRIP_TAC THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
CASES256 ``w:word8`` (SIMP_TAC arith_ss [] THEN CONJ_TAC THENL
              [POP_ASSUM (ACCEPT_TAC o GSYM), POP_ASSUM (K ALL_TAC)]) THEN
Cases_on `n` THEN RW_TAC arith_ss [])
in 

val word8UniquePrimRec = BETA_RULE prim_rec

val word8PrimRec = 
GENL vars
 (BETA_RULE (hd (BODY_CONJUNCTS (REWRITE_RULE [EXISTS_UNIQUE_THM] prim_rec))))

val induct = Prim_rec.prove_induction_thm word8UniquePrimRec

end


val _ = save_thm("word8UniquePrimRec",word8UniquePrimRec);
val _ = save_thm("word8PrimRec",word8PrimRec);
val _ = save_thm("word8Induct",induct);
val _ = save_thm("word8Cases", cases);

(*
local 

val inner_clauses =
     Lib.map2 (fn c => fn v => ``^c -> ^v``) consts vars
val inner_clauses2 = 
    fold_term (fn (x, y) => ``^x || ^y``) inner_clauses

fun mk_thm c v = 
  foldr mk_forall
        ``(case ^c of ^inner_clauses2) = ^v``
        vars

in

end
*)

(*
local

fun fold_term f [x] = x
  | fold_term f (h::t) = f (h, (fold_term f t))

val less_than_lems =
  map (fn n => prove (``^(numSyntax.term_of_int n) < 256``,
                      RW_TAC list_ss [])) nums

val not_eq_thms = flatten
  (List.map (fn i =>
              List.map (fn j =>
                          Q.prove (`~(n2w ^(numSyntax.term_of_int i) =
                                   n2w ^(numSyntax.term_of_int j))`,
                                 SIMP_TAC arith_ss [not_eq_lem]))
                       (upto 0 (i - 1)))
            nums)

in
val distinct = LIST_CONJ not_eq_thms
end

*)
val _ = export_theory();

