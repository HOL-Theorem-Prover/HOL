(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)

(* Interactive mode:
  load "word8Lib";*)

open HolKernel Parse boolLib bossLib word8Lib word8Theory

val _ = new_theory "word8Cases"

fun buildVar name t n = mk_var ((name ^ int_to_string n), t)
val nums = upto 0 255
val vars = map (buildVar "w" alpha) nums
val consts = map (fn n => ``n2w ^(numSyntax.term_of_int n)``) nums

val bound_thm = Q.prove (
`!x. ?y. y < 256 /\ (x = n2w y)`,
RW_TAC list_ss [] THEN Q.EXISTS_TAC `w2n x` THEN
RW_TAC arith_ss [fetch "arithmetic" "DIVISION",
                 w2n_ELIM, SIMP_RULE arith_ss [WL_def, HB_def] w2n_LT])

val lem = Q.prove (
 `!c.(0 < c /\ P (c - 1) /\ !n. n < c - 1 ==> P n) ==>(!n. n < c ==> P n)`,
RW_TAC arith_ss [arithmeticTheory.BOUNDED_FORALL_THM]);

fun CASES256 w x =
`?n. n < 256 /\ (^w = n2w n)` by RW_TAC std_ss [bound_thm] THEN
RW_TAC std_ss [] THEN (POP_ASSUM MP_TAC) THEN
Q.SPEC_TAC (`n`, `n`) THEN REPEAT (HO_MATCH_MP_TAC lem THEN x)

val nchotomy = Q.prove (
`!x. ^(list_mk_disj (map (fn c => ``x = ^c``) (rev consts)))`,
STRIP_TAC THEN CASES256 ``x:word8``
 (CONJ_TAC THENL [RW_TAC arith_ss [], ALL_TAC] THEN
  CONJ_TAC THENL [DISJ1_TAC THEN WORD_TAC,
                  REPEAT STRIP_TAC THEN DISJ2_TAC THEN 
                   POP_ASSUM (MP_TAC o SIMP_RULE arith_ss []) THEN
                   Q.SPEC_TAC (`n`, `n`)]) THEN
Cases THEN RW_TAC arith_ss [])

val _ = save_thm ("word8Nchotomy", nchotomy);

fun mk_body low hi var results = 
  if low = hi then
    List.nth (results, low)
  else
    let val mid = (hi + low) div 2 in
      mk_cond (``w2n ^var <= ^(numSyntax.term_of_int mid)``,
               mk_body low mid var results,
               mk_body (mid + 1) hi var results)
    end

val body = mk_body 0 255 ``x:word8`` vars

val word8_cases_def = Define
`word8_cases = ^(list_mk_abs (vars, ``\x.^body``))`;

(*
val f = #1 (dest_eq (concl word8_cases_def));
val clauses =
  map2 (fn c => fn v =>
          ``^(mk_comb (list_mk_comb (f, vars), c)) = ^v``)
       consts vars
                 
val thms = 
  map (fn clause =>
         prove (clause, PURE_ONCE_REWRITE_TAC [word8_cases_def] THEN WORD_TAC))
      clauses

val cases = LIST_CONJ thms

val _ = save_thm("word8Cases", cases);
*)

val pr_body_eqns = map2 (fn c => fn v => ``fn ^c = ^v``) 
                        consts vars

val use_top_assum = POP_ASSUM (fn thm => PURE_ONCE_REWRITE_TAC [GSYM thm])

val witness =
 snd (dest_eq (concl (BETA_RULE (PURE_ONCE_REWRITE_CONV [word8_cases_def]
                                  (list_mk_comb (``word8_cases``, vars))))))

val prim_rec = prove (
list_mk_forall (vars, ``?!fn. (\fn. ^(list_mk_conj pr_body_eqns)) fn``),
REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
BETA_TAC THEN REPEAT STRIP_TAC
THENL
 [EXISTS_TAC witness THEN REPEAT STRIP_TAC THEN WORD_TAC,
  ALL_TAC] THEN
NTAC 256 (POP_ASSUM MP_TAC) THEN
NTAC 256 use_top_assum THEN
REPEAT STRIP_TAC THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
CASES256 ``w:word8`` (SIMP_TAC arith_ss [] THEN CONJ_TAC THENL
              [POP_ASSUM (ACCEPT_TAC o GSYM), POP_ASSUM (K ALL_TAC)]) THEN
Cases_on `n` THEN RW_TAC arith_ss [])

val word8UniquePrimRec = BETA_RULE prim_rec

val word8PrimRec = 
GENL vars
 (BETA_RULE (hd (BODY_CONJUNCTS (REWRITE_RULE [EXISTS_UNIQUE_THM] prim_rec))))

val induct = Prim_rec.prove_induction_thm word8UniquePrimRec

val _ = save_thm ("word8PrimRec", word8PrimRec)
val _ = save_thm ("word8UniquePrimRec", word8UniquePrimRec)
val _ = save_thm ("word8Induct", induct);

val _ = export_theory();
