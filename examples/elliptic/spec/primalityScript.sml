(* ========================================================================= *)
(* Create "primalityTheory" supporting the primality prover                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load 
  ["bossLib", "metisLib",
   "arithmeticTheory", "dividesTheory", "gcdTheory"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib;
open arithmeticTheory dividesTheory gcdTheory;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "primality".                                    *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "primality";

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

val divides_mod_zero = store_thm
  ("divides_mod_zero",
   ``!m n. 0 < n ==> (divides n m = (m MOD n = 0))``,
   RW_TAC std_ss [divides_def]
   ++ (EQ_TAC ++ STRIP_TAC)
   ++ RW_TAC std_ss [MOD_EQ_0]
   ++ MP_TAC (Q.SPEC `n` DIVISION)
   ++ ASM_SIMP_TAC std_ss []
   ++ DISCH_THEN (MP_TAC o Q.SPEC `m`)
   ++ ASM_SIMP_TAC arith_ss []
   ++ METIS_TAC []);

(* ------------------------------------------------------------------------- *)
(* Primality prover.                                                         *)
(* ------------------------------------------------------------------------- *)

val (nat_sqrt_def,nat_sqrt_ind) = Defn.tprove
  (Defn.Hol_defn "nat_sqrt"
   `nat_sqrt n k = if n < k * k then k - 1 else nat_sqrt n (k + 1)`,
   WF_REL_TAC `measure (\(n,k). (n + 1) - k)`
   ++ RW_TAC arith_ss [NOT_LESS]
   ++ Suff `k <= n` >> DECIDE_TAC
   ++ Cases_on `k = 0` >> RW_TAC arith_ss []
   ++ Suff `k * k <= k * n` >> RW_TAC arith_ss [LE_MULT_LCANCEL]
   ++ MATCH_MP_TAC LESS_EQ_TRANS
   ++ Q.EXISTS_TAC `1 * n`
   ++ CONJ_TAC >> RW_TAC arith_ss []
   ++ RW_TAC bool_ss [LE_MULT_RCANCEL]
   ++ DECIDE_TAC);

val prime_checker_def = Define
  `prime_checker n i =
   if i <= 1 then T
   else if n MOD i = 0 then F
   else prime_checker n (i - 1)`;

val prime_checker_ind = fetch "-" "prime_checker_ind";

val nat_sqrt = store_thm
  ("nat_sqrt",
   ``!n k. k * k <= n = k <= nat_sqrt n 0``,
   RW_TAC std_ss []
   ++ Suff `!n i k. k * k <= n \/ k < i = k <= nat_sqrt n i`
   >> METIS_TAC [ZERO_LESS_EQ, prim_recTheory.NOT_LESS_0]
   ++ recInduct nat_sqrt_ind
   ++ RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [nat_sqrt_def]
   ++ Cases_on `n < k * k`
   >> (RW_TAC std_ss []
       ++ Q.PAT_ASSUM `X ==> Y` (K ALL_TAC)
       ++ Cases_on `k = 0`
       >> (RW_TAC std_ss []
           ++ FULL_SIMP_TAC arith_ss [])
       ++ MATCH_MP_TAC (PROVE [] ``(~b ==> ~a) /\ (b = c) ==> (a \/ b = c)``)
       ++ REVERSE CONJ_TAC >> DECIDE_TAC
       ++ Suff `k <= k' ==> n < k' * k'` >> DECIDE_TAC
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC LESS_LESS_EQ_TRANS
       ++ Q.EXISTS_TAC `k * k`
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC LESS_EQ_TRANS
       ++ Q.EXISTS_TAC `k * k'`
       ++ RW_TAC arith_ss [LE_MULT_LCANCEL, LE_MULT_RCANCEL])
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MATCH_MP_TAC
        (PROVE [] ``(b ==> c) /\ (~a /\ c ==> b) ==> (a \/ b = a \/ c)``)
   ++ CONJ_TAC >> DECIDE_TAC
   ++ RW_TAC std_ss []
   ++ Suff `~(k = k')` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC arith_ss []);

val prime_condition = store_thm
  ("prime_condition",
   ``!p. prime p = 1 < p /\ !n. 1 < n /\ n * n <= p ==> ~(p MOD n = 0)``,
   STRIP_TAC
   ++ Know `(p = 0) \/ 0 < p` >> DECIDE_TAC
   ++ STRIP_TAC >> RW_TAC bool_ss [NOT_PRIME_0, prim_recTheory.NOT_LESS_0]
   ++ RW_TAC std_ss [prime_def]
   ++ MATCH_MP_TAC
        (PROVE [] ``(a = d) /\ (a /\ d ==> (b = c)) ==> (a /\ b = d /\ c)``)
   ++ CONJ_TAC >> DECIDE_TAC
   ++ STRIP_TAC
   ++ Know `!n. 1 < n ==> 0 < n` >> DECIDE_TAC
   ++ DISCH_THEN (fn th => RW_TAC std_ss [GSYM divides_mod_zero, th])
   ++ EQ_TAC
   >> (RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `!b. P b` (MP_TAC o Q.SPEC `n`)
       ++ REVERSE (RW_TAC std_ss []) >> DECIDE_TAC
       ++ STRIP_TAC
       ++ RW_TAC std_ss []
       ++ Know `(n = 0) \/ n <= 1` >> METIS_TAC [LE_MULT_LCANCEL, MULT_CLAUSES]
       ++ RW_TAC arith_ss [])
   ++ RW_TAC std_ss []
   ++ Cases_on `b = 1` >> RW_TAC std_ss []
   ++ Cases_on `b = p` >> RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `divides b p` MP_TAC
   ++ RW_TAC std_ss [divides_def]
   ++ STRIP_TAC
   ++ RW_TAC std_ss []
   ++ Cases_on `q = 1` >> FULL_SIMP_TAC arith_ss []
   ++ Cases_on `q = 0` >> FULL_SIMP_TAC arith_ss []
   ++ Cases_on `b = 0` >> FULL_SIMP_TAC arith_ss []
   ++ Q.PAT_ASSUM `!n. P n`
        (fn th => MP_TAC (Q.SPEC `q` th) ++ MP_TAC (Q.SPEC `b` th))
   ++ REVERSE (RW_TAC arith_ss [divides_def, LE_MULT_LCANCEL])
   >> METIS_TAC [MULT_COMM]
   ++ REVERSE (Cases_on `b <= q`) >> DECIDE_TAC
   ++ METIS_TAC [MULT_COMM]);

val prime_checker = store_thm
  ("prime_checker",
   ``!p. prime p = 1 < p /\ prime_checker p (nat_sqrt p 0)``,
   RW_TAC std_ss [prime_condition]
   ++ Cases_on `p = 0` >> RW_TAC arith_ss []
   ++ Cases_on `p = 1` >> RW_TAC arith_ss []
   ++ RW_TAC arith_ss []
   ++ Suff `!p k. prime_checker p k = !i. 1 < i /\ i <= k ==> ~(p MOD i = 0)`
   >> (DISCH_THEN (fn th => RW_TAC arith_ss [th])
       ++ RW_TAC arith_ss [GSYM nat_sqrt])
   ++ recInduct prime_checker_ind
   ++ RW_TAC arith_ss []
   ++ ONCE_REWRITE_TAC [prime_checker_def]
   ++ RW_TAC arith_ss []
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `i = 0` >> RW_TAC arith_ss []
   ++ Cases_on `i = 1` >> RW_TAC arith_ss []
   ++ ASM_SIMP_TAC arith_ss []
   ++ Cases_on `n MOD i = 0`
   >> (RW_TAC arith_ss []
       ++ Q.EXISTS_TAC `i`
       ++ RW_TAC arith_ss [])
   ++ RW_TAC arith_ss []
   ++ POP_ASSUM (K ALL_TAC)
   ++ REVERSE EQ_TAC
   >> RW_TAC arith_ss []
   ++ RW_TAC arith_ss []
   ++ Suff `i' <= i - 1 \/ (i' = i)` >> METIS_TAC []
   ++ DECIDE_TAC);

val () = export_theory ();
