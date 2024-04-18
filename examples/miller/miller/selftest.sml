open HolKernel Parse boolLib bossLib testutils miller_rabinTools

val prime_t = prim_mk_const{Name = "prime", Thy = "divides"}

datatype t = N of int | T of int

fun test0 n_t =
  let
    val _ = tprint ("Composite test on "^Parse.term_to_string n_t)
    val nprime_n = mk_neg (mk_comb(prime_t, n_t))
  in
    require (check_result (aconv nprime_n o concl)) COMPOSITE_PROVER n_t
  end

fun mkN n = numSyntax.mk_numeral (Arbnum.fromInt n)

fun test (N n) = test0 (mkN n)
  | test (T n) = test0 (``2 ** (2 ** ^(mkN n)) + 1n`` |> EVAL |> concl |> rhs)

open Systeml
val _ = app (ignore o test)
            [N 91, N 123, T 5,
             T 6, (* takes ~3s on 2014 Macbook Pro *)
             T 7 (* takes ~25s on 2014 Macbook Pro *)
               (* , T 8 takes 194s on 2014 Macbook Pro *)
            ]
;
