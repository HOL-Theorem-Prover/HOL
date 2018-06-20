open HolKernel Parse boolLib bossLib testutils miller_rabinTools

val prime_t = prim_mk_const{Name = "prime", Thy = "divides"}

datatype t = N of int | T of int

fun test0 n_t =
  let
    val _ = tprint ("Composite test on "^Parse.term_to_string n_t)
    val nprime_n = mk_neg (mk_comb(prime_t, n_t))
    fun c th = if aconv nprime_n (concl th) then OK() else die "FAILED!"
  in
    timed COMPOSITE_PROVER (exncheck c) n_t
  end

fun mkN n = numSyntax.mk_numeral (Arbnum.fromInt n)

fun test (N n) = test0 (mkN n)
  | test (T n) = test0 (``2 ** 2 ** ^(mkN n) + 1`` |> EVAL |> concl |> rhs)

val _ = app test [N 91, N 123, T 5,
                  T 6, (* takes ~3s on 2014 Macbook Pro *)
                  T 7 (* takes ~25s on 2014 Macbook Pro *)
                  (* , T 8 takes 194s on 2014 Macbook Pro *)
                 ]
;
