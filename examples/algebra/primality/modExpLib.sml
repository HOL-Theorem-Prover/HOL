(* efficient checked Modular exponentiation and arithmetic conversions; 
   NAT_CONV normalizes natural arithmetic without rewriting Boolean structure.
   MODPOW_CONV checks closed a ** e MOD n by the proved CV binary program,
*)
structure modExpLib :> modExpLib =
struct

open HolKernel boolLib Conv

(* Unlike numLib.REDUCE_CONV's numeral-rewrite compset, these primitive
   conversions use the modern kernel CV arithmetic implementation. *)
val nat_step = FIRST_CONV
  [Arithconv.DIV_CONV, Arithconv.LT_CONV, Arithconv.MUL_CONV,
   Arithconv.NEQ_CONV, Arithconv.SBC_CONV]
(* Normalize only certificate arithmetic; leave Boolean structure unchanged. *)
fun NAT_CONV tm =
  (* Numeral bit trees are already values; do not revisit every BIT1/BIT2. *)
  if numSyntax.is_numeral tm then REFL tm
  else (SUB_CONV NAT_CONV THENC TRY_CONV nat_step) tm

val eval_modpow = cv_computeLib.cv_compute
  [modExpTheory.modExp_cv_modpow_eq]

val normalise_modpow =
  RATOR_CONV (RAND_CONV (BINOP_CONV NAT_CONV)) THENC RAND_CONV NAT_CONV

val evaluate_modpow =
  REWR_CONV modExpTheory.modExp_modpow_to_cv THENC
  RAND_CONV eval_modpow THENC REWR_CONV CONJUNCT1 cvTheory.c2n_def

fun MODPOW_CONV tm =
  let
    val (power,_) = numSyntax.dest_mod tm
    val _ = numSyntax.dest_exp power
    val norm = QCONV normalise_modpow tm
    val closed = rhs (concl norm)
    val (power,n) = numSyntax.dest_mod closed
    val (a,e) = numSyntax.dest_exp power
    val _ = List.app (ignore o numSyntax.dest_numeral) [a,e,n]
  in
    TRANS norm (evaluate_modpow closed)
  end

end
