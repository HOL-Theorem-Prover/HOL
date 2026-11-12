(* Certificate arithmetic conversions; see certificateComputeLib.sig.
   NAT_CONV normalizes natural arithmetic without rewriting Boolean structure.
   EVAL_COMPSET / EVAL_CONV snapshot the currently loaded compute equations;
   retain the resulting context for repeated bounded calculations.
   MODPOW_CONV checks closed a ** e MOD n through the shared expMod program
   and standard CV translations. All results are kernel equalities, not
   trusted answers from external arithmetic. *)

structure certificateComputeLib :> certificateComputeLib =
struct

open HolKernel boolLib Conv

open cv_stdTheory

(* Unlike numLib.REDUCE_CONV's numeral-rewrite compset, these primitive
   conversions use the modern kernel CV arithmetic implementation. *)
val nat_step = FIRST_CONV
  [Arithconv.ADD_CONV, Arithconv.EVEN_CONV, Arithconv.DIV_CONV,
   Arithconv.EXP_CONV, Arithconv.GE_CONV, Arithconv.GT_CONV,
   Arithconv.LE_CONV, Arithconv.LT_CONV, Arithconv.MOD_CONV,
   Arithconv.MUL_CONV, Arithconv.NEQ_CONV, Arithconv.ODD_CONV,
   Arithconv.PRE_CONV, Arithconv.SBC_CONV, Arithconv.SUC_CONV]
(* Leave Boolean normalization to the computation engine: the legacy
   reduceLib Boolean conversions can change negation into implication. *)
fun NAT_CONV tm =
  (* Numeral bit trees are already values; do not revisit every BIT1/BIT2. *)
  if numSyntax.is_numeral tm then REFL tm
  else (SUB_CONV NAT_CONV THENC TRY_CONV nat_step) tm

val binary =
  [numSyntax.plus_tm,numSyntax.minus_tm,numSyntax.mult_tm,
   numSyntax.exp_tm,numSyntax.div_tm,numSyntax.mod_tm,
   numSyntax.less_tm,numSyntax.leq_tm,
   numSyntax.greater_tm,numSyntax.geq_tm]
val unary =
  [numSyntax.suc_tm,numSyntax.pre_tm,numSyntax.even_tm,numSyntax.odd_tm]

fun EVAL_COMPSET () =
  let
    (* External conversions append after existing rewrites, so replace those
       rules. Leave polymorphic equality and its datatype support untouched. *)
    fun install arity (head,cs) =
      computeLib.add_conv (head,arity,nat_step) (computeLib.scrub_const cs head)
    val cs = List.foldl (install 1)
      (List.foldl (install 2) (computeLib.copy (computeLib.the_compset ()))
        binary) unary
  in
    (* Compile dependent equations after installing their private callbacks. *)
    computeLib.add_thms
      [certificateComputeTheory.certificate_gf_add,
       certificateComputeTheory.certificate_gf_mult] cs
  end

fun EVAL_CONV () = computeLib.CBV_CONV (EVAL_COMPSET ())

val normalise_modpow =
  RATOR_CONV (RAND_CONV (BINOP_CONV NAT_CONV)) THENC RAND_CONV NAT_CONV

val evaluate_modpow =
  REWR_CONV (GSYM expModTheory.exp_mod_binary_eqn) THENC cv_transLib.cv_eval

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
