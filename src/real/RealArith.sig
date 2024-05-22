signature RealArith =
sig
  include Abbrev

  type positivstellensatz
  type rat = Arbrat.rat
  type aint = Arbint.int

  val is_realintconst      : term -> bool
  val dest_realintconst    : term -> aint
  val mk_realintconst      : aint -> term
  val is_ratconst          : term -> bool
  val rat_of_term          : term -> rat
  val term_of_rat          : rat -> term
  val mk_real_arith_tac    : (term -> thm) -> tactic * tactic

  val REAL_INT_LE_CONV     : conv
  val REAL_INT_LT_CONV     : conv
  val REAL_INT_GE_CONV     : conv
  val REAL_INT_GT_CONV     : conv
  val REAL_INT_EQ_CONV     : conv
  val REAL_INT_ADD_CONV    : conv
  val REAL_INT_SUB_CONV    : conv
  val REAL_INT_NEG_CONV    : conv
  val REAL_INT_MUL_CONV    : conv
  val REAL_INT_POW_CONV    : conv
  val REAL_INT_ABS_CONV    : conv

  val REAL_INT_REDUCE_CONV : conv
  val real_int_compset     : unit -> computeLib.compset

 (* fn translator (eq,le,lt) -> 'a *)
  val REAL_LINEAR_PROVER   : (thm list * thm list * thm list ->
                              positivstellensatz -> 'a) ->
                             thm list * thm list * thm list -> 'a

 (* for REAL_LINEAR_PROVER, 0: nothing, 1: minimal, 2+: details *)
  val verbose_level        : int ref (* default: 1 *)

 (* fn (mkconst,EQ,GE,GT,NORM,NEG,ADD,MUL,PROVER) -> term -> thm *)
  val GEN_REAL_ARITH       :
     (rat -> term) * conv * conv * conv * conv * conv * conv * conv *
     ((thm list * thm list * thm list -> positivstellensatz -> thm) ->
       thm list * thm list * thm list -> thm) -> term -> thm

 (* NOTE: users are recommended to use the final versions in RealField *)
  val REAL_ARITH           : term -> thm
  val REAL_ARITH_TAC       : tactic
  val REAL_ASM_ARITH_TAC   : tactic

end
