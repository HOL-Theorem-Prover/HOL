signature Thm =
sig
  include FinalThm

  val trace_id      : thm -> int
  val trace_counter : int ref
  datatype trace_step =
      TR_ASSUME      of thm * term
    | TR_REFL        of thm * term
    | TR_BETA_CONV   of thm * term
    | TR_SUBST       of thm * {redex: term, residue: thm} list * term * thm
    | TR_ABS         of thm * thm * term
    | TR_GEN_ABS     of thm * thm * term option * term list
    | TR_INST_TYPE   of thm * thm * {redex: hol_type, residue: hol_type} list
    | TR_DISCH       of thm * thm * term
    | TR_MP          of thm * thm * thm
    | TR_ALPHA       of thm * term * term
    | TR_SYM         of thm * thm
    | TR_TRANS       of thm * thm * thm
    | TR_MK_COMB     of thm * thm * thm
    | TR_AP_TERM     of thm * thm * term
    | TR_AP_THM      of thm * thm * term
    | TR_EQ_MP       of thm * thm * thm
    | TR_EQ_IMP_RULE1 of thm * thm
    | TR_EQ_IMP_RULE2 of thm * thm
    | TR_SPEC        of thm * thm * term
    | TR_GEN         of thm * thm * term
    | TR_GENL        of thm * thm * term list
    | TR_EXISTS      of thm * thm * term * term
    | TR_CHOOSE      of thm * thm * thm * term
    | TR_CONJ        of thm * thm * thm
    | TR_CONJUNCT1   of thm * thm
    | TR_CONJUNCT2   of thm * thm
    | TR_DISJ1       of thm * thm * term
    | TR_DISJ2       of thm * thm * term
    | TR_DISJ_CASES  of thm * thm * thm * thm
    | TR_NOT_INTRO   of thm * thm
    | TR_NOT_ELIM    of thm * thm
    | TR_CCONTR      of thm * thm * term
    | TR_INST        of thm * thm * {redex: term, residue: term} list
    | TR_Beta        of thm * thm
    | TR_Mk_comb     of thm * thm * thm * thm
    | TR_Mk_abs      of thm * thm * thm * term
    | TR_Specialize  of thm * thm * term
    | TR_ORACLE      of thm * string
    | TR_AXIOM       of thm * term
    | TR_DEF_TYOP    of thm * thm * string * string
    | TR_DEF_SPEC    of thm * thm
    | TR_DISK_THM    of thm
    | TR_COMPUTE     of thm * thm list * term * term
  val trace_hook : (trace_step -> unit) option ref
  val trace_export_hook :
    (string -> string list -> (string * thm) list -> unit) option ref
  val trace_export : string -> string list -> (string * thm) list -> unit
end
