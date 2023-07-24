signature FinalThm =
sig
  type thm
  type tag
  type term
  type hol_type
  type 'a set   = 'a HOLset.set
  type depdisk  = (string * int) * ((string * int list) list)

  val kernelid : string

  (* Simple operations on the type of theorems *)

  val tag           : thm -> tag
  val hyp           : thm -> term list
  val hypset        : thm -> term set
  val concl         : thm -> term
  val dest_thm      : thm -> term list * term
  val thm_frees     : thm -> term list
  val hyp_frees     : thm -> term set
  val hyp_tyvars    : thm -> hol_type set


  (* The primitive rules of inference *)

  val ASSUME        : term -> thm
  val REFL          : term -> thm
  val BETA_CONV     : term -> thm
  val ABS           : term -> thm -> thm
  val DISCH         : term -> thm -> thm
  val MP            : thm -> thm -> thm
  val SUBST         : (term,thm)Lib.subst -> term -> thm -> thm
  val INST_TYPE     : (hol_type,hol_type)Lib.subst -> thm -> thm


  (* Now some derivable-but-primitive rules of inference *)


  (* Lambda calculus rules *)

  val ALPHA         : term -> term -> thm
  val MK_COMB       : thm * thm -> thm
  val AP_TERM       : term -> thm -> thm
  val AP_THM        : thm -> term -> thm


  (* Equality *)

  val SYM           : thm -> thm
  val TRANS         : thm -> thm -> thm
  val EQ_MP         : thm -> thm -> thm
  val EQ_IMP_RULE   : thm -> thm * thm


  (* Free variable instantiation *)

  val INST          : (term,term)Lib.subst -> thm -> thm


  (* Universal quantification *)

  val SPEC          : term -> thm -> thm
  val GEN           : term -> thm -> thm
  val GENL          : term list -> thm -> thm


  (* Existential quantification *)

  val EXISTS        : term * term -> thm -> thm
  val CHOOSE        : term * thm -> thm -> thm


  (* Conjunction *)

  val CONJ          : thm -> thm -> thm
  val CONJUNCT1     : thm -> thm
  val CONJUNCT2     : thm -> thm


  (* Disjunction *)

  val DISJ1         : thm -> term -> thm
  val DISJ2         : term -> thm -> thm
  val DISJ_CASES    : thm -> thm -> thm -> thm


  (* Negation *)

  val NOT_INTRO     : thm -> thm
  val NOT_ELIM      : thm -> thm
  val CCONTR        : term -> thm -> thm


  (* Computing with explicit substitutions *)

  val Beta          : thm -> thm
  val Mk_comb       : thm -> thm * thm * (thm -> thm -> thm)
  val Mk_abs        : thm -> term * thm * (thm -> thm)
  val Specialize    : term -> thm -> thm

  (* Multiple binders *)

  val GEN_ABS       : term option -> term list -> thm -> thm

  (* Oracle invocation *)

  val mk_thm        : term list * term -> thm
  val mk_oracle_thm : string -> term list * term -> thm
  val mk_axiom_thm  : (string Nonce.t * term) -> thm
  val add_tag       : tag * thm -> thm

  (* definitional rules of inference *)
  val prim_type_definition : {Thy : string, Tyop : string} * thm -> thm
  val prim_specification : string -> string list -> thm -> thm
  val gen_prim_specification : string -> thm -> string list * thm

  (* Fetching theorems from disk *)

  val disk_thm : (depdisk * string list) * term list -> thm

  (* Saving proof dependencies *)

  val save_dep : string -> thm -> thm

  (* Computing with first-order lisp-style expressions *)

  val compute :
    (* initialization: *)
    { cval_terms : (string * term) list,
      cval_type  : hol_type,
      num_type   : hol_type,
      char_eqns  : (string * thm) list }
    (* code equations: *)
    -> thm list
    -> term -> thm

end;

