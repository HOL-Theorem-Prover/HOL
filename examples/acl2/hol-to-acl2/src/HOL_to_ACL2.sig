signature HOL_to_ACL2 =
sig
  include Abbrev

  datatype t = datatype HOLsexp_dtype.t

  val basis_defs : thm list
  val builtin_const_map : (term * string) list
  val ty_sexp : hol_type -> t
  val tm_sexp : term -> t
  val thm_sexp : thm -> string * t
  val goal_sexp : thm -> string * t
  val def_sexp : thm -> string * t
  val spec_sexp : thm -> string * t
  val hol_sexp : thm -> string * t
  val pp_sexp : t HOLPP.pprinter
  val pp_defhol : t -> PolyML.pretty

  val print_defhols : TextIO.outstream -> thm list -> unit
  val print_defhols_to_stdout : thm list -> unit
  val print_defhols_to_file : string -> thm list -> unit

  val mk_named_thm : string -> thm -> thm
  val mk_named_goal : string -> term -> thm
  val mk_spec : term list -> thm -> thm
  val dest_named_thm : thm -> string * term
  val dest_named_goal : thm -> string * term
  val dest_spec : thm -> term list * term
  val dest_def :
   thm ->
     {fns: term list,
      defs: (term list * ((term * term list) * term)) list}

end
