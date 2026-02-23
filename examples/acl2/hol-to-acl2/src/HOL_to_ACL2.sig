signature HOL_to_ACL2 =
sig
  include Abbrev

  datatype t = datatype HOLsexp_dtype.t

  val basis_defs : thm list

  val unlambda_conj : thm -> thm list * thm

  datatype bundle
    = THM  of string * thm * (thm list * thm) option
    | GOAL of string * term * (thm list * term) option
    | DEF  of thm * (thm list * thm list * thm) option
    | SPEC of term list * thm * (thm list * thm list * thm) option

  val def_bundle : thm -> bundle
  val thm_bundle : string -> thm -> bundle
  val goal_bundle : string -> term -> bundle
  val spec_bundle : term list -> thm -> bundle

  val builtin_const_map : (term * string) list
  val ty_sexp : hol_type -> t
  val tm_sexp : term -> t
  val thm_sexp : thm -> string * t
  val goal_sexp : thm -> string * t
  val def_sexp : thm -> string * t
  val spec_sexp : thm -> string * t
  val pp_sexp : t HOLPP.pprinter
  val pp_defhol : t -> PolyML.pretty
  val pp_bundle : bundle -> PolyML.pretty

  val print_bundles : TextIO.outstream -> bundle list -> unit
  val print_bundles_to_stdout : bundle list -> unit
  val print_bundles_to_file : string -> bundle list -> unit

  val pp_bundle_as_defhols : bundle -> PolyML.pretty

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
