signature EmitML = 
sig
  include Abbrev

  val reshape_thm_hook : (thm -> thm) ref
  val pseudo_constr_rws : unit -> term list
  val new_pseudo_constr : term * int -> unit 
  val is_int_literal_hook : (term -> bool) ref
  val int_of_term_hook : (term -> Arbint.int) ref

  datatype side = LEFT | RIGHT

  val pp_type_as_ML     : ppstream -> hol_type -> unit
  val pp_term_as_ML     : string list -> side -> ppstream -> term -> unit
  val pp_defn_as_ML     : string list -> ppstream -> term -> unit
  val pp_datatype_as_ML : ppstream -> string list * ParseDatatype.AST list -> unit

  datatype elem = DEFN of thm
                | DEFN_NOSIG of thm
                | DATATYPE of hol_type quotation
                | EQDATATYPE of string list * hol_type quotation
                | ABSDATATYPE of string list * hol_type quotation
                | OPEN of string list
                | MLSIG of string
                | MLSTRUCT of string

  val MLSIGSTRUCT      : string list -> elem list

  val sigSuffix        : string ref 
  val structSuffix     : string ref 
  val sigCamlSuffix    : string ref 
  val structCamlSuffix : string ref 

  val emitML   : string -> string * elem list -> unit
  val emitCAML : string -> string * elem list -> unit

  val eSML     : string -> elem list -> unit
  val eCAML    : string -> elem list -> unit
end
