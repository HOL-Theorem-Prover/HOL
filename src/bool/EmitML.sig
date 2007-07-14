signature EmitML = 
sig
  include Abbrev

  val is_num_literal_hook      : (term -> bool) ref
  val is_int_literal_hook      : (term -> bool) ref
  val is_list_hook             : (term -> bool) ref
  val is_comma_hook            : (term -> bool) ref
  val is_pair_hook             : (term -> bool) ref
  val is_let_hook              : (term -> bool) ref
  val is_pabs_hook             : (term -> bool) ref
  val is_one_hook              : (term -> bool) ref
  val is_fail_hook             : (term -> bool) ref

  val dest_num_literal_hook    : (term -> Arbnum.num) ref
  val dest_int_literal_hook    : (term -> Arbint.int) ref
  val dest_list_hook           : (term -> term list) ref
  val dest_cons_hook           : (term -> term * term) ref
  val dest_pair_hook           : (term -> term * term) ref
  val dest_pabs_hook           : (term -> term * term) ref
  val dest_fail_hook           : (term -> term * string * term list) ref
  val strip_let_hook           : (term -> (term * term) list list * term) ref
  val list_mk_prod_hook        : (hol_type list -> hol_type) ref
  val list_mk_pair_hook        : (term list -> term) ref
  val list_mk_pabs_hook        : (term list * term -> term) ref

  val pseudo_constructors      : thm list ref
  val reshape_thm_hook         : (thm -> thm) ref
  val curried_const_equiv_tupled_var 
    : term * int -> thm (* side effects pseudo_constructors *)

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

  val sigSuffix : string ref 
  val structSuffix : string ref 
  val emitML : string -> string * elem list -> unit
end
