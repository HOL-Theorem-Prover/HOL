signature TypeBase =
sig

   type hol_type  = Type.hol_type
   type term      = Term.term
   type thm       = Thm.thm
   type tyinfo    = TypeBasePure.tyinfo
   type typeBase  = TypeBasePure.typeBase
   type shared_thm = TypeBasePure.shared_thm

   (* Imperative database of datatype facts and associated operations. *)

   val theTypeBase        : unit -> typeBase
   val write              : tyinfo list -> tyinfo list
   val read               : {Thy :string, Tyop: string} -> tyinfo option
   val elts               : unit -> tyinfo list
   val register_update_fn : (tyinfo list -> tyinfo list) -> unit

   val axiom_of           : string * string -> thm
   val induction_of       : string * string -> thm
   val constructors_of    : string * string -> term list
   val case_const_of      : string * string -> term
   val case_cong_of       : string * string -> thm
   val case_def_of        : string * string -> thm
   val nchotomy_of        : string * string -> thm
   val distinct_of        : string * string -> thm
   val fields_of          : string * string -> (string * hol_type) list
   val one_one_of         : string * string -> thm
   val simpls_of          : string * string -> simpfrag.simpfrag
   val size_of            : string * string -> term * thm
   val encode_of          : string * string -> term * thm

   val axiom_of0          : string * string -> shared_thm
   val induction_of0      : string * string -> shared_thm
   val size_of0           : string * string -> (term * shared_thm) option
   val encode_of0         : string * string -> (term * shared_thm) option

   val is_constructor     : term -> bool

   val mk_case            : term * (term * term) list -> term
   val dest_case          : term -> term * term * (term * term) list
   val is_case            : term -> bool
   val strip_case         : term -> term * (term * term) list

   val mk_record          : hol_type -> (string * term) list -> term
   val dest_record        : term -> (string * term) list
   val is_record          : term -> bool

end
