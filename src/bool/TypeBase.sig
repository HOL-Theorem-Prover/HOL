signature TypeBase =
sig

   type term      = Term.term
   type thm       = Thm.thm
   type tyinfo    = TypeBasePure.tyinfo
   type typeBase  = TypeBasePure.typeBase
   type shared_thm = TypeBasePure.shared_thm

   (* Imperative database of datatype facts and associated operations. *)

   val theTypeBase        : unit -> typeBase
   val write              : tyinfo list -> tyinfo list
   val read               : string -> tyinfo option
   val elts               : unit -> tyinfo list
   val register_update_fn : (tyinfo list -> tyinfo list) -> unit

   val axiom_of           : string -> thm
   val induction_of       : string -> thm
   val constructors_of    : string -> term list
   val case_const_of      : string -> term
   val case_cong_of       : string -> thm
   val case_def_of        : string -> thm
   val nchotomy_of        : string -> thm
   val distinct_of        : string -> thm
   val one_one_of         : string -> thm
   val simpls_of          : string -> simpfrag.simpfrag
   val size_of            : string -> term * thm
   val encode_of          : string -> term * thm

   val axiom_of0          : string -> shared_thm
   val induction_of0      : string -> shared_thm
   val size_of0           : string -> (term * shared_thm) option
   val encode_of0         : string -> (term * shared_thm) option

   val mk_case            : term * (term * term) list -> term
   val dest_case          : term -> term * term * (term * term) list
   val strip_case         : term -> term * (term * term) list
   val is_case            : term -> bool
   val is_constructor     : term -> bool

end
