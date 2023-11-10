signature TypeBase =
sig

   type hol_type  = Type.hol_type
   type term      = Term.term
   type thm       = Thm.thm
   type tyinfo    = TypeBasePure.tyinfo
   type typeBase  = TypeBasePure.typeBase
   type shared_thm = TypeBasePure.shared_thm
   type rcd_fieldinfo = TypeBasePure.rcd_fieldinfo

   (* Imperative database of datatype facts and associated operations. *)

   val theTypeBase        : unit -> typeBase
   val thy_typebase       : {thyname : string} -> typeBase option
   val thy_updates        : {thyname : string} -> tyinfo list
   val merge_typebases    : string list -> typeBase option
   val write              : tyinfo list -> unit
   val export             : tyinfo list -> unit (* includes write action *)
   val fetch              : hol_type -> tyinfo option
   val read               : {Thy :string, Tyop: string} -> tyinfo option
   val elts               : unit -> tyinfo list
   val register_update_fn : (tyinfo -> tyinfo) -> unit

   val axiom_of           : hol_type -> thm
   val induction_of       : hol_type -> thm
   val constructors_of    : hol_type -> term list
   val destructors_of     : hol_type -> thm list
   val recognizers_of     : hol_type -> thm list
   val case_const_of      : hol_type -> term
   val case_cong_of       : hol_type -> thm
   val case_def_of        : hol_type -> thm
   val case_eq_of         : hol_type -> thm
   val nchotomy_of        : hol_type -> thm
   val distinct_of        : hol_type -> thm
   val fields_of          : hol_type -> (string * rcd_fieldinfo) list
   val accessors_of       : hol_type -> thm list
   val updates_of         : hol_type -> thm list
   val one_one_of         : hol_type -> thm
   val simpls_of          : hol_type -> simpfrag.simpfrag
   val size_of            : hol_type -> term * thm
   val encode_of          : hol_type -> term * thm

   val axiom_of0          : hol_type -> shared_thm
   val induction_of0      : hol_type -> shared_thm
   val size_of0           : hol_type -> (term * shared_thm) option
   val encode_of0         : hol_type -> (term * shared_thm) option

   val is_constructor     : term -> bool

   val mk_case            : term * (term * term) list -> term
   val dest_case          : term -> term * term * (term * term) list
   val is_case            : term -> bool
   val strip_case         : term -> term * (term * term) list
   val mk_pattern_fn      : (term * term) list -> term

   val mk_record          : hol_type * (string * term) list -> term
   val dest_record        : term -> hol_type * (string * term) list
   val is_record          : term -> bool

   val dest_record_type   : hol_type -> (string * rcd_fieldinfo) list
   val is_record_type     : hol_type -> bool

   val CaseEq             : string -> thm
   val CaseEqs            : string list -> thm
   val AllCaseEqs         : unit -> thm

   val CasePred           : string -> thm
   val CasePreds          : string list -> thm
   val AllCasePreds       : unit -> thm

   (* f (case x of ...) <=> (case x of ..) *)
   val case_rand_of       : hol_type -> thm
   (* f (case x of ...) <=> disjunction of possibilities *)
   val case_pred_disj_of  : hol_type -> thm
   (* f (case x of ...) <=> conjunction of implications *)
   val case_pred_imp_of   : hol_type -> thm

   val update_induction   : thm -> unit
   val update_axiom       : thm -> unit
   val general_update     : hol_type -> (tyinfo -> tyinfo) -> unit
end
