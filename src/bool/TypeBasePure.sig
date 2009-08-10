signature TypeBasePure =
sig
   type hol_type = Type.hol_type
   type term     = Term.term
   type thm      = Thm.thm
   type ppstream = Portable.ppstream

   type tyinfo
   type typeBase
   type simpfrag = simpfrag.simpfrag

   datatype shared_thm = ORIG of thm
                       | COPY of (string * string) * thm

   val mk_datatype_info
           : {ax        : shared_thm,
              induction : shared_thm,
              case_def  : thm,
              case_cong : thm,
              nchotomy  : thm,
              size      : (term * shared_thm) option,
              encode    : (term * shared_thm) option,
              lift      : term option,
              one_one   : thm option,
              distinct  : thm option,
              fields    : (string * hol_type) list,
              accessors : thm list,
              updates   : thm list} -> tyinfo

   val gen_datatype_info : {ax:thm,ind:thm,case_defs:thm list} -> tyinfo list

   val mk_nondatatype_info
           : hol_type *
             {nchotomy : thm option,
              size     : (term * thm) option,
              encode   : (term * thm) option} -> tyinfo

   val pp_tyinfo       : ppstream -> tyinfo -> unit

   val ty_of           : tyinfo -> hol_type
   val ty_name_of      : tyinfo -> string * string

   val axiom_of        : tyinfo -> thm
   val induction_of    : tyinfo -> thm
   val constructors_of : tyinfo -> term list
   val case_const_of   : tyinfo -> term
   val case_cong_of    : tyinfo -> thm
   val case_def_of     : tyinfo -> thm
   val nchotomy_of     : tyinfo -> thm
   val distinct_of     : tyinfo -> thm option
   val one_one_of      : tyinfo -> thm option
   val fields_of       : tyinfo -> (string * hol_type) list
   val accessors_of    : tyinfo -> thm list
   val updates_of      : tyinfo -> thm list
   val simpls_of       : tyinfo -> simpfrag
   val size_of         : tyinfo -> (term * thm) option
   val encode_of       : tyinfo -> (term * thm) option
   val lift_of         : tyinfo -> term option

   val axiom_of0       : tyinfo -> shared_thm
   val induction_of0   : tyinfo -> shared_thm
   val size_of0        : tyinfo -> (term * shared_thm) option
   val encode_of0      : tyinfo -> (term * shared_thm) option

   val put_nchotomy    : thm -> tyinfo -> tyinfo
   val put_simpls      : simpfrag -> tyinfo -> tyinfo
   val put_induction   : shared_thm -> tyinfo -> tyinfo
   val put_size        : term * shared_thm -> tyinfo -> tyinfo
   val put_encode      : term * shared_thm -> tyinfo -> tyinfo
   val put_lift        : term -> tyinfo -> tyinfo
   val put_fields      : (string * hol_type) list -> tyinfo -> tyinfo
   val put_accessors   : thm list -> tyinfo -> tyinfo
   val put_updates     : thm list -> tyinfo -> tyinfo

   (* Functional databases of datatype facts and associated operations *)

   val empty           : typeBase
   val insert          : typeBase -> tyinfo -> typeBase
   val add             : typeBase -> tyinfo -> typeBase

   val fetch           : typeBase -> hol_type -> tyinfo option
   val prim_get        : typeBase -> string * string -> tyinfo option
   val get             : typeBase -> string -> tyinfo list
       (* get returns list of tyinfos for types with that tyop *)
   val listItems       : typeBase -> tyinfo list

  (* Support for polytypism *)

   val typeValue       : (hol_type -> term option) *
                         (hol_type -> term option) *
                         (hol_type -> term) -> hol_type -> term
   val tyValue         : (hol_type -> term option) *
                         (hol_type -> term option) *
                         (hol_type -> term) -> hol_type -> term

   val type_size       : typeBase -> hol_type -> term
   val type_encode     : typeBase -> hol_type -> term
   val type_lift       : typeBase -> hol_type -> term

   val cinst           : hol_type -> term -> term

   val is_constructor  : typeBase -> term -> bool

   val mk_case         : typeBase -> term * (term * term) list -> term
   val dest_case       : typeBase -> term -> term * term * (term * term) list
   val is_case         : typeBase -> term -> bool
   val strip_case      : typeBase -> term -> term * (term * term) list

   val mk_record       : typeBase -> hol_type * (string * term) list -> term
   val dest_record     : typeBase -> term -> hol_type * (string * term) list
   val is_record       : typeBase -> term -> bool
end
