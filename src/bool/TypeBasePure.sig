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
                       | COPY of string * thm

   val gen_tyinfo      : {ax  : thm,
                          ind : thm,
                          case_defs : thm list} -> tyinfo list

   val mk_tyinfo       : {ax        : shared_thm,
                          induction : shared_thm,
                          case_def  : thm,
                          case_cong : thm,
                          nchotomy  : thm,
                          size      : (term * shared_thm) option,
                          boolify   : (term * shared_thm) option,
                          one_one   : thm option,
                          distinct  : thm option} -> tyinfo

   val ty_name_of      : tyinfo -> string
   val axiom_of        : tyinfo -> thm
   val induction_of    : tyinfo -> thm
   val constructors_of : tyinfo -> term list
   val case_const_of   : tyinfo -> term
   val case_cong_of    : tyinfo -> thm
   val case_def_of     : tyinfo -> thm
   val nchotomy_of     : tyinfo -> thm
   val distinct_of     : tyinfo -> thm option
   val one_one_of      : tyinfo -> thm option
   val simpls_of       : tyinfo -> simpfrag
   val size_of         : tyinfo -> (term * thm) option
   val boolify_of         : tyinfo -> (term * thm) option

   val axiom_of0       : tyinfo -> shared_thm
   val induction_of0   : tyinfo -> shared_thm
   val size_of0        : tyinfo -> (term * shared_thm) option
   val boolify_of0        : tyinfo -> (term * shared_thm) option

   val pp_tyinfo       : ppstream -> tyinfo -> unit

   val put_nchotomy    : thm -> tyinfo -> tyinfo
   val put_simpls      : simpfrag -> tyinfo -> tyinfo
   val put_induction   : shared_thm -> tyinfo -> tyinfo
   val put_size        : term * shared_thm -> tyinfo -> tyinfo
   val put_boolify     : term * shared_thm -> tyinfo -> tyinfo

   (* Functional databases of datatype facts and associated operations *)

   val empty           : typeBase
   val add             : typeBase -> tyinfo -> typeBase
   val get             : typeBase -> string -> tyinfo option
   val listItems       : typeBase -> tyinfo list

  (* Support for polytypism *)

   val typeValue
      : (hol_type -> term option) *
        (string -> term option)   *
        (hol_type -> term)
        -> hol_type -> term

  (* Size of a type *)

   val type_size    : typeBase -> hol_type -> term
   val type_boolify : typeBase -> hol_type -> term

end
