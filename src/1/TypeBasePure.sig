signature TypeBasePure =
sig
   type hol_type = Type.hol_type
   type term     = Term.term
   type thm      = Thm.thm

   type tyinfo
   type typeBase
   type simpfrag = simpfrag.simpfrag
   type rcd_fieldinfo = {ty: hol_type, accessor: term, fupd : term}

   val mk_recordtype_constructor : string -> string
   val mk_recordtype_fieldsel : {tyname:string,fieldname:string} -> string
   val mk_recordtype_fieldfupd : {tyname:string,fieldname:string} -> string

   datatype shared_thm = ORIG of thm
                       | COPY of (string * string) * thm
   type mk_datatype_record =
        {ax        : shared_thm,
         induction : shared_thm,
         case_def  : thm,
         case_cong : thm,
         case_eq   : thm,
         case_elim : thm,
         nchotomy  : thm,
         size      : (term * shared_thm) option,
         encode    : (term * shared_thm) option,
         lift      : term option,
         one_one   : thm option,
         distinct  : thm option,
         fields    : (string * rcd_fieldinfo) list,
         accessors : thm list,
         updates   : thm list,
         destructors : thm list,
         recognizers : thm list}

   val mk_datatype_info_no_simpls : mk_datatype_record -> tyinfo
   val gen_std_rewrs    : tyinfo -> thm list
   val add_std_simpls   : tyinfo -> tyinfo
   val mk_datatype_info : mk_datatype_record -> tyinfo

   val gen_datatype_info : {ax:thm,ind:thm,case_defs:thm list} -> tyinfo list

   val mk_nondatatype_info
           : hol_type *
             {nchotomy  : thm option,
              induction : thm option,
              size      : (term * thm) option,
              encode    : (term * thm) option} -> tyinfo

   val pp_tyinfo       : tyinfo Parse.pprinter

   val ty_of           : tyinfo -> hol_type
   val ty_name_of      : tyinfo -> string * string

   val axiom_of        : tyinfo -> thm
   val induction_of    : tyinfo -> thm
   val constructors_of : tyinfo -> term list
   val destructors_of  : tyinfo -> thm list
   val recognizers_of  : tyinfo -> thm list
   val case_const_of   : tyinfo -> term
   val case_cong_of    : tyinfo -> thm
   val case_def_of     : tyinfo -> thm
   val case_eq_of      : tyinfo -> thm
   val case_elim_of    : tyinfo -> thm
   val nchotomy_of     : tyinfo -> thm
   val distinct_of     : tyinfo -> thm option
   val one_one_of      : tyinfo -> thm option
   val fields_of       : tyinfo -> (string * rcd_fieldinfo) list
   val accessors_of    : tyinfo -> thm list
   val updates_of      : tyinfo -> thm list
   val simpls_of       : tyinfo -> simpfrag
   val size_of         : tyinfo -> (term * thm) option
   val encode_of       : tyinfo -> (term * thm) option
   val lift_of         : tyinfo -> term option
   val extra_of        : tyinfo -> ThyDataSexp.t list

   val axiom_of0       : tyinfo -> shared_thm
   val induction_of0   : tyinfo -> shared_thm
   val size_of0        : tyinfo -> (term * shared_thm) option
   val encode_of0      : tyinfo -> (term * shared_thm) option

   val put_nchotomy    : thm -> tyinfo -> tyinfo
   val put_simpls      : simpfrag -> tyinfo -> tyinfo
   val add_rewrs       : thm list -> tyinfo -> tyinfo
   val add_ssfrag_convs: simpfrag.convdata list -> tyinfo -> tyinfo
   val put_induction   : shared_thm -> tyinfo -> tyinfo
   val put_axiom       : shared_thm -> tyinfo -> tyinfo
   val put_size        : term * shared_thm -> tyinfo -> tyinfo
   val put_encode      : term * shared_thm -> tyinfo -> tyinfo
   val put_lift        : term -> tyinfo -> tyinfo
   val put_fields      : (string * rcd_fieldinfo) list -> tyinfo -> tyinfo
   val put_accessors   : thm list -> tyinfo -> tyinfo
   val put_updates     : thm list -> tyinfo -> tyinfo
   val put_destructors : thm list -> tyinfo -> tyinfo
   val put_recognizers : thm list -> tyinfo -> tyinfo
   val put_extra       : ThyDataSexp.t list -> tyinfo -> tyinfo
   val add_extra       : ThyDataSexp.t list -> tyinfo -> tyinfo

   (* Functional databases of datatype facts and associated operations *)

   val empty           : typeBase
   val insert          : typeBase -> tyinfo -> typeBase
   val fold            : (hol_type * tyinfo * 'b -> 'b) -> 'b -> typeBase ->
                         'b
(*   val add             : typeBase -> tyinfo -> typeBase  *)

   val fetch           : typeBase -> hol_type -> tyinfo option
   val prim_get        : typeBase -> string * string -> tyinfo option
   val get             : typeBase -> string -> tyinfo list
                       (* get returns list of tyinfos for types with that tyop *)

   val listItems       : typeBase -> tyinfo list
   val toPmatchThry    : typeBase -> {Thy:string,Tyop:string} ->
                         {constructors : term list, case_const : term} option

  (* Support for polytypism *)

   val typeValue       : (hol_type -> term option) *
                         (hol_type -> term option) *
                         (hol_type -> term) -> hol_type -> term
   val tyValue         : (hol_type -> term option) *
                         (hol_type -> term option) *
                         (hol_type -> term) -> hol_type -> term

   val type_size_pre   : (hol_type -> term option) -> typeBase -> hol_type -> term
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

   val dest_record_type : typeBase -> hol_type -> (string * rcd_fieldinfo) list
   val is_record_type   : typeBase -> hol_type -> bool

   val toSEXP          : tyinfo -> ThyDataSexp.t
   val fromSEXP        : ThyDataSexp.t -> tyinfo option

end
