signature TypeBase =
sig

 type hol_type = Type.hol_type
 type term = Term.term
 type thm = Thm.thm
 type ppstream = Portable.ppstream

  type tyinfo
  type typeBase

  val gen_tyinfo : {ax:thm,
                    case_def: thm,
                    one_one : thm option,
                    distinct: thm option} -> tyinfo

  val mk_tyinfo : {ax:thm, case_def:thm,case_cong:thm,
                   induction:thm,nchotomy:thm, size: (term * thm) option,
                   one_one:thm option,distinct:thm option} -> tyinfo

  val ty_name_of      :tyinfo -> string
  val axiom_of        :tyinfo -> thm
  val constructors_of :tyinfo -> term list
  val case_const_of   :tyinfo -> term
  val case_cong_of    :tyinfo -> thm
  val case_def_of     :tyinfo -> thm
  val induction_of    :tyinfo -> thm
  val nchotomy_of     :tyinfo -> thm
  val distinct_of     :tyinfo -> thm option
  val one_one_of      :tyinfo -> thm option
  val simpls_of       :tyinfo -> thm list
  val size_of         :tyinfo -> (term * thm) option

  val pp_tyinfo : ppstream -> tyinfo -> unit

  val put_nchotomy  : thm -> tyinfo -> tyinfo
  val put_induction : thm -> tyinfo -> tyinfo
  val put_simpls    : thm list -> tyinfo -> tyinfo
  val put_size      : term * thm -> tyinfo -> tyinfo

  (* Functional database of datatype facts and associated operations. *)
  val empty     : typeBase
  val add       : typeBase -> tyinfo -> typeBase
  val get       : typeBase -> string -> tyinfo option
  val listItems : typeBase -> tyinfo list

  val tysize    : (hol_type -> term option) * (string -> term option) 
                    -> hol_type -> term
  val type_size : typeBase -> hol_type -> term

  (* Imperative database of datatype facts and associated operations. *)
  val theTypeBase : unit -> typeBase
  val write       : tyinfo -> unit
  val read        : string -> tyinfo option
  val elts        : unit -> tyinfo list

end;
