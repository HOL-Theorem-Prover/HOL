signature DB =
sig

 type term = Term.term
 type thm = Thm.thm
 datatype theory = datatype DB_dtype.theory
 datatype class = datatype DB_dtype.class
 datatype selector = datatype DB_dtype.selector
 type data = DB_dtype.data
 datatype location = datatype DB_dtype.location
 type hol_type = Type.hol_type

  val thy         : string -> data list
  val fetch       : string -> string -> thm
  val thms        : string -> (string * thm) list

  val theorem     : string -> thm
  val definition  : string -> thm
  val axiom       : string -> thm

  val axioms      : string -> (string * thm) list
  val theorems    : string -> (string * thm) list
  val definitions : string -> (string * thm) list
  val find        : string -> data list
  val find_in     : string -> data list -> data list
  val matchp      : (thm -> bool) -> string list -> data list
  val matcher     : (term -> term -> 'a) -> string list -> term -> data list
  val match       : string list -> term -> data list
  val matches     : term -> thm -> bool
  val apropos     : term -> data list
  val apropos_in  : term -> data list -> data list
  val selectDB    : selector list -> data list
  val listDB      : unit -> data list
  val revlookup   : thm -> location list

  val store_local : string -> thm -> unit
  val local_thm   : string -> thm option

  val dest_theory  : string -> theory
  val bindl : string -> (string * thm * class) list -> unit

  (* Derived search functions *)
  val find_consts_thy : string list -> hol_type -> term list
  val find_consts : hol_type -> term list

end
