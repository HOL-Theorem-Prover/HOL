signature DB =
sig

 type term = Term.term
 type thm = Thm.thm
 type theory = Hol_pp.theory

 datatype class = Thm | Axm | Def

 type data = (string * string) * (thm * class)

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
  val matchp      : (thm -> bool) -> string list -> data list
  val matcher     : (term -> term -> 'a) -> string list -> term -> data list
  val match       : string list -> term -> data list
  val apropos     : term -> data list
  val listDB      : unit -> data list

  val data_list_to_string : data list -> string
  val print_apropos       : term -> unit
  val print_find          : string -> unit
  val print_match         : string list -> term -> unit


  val dest_theory  : string -> theory
  val print_theory : string -> unit

  val print_theory_to_file      : string -> string -> unit
  val print_theory_to_outstream : string -> TextIO.outstream -> unit
  val export_theory_as_docfiles : string -> unit

  val pp_theory_as_html         : ppstream -> string -> unit
  val print_theory_as_html      : string -> string -> unit
  val html_theory               : string -> unit

  val bindl : string -> (string * thm * class) list -> unit



end
