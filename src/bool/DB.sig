signature DB =
sig

 type term = Term.term
 type thm = Thm.thm

 datatype class = Thm | Axm | Def

 type data = (string * string) * (thm * class)

  val thy         : string -> data list
  val fetch       : string -> string -> thm
  val thms        : string -> (string * thm) list
  val axioms      : string -> (string * thm) list
  val theorems    : string -> (string * thm) list
  val definitions : string -> (string * thm) list
  val find        : string -> data list
  val matchp      : (thm -> bool) -> string list -> data list
  val matcher     : (term -> term -> 'a) -> string list -> term -> data list
  val match       : string list -> term -> data list 
  val apropos     : term -> data list 
  val all_thys    : unit -> data list

  val export_theory_as_docfiles : string -> unit

  val bindl : string -> (string * thm * class) list -> unit

end
