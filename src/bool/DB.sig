signature DB =
sig

 type term = Term.term
 type thm = Thm.thm
 type 'a quotation = 'a Portable.frag list

 datatype class = Thm | Axm | Def
 
 type data = (string * string) * (thm * class)

  val thy           : string -> data list
  val theorems      : string -> (string * thm) list
  val find          : string -> data list
  val matchp        : (thm -> bool) -> string list -> data list
  val matcher       : (term -> term -> 'a) -> string list -> term -> data list
  val match         : string list -> term -> data list 
  val apropos       : term -> data list 
  val theorem       : string -> string -> thm
  val theorem_class : string -> string -> thm * class
  val all_thms      : unit -> data list

  val bindl : string -> (string * thm * class) list -> unit

end
