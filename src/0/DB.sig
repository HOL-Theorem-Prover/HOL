signature DB =
sig

 type term = Term.term
 type thm = Thm.thm

 datatype class = Def | Axm | Thm
 type data = (string * string) * (thm * class)

  val lemmas : unit -> (string * string, data) Binarymap.dict

  val thy    : string -> data list
  val find   : string -> data list
  val match  : string list -> Term.term -> data list (* first order matches *)

  val theorem : string -> string -> thm
  val theorems : string -> (string * thm) list
  val gen_theorem : string -> string -> thm * class
  val gen_theorems : string -> (string * thm * class) list

  val rawmatch  : (term -> term -> bool)
                  -> string list -> Term.term -> data list

  (* For system use *)
  val bindl : string -> (string * thm * class) list -> unit

end;
