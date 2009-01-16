signature ConstMapML =
sig

  type constmap

  type hol_type = Type.hol_type
  type term     = Term.term

  val theConstMap : unit -> constmap
  val prim_insert : term * (bool * string * string * hol_type) -> unit
  val insert      : term -> unit
  val insert_cons : term -> unit
  val apply       : term -> bool * string * string * hol_type
  val exact_peek  : term -> (bool * string * string * hol_type) option

  (* [apply] peforms a lookup and returns the most specific match.  Thus,
     if the map has data for both
       APPEND : 'a list -> 'a list -> 'a list
     and
       APPEND : char list -> char list -> char list
     Then, you will get the data for the latter rather than the former when
     you ask for APPEND : string -> string -> string.  But you will get the
     former if you ask for data on APPEND : num list -> num list -> num list.

     [exact_peek] does an exact lookup on the term.  Thus, if you have the
     situation as above, and exact_peek on
       APPEND : num list -> num list -> num list
     you will get back NONE.
   *)
end
