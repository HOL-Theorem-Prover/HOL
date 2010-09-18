signature LVTermNet =
sig

  (* signature names modelled on Binarymap's *)
  type 'a lvtermnet
  type term = Term.term
  type key = Term.term list * Term.term

  val empty : 'a lvtermnet
  val insert : ('a lvtermnet * key * 'a) -> 'a lvtermnet
  val find : 'a lvtermnet * key -> 'a list
  val peek : 'a lvtermnet * key -> 'a list
  val match : 'a lvtermnet * term -> (key * 'a) list

  val delete : 'a lvtermnet * key -> 'a lvtermnet * 'a list
  val numItems : 'a lvtermnet -> int
  val listItems : 'a lvtermnet -> (key * 'a) list
  val app : (key * 'a list -> unit) -> 'a lvtermnet -> unit
  val fold : (key * 'a * 'b -> 'b) -> 'b -> 'a lvtermnet -> 'b

  val map : (key * 'a -> 'b) -> 'a lvtermnet -> 'b lvtermnet
  val transform : ('a -> 'b) -> 'a lvtermnet -> 'b lvtermnet

end
