signature TypeNet =
sig

  (* signature names modelled on Binarymap's *)
  type 'a typenet
  type hol_type = Type.hol_type

  val empty : 'a typenet
  val insert : ('a typenet * hol_type * 'a) -> 'a typenet
  val find : 'a typenet * hol_type -> 'a
  val peek : 'a typenet * hol_type -> 'a option
  val match : 'a typenet * hol_type -> (hol_type * 'a) list

  val delete : 'a typenet * hol_type -> 'a typenet * 'a
  val numItems : 'a typenet -> int
  val listItems : 'a typenet -> (hol_type * 'a) list
  val app : (hol_type * 'a -> unit) -> 'a typenet -> unit
  val fold : (hol_type * 'a * 'b -> 'b) -> 'b -> 'a typenet -> 'b

  val map : (hol_type * 'a -> 'b) -> 'a typenet -> 'b typenet
  val transform : ('a -> 'b) -> 'a typenet -> 'b typenet

end
