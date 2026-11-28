signature hhFactIndex =
sig
  type 'a index

  val create : ('a -> string) -> 'a list -> 'a index

  (* Match names using String.compare and return selected entries in their
     original order, including repeated entries for the same name. *)
  val select : 'a index -> (string, unit) Redblackmap.dict -> 'a list
  (* As select, but NONE when the selection is dense (at least an eighth of
     the facts), for which a linear scan is faster. *)
  val select_sparse :
    'a index -> (string, unit) Redblackmap.dict -> 'a list option
end
