signature hhFactIndex =
sig
  type 'a index

  val create : ('a -> string) -> 'a list -> 'a index

  (* Match names using String.compare and return selected entries in their
     original order, including repeated entries for the same name. *)
  val select : 'a index -> (string, unit) Redblackmap.dict -> 'a list
  (* NONE recommends a linear scan for a dense selection. *)
  val select_sparse :
    'a index -> (string, unit) Redblackmap.dict -> 'a list option
end
