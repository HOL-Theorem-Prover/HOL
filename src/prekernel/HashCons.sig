signature HashCons = sig

  val hashstring : string -> word

  eqtype 'a hconsed
  val node : 'a hconsed -> 'a
  val tag  : 'a hconsed -> int

  val hc_compare : 'a Lib.cmp -> 'a hconsed Lib.cmp
  val hc_tag_compare : 'a hconsed Lib.cmp

  type 'a weakref = 'a option ref

  type 'a htable = 'a hconsed weakref HOLset.set PIntMap.t

  val empty_table : 'a htable

  val mk_next_tag : unit -> (unit -> int)

  val mk_hashconsed : ('a * 'a -> bool) -> (unit -> int) -> 'a htable ref -> ('b -> word) ->
                        ('b -> 'a) -> 'b -> 'a hconsed

end
