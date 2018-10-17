signature Parmap =
sig

  val parmap : ('a -> 'b) -> 'a list -> 'b list

  val chunking_parmap : {ratio:int,mincsz:int} -> ('a -> 'b) ->
                        'a list -> 'b list
    (* number of chunks will be roughly ratio * num_threads *)

end
