signature smlParallel =
sig

  (* internal *)
  val use_thread_flag : bool ref (* for debugging *)
  val parmap_exact : int -> ('a -> 'b) -> 'a list -> 'b list
  val parmap_batch : int -> ('a -> 'b) -> 'a list -> 'b list
  val parmap_queue : int -> ('a -> 'b) -> 'a list -> 'b list
  val parapp_queue : int -> ('a -> 'b) -> 'a list -> unit
  val parmap_gen : int -> (('b -> 'c) -> 'b list -> 'c list) * (unit -> unit)

  (* external *)
  val parallel_dir : string ref
  (* 'a: type of parameter, 'b: type of arguments, 'c: returned type *)
  type ('a,'b,'c) extspec = 
    {
    self: string,
    reflect_globals : unit -> string,
    function : 'a -> 'b -> 'c,
    write_param : string -> 'a -> unit,
    read_param : string -> 'a,
    write_argl : string -> 'b list -> unit,
    read_argl : string -> 'b list,
    write_result : string ->'c -> unit,
    read_result : string -> 'c
    }
  val worker_start : int -> ('a,'b,'c) extspec -> unit
  val parmap_queue_extern : int -> ('a,'b,'c) extspec -> 'a -> 'b list -> 'c list

  (* example *)
  val idspec : (unit,int,int) extspec

end
