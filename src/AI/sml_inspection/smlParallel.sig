signature smlParallel =
sig

  (* internal *)
  val use_thread_flag : bool ref (* for debugging *)
  val parmap_exact : int -> ('a -> 'b) -> 'a list -> 'b list
  val parmap_batch : int -> ('a -> 'b) -> 'a list -> 'b list
  val parmap_gen : int -> (('a -> 'b) -> 'a list -> 'b list) * (unit -> unit)
  val parmap_queue : int -> ('a -> 'b) -> 'a list -> 'b list
  val parapp_queue : int -> ('a -> 'b) -> 'a list -> unit

  (* external *)
  val default_parallel_dir : string
  (* 'a: type of parameter, 'b: type of arguments, 'c: returned type *)
  type ('a,'b,'c) extspec =
    {
    self_dir : string,
    self: string,
    parallel_dir: string,
    reflect_globals : unit -> string,
    function : 'a -> 'b -> 'c,
    write_param : string -> 'a -> unit,
    read_param : string -> 'a,
    write_arg : string -> 'b -> unit,
    read_arg : string -> 'b,
    write_result : string ->'c -> unit,
    read_result : string -> 'c
    }
  val worker_start : int -> ('a,'b,'c) extspec -> unit
  val parmap_queue_extern :
    int -> ('a,'b,'c) extspec -> 'a -> 'b list -> 'c list

  (* example *)
  val idspec : (unit,int,int) extspec

end
