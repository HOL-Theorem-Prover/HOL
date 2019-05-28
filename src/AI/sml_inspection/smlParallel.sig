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
  val wid_dir : int -> string
  val widout_file : int -> string
  val argl_file : unit -> string
  val readl_rm : string -> string list
  val writel_atomic : string -> string list -> unit
  val result_file : (int * int) -> string
  val worker_start : int -> (int * int -> 'a -> 'b) * 'a list -> unit
  val parmap_queue_extern :
    int ->
    (int -> string list) ->
    ((unit -> unit) * ('a list -> unit))
    -> ((int * int) -> 'b) ->
    'a list -> 'b list

  val standard_code_of : string * string * string -> int -> string list

  (* example *)
  val id_parallel : int -> int list -> int list

end
