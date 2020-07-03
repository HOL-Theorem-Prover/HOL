signature smlRedirect =
sig

  val pop_output_file : unit -> bool
  val push_output_file : {append: bool, name: string} -> unit
  val hide_in_file : string -> ('a -> 'b) -> 'a -> 'b
  val hide_out : ('a -> 'b) -> 'a -> 'b
  val hide_flag : bool ref
  val hidef : ('a -> 'b) -> 'a -> 'b

end
