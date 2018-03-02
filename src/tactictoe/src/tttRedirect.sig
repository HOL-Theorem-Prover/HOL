signature tttRedirect =
sig

  val pop_output_file : unit -> bool
  val push_output_file : {append: bool, name: string} -> unit
  val hide_in_file : string -> ('a -> 'b) -> 'a -> 'b

end
