signature Context =
sig
   val read_context : unit -> Thm.thm list
   val write_context: Thm.thm list -> unit
end
