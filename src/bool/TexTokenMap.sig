signature TexTokenMap =
sig

  val TeX_notation : {hol: string, TeX : string * int} -> unit
  val temp_TeX_notation : {hol: string, TeX : string * int} -> unit

  val the_map : unit -> {src : string, info : string * int} Symtab.table

end
