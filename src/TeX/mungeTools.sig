signature mungeTools =
sig

  datatype command = Theorem | Term | Type
  type optionset
  type posn = int * int (* linenum, charnum *)
  type override_map = (string,(string * int))Binarymap.dict

  val parseOpts : posn -> string -> optionset
  val usage : unit -> 'a
  val user_overrides : override_map ref
  val read_overrides : string -> override_map
  val optset_width : optionset -> int option

  val numErrors : int ref

  val replacement : PP.ppstream ->
                    {commpos : posn, argpos : posn, command : command,
                     options : optionset, argument : string} ->
                    unit
end
