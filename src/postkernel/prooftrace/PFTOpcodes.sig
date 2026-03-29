signature PFTOpcodes = sig

  (* Describes the layout of arguments following the result id varint.
     Used by PFTMerge and PFTRename to process ruleset commands
     generically without ruleset-specific handlers. *)

  datatype arg_desc =
      Id of string                (* varint ID in given namespace *)
    | Val                         (* varint, pass through *)
    | IdList of string            (* count-prefixed ID list *)
    | IdPairs of string * string  (* count-prefixed ID pairs *)
    | StrIdPairs of string        (* count-prefixed (string, id) pairs *)
    | NewTypeName                 (* string that introduces a type *)
    | NewConstName                (* string that introduces a constant *)
    | NewConstNames               (* string list that introduces constants *)

  type opcode_desc = {
    results : string list,
    args : arg_desc list
  }

  val hol4_descs : (int * opcode_desc) list
  val candle_descs : (int * opcode_desc) list

  val lookup_desc : (int * opcode_desc) list -> int -> opcode_desc

  (* Get the appropriate descriptor list for a ruleset name *)
  val descs_for_ruleset : string -> (int * opcode_desc) list

end
