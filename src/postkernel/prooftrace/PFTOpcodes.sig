signature PFTOpcodes = sig

  (* The wire / JSON shape of one argument of a ruleset command. *)
  datatype arg_shape =
      AId of string               (* varint ID in given namespace *)
    | AVal                        (* varint, no namespace meaning *)
    | AIdList of string           (* count-prefixed ID list *)
    | AIdPairs of string * string (* count-prefixed ID pairs, rendered as
                                     {"redex":..,"residue":..} in JSON *)
    | AStrIdPairs of string       (* count-prefixed (string, id) pairs,
                                     rendered as a named map in JSON *)
    | AName                       (* single string argument *)
    | ANameList                   (* count-prefixed list of strings *)

  (* The merge-relevant semantic role of an argument. *)
  datatype arg_role =
      RNormal
    | RNewType                    (* string that introduces a type op *)
    | RNewConst                   (* string that introduces a constant *)
    | RNewConsts                  (* strings that introduce constants *)

  type arg_spec = {
    label : string,               (* JSON key for this argument *)
    shape : arg_shape,
    role  : arg_role
  }

  type opcode_desc = {
    tag     : string,             (* JSON "cmd" tag, e.g. "REFL" *)
    results : string list,        (* namespaces of the result IDs
                                     (all but COMPUTE_INIT have one;
                                     Candle new_type_definition has two) *)
    args    : arg_spec list
  }

  (* Decoded form of one argument, parallel to arg_shape. *)
  datatype arg_val =
      VId         of int
    | VVal        of int
    | VIdList     of int list
    | VIdPairs    of (int * int) list
    | VStrIdPairs of (string * int) list
    | VName       of string
    | VNameList   of string list

  val hol4_descs : (int * opcode_desc) list
  val candle_descs : (int * opcode_desc) list

  val lookup_desc : (int * opcode_desc) list -> int -> opcode_desc

  val descs_for_ruleset : string -> (int * opcode_desc) list

end
