structure PFTOpcodes :> PFTOpcodes = struct

datatype arg_desc =
    Id of string
  | Val
  | IdList of string
  | IdPairs of string * string
  | StrIdPairs of string
  | NewTypeName
  | NewConstName
  | NewConstNames

type opcode_desc = {
  results : string list,
  args : arg_desc list
}

val hol4_descs : (int * opcode_desc) list = [
  (0x10, {results=["th"], args=[Id "tm"]}),
  (0x11, {results=["th"], args=[Id "tm", Id "tm"]}),
  (0x12, {results=["th"], args=[Id "tm"]}),
  (0x13, {results=["th"], args=[Id "tm"]}),
  (0x14, {results=["th"], args=[Id "th", Id "th"]}),
  (0x15, {results=["th"], args=[Id "th", Id "th"]}),
  (0x16, {results=["th"], args=[Id "th"]}),
  (0x17, {results=["th"], args=[Id "th", Id "th"]}),
  (0x18, {results=["th"], args=[Id "th", Id "th"]}),
  (0x19, {results=["th"], args=[Id "th"]}),
  (0x1A, {results=["th"], args=[Id "th"]}),
  (0x1B, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x1C, {results=["th"], args=[Id "th", Id "tm"]}),
  (0x1D, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x1E, {results=["th"], args=[Id "th", Id "th", Id "th"]}),
  (0x1F, {results=["th"], args=[Id "th"]}),
  (0x20, {results=["th"], args=[Id "th"]}),
  (0x21, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x22, {results=["th"], args=[Id "tm", Id "tm", Id "th"]}),
  (0x23, {results=["th"], args=[Id "tm", Id "th", Id "th"]}),
  (0x24, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x25, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x26, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x27, {results=["th"], args=[Id "th", IdList "tm"]}),
  (0x28, {results=["th"], args=[Id "th", IdList "tm"]}),
  (0x29, {results=["th"], args=[Id "th", Id "tm", IdList "tm"]}),
  (0x30, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x31, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x32, {results=["th"], args=[Id "th", Id "tm"]}),
  (0x33, {results=["th"], args=[Id "th", Id "th"]}),
  (0x34, {results=["th"], args=[Id "th"]}),
  (0x35, {results=["th"], args=[Id "th", Id "th"]}),
  (0x36, {results=["th"], args=[Id "th", Id "th", Id "th"]}),
  (0x37, {results=["th"], args=[Id "th"]}),
  (0x38, {results=["th"], args=[Id "th"]}),
  (0x39, {results=["th"], args=[Id "th", IdPairs("tm","tm")]}),
  (0x3A, {results=["th"], args=[Id "th", IdPairs("ty","ty")]}),
  (0x3B, {results=["th"], args=[Id "tm", Id "th", IdPairs("tm","th")]}),
  (0x3C, {results=["th"], args=[Id "th", Id "th"]}),
  (0x40, {results=["th"], args=[Id "th", NewTypeName]}),
  (0x41, {results=["th"], args=[Id "th", NewConstNames]}),
  (0x42, {results=["th"], args=[Id "th", NewConstNames]}),
  (0x43, {results=["ci"], args=[Id "ty", Id "ty",
                                StrIdPairs "th", StrIdPairs "tm"]}),
  (0x44, {results=["th"], args=[Id "ci", Id "tm", IdList "th"]})
]

val candle_descs : (int * opcode_desc) list = [
  (0x10, {results=["th"], args=[Id "tm"]}),
  (0x11, {results=["th"], args=[Id "th", Id "th"]}),
  (0x12, {results=["th"], args=[Id "th", Id "th"]}),
  (0x13, {results=["th"], args=[Id "tm", Id "th"]}),
  (0x14, {results=["th"], args=[Id "tm"]}),
  (0x15, {results=["th"], args=[Id "tm"]}),
  (0x16, {results=["th"], args=[Id "th", Id "th"]}),
  (0x17, {results=["th"], args=[Id "th", Id "th"]}),
  (0x18, {results=["th"], args=[Id "th", IdPairs("tm","tm")]}),
  (0x19, {results=["th"], args=[Id "th", IdPairs("ty","ty")]}),
  (0x20, {results=["th"], args=[Id "th"]}),
  (0x21, {results=["th"], args=[Id "th", Id "th"]}),
  (0x22, {results=["th"], args=[Id "th", IdList "tm", Id "tm"]}),
  (0x30, {results=["th"], args=[Id "th", NewConstNames]}),
  (0x31, {results=["th","th"], args=[Id "th", NewTypeName, NewConstName, NewConstName]}),
  (0x40, {results=["ci"], args=[IdList "th"]}),
  (0x41, {results=["th"], args=[Id "ci", Id "tm", IdList "th"]})
]

fun lookup_desc descs opc =
  case List.find (fn (o', _) => o' = opc) descs of
    SOME (_, d) => d
  | NONE => raise Fail ("PFTOpcodes: unknown opcode 0x" ^
                         Int.fmt StringCvt.HEX opc)

fun descs_for_ruleset "candle" = candle_descs
  | descs_for_ruleset "hol4" = hol4_descs
  | descs_for_ruleset r = raise Fail ("PFTOpcodes: unknown ruleset " ^ r)

end
