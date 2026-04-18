structure PFTOpcodes :> PFTOpcodes = struct

datatype arg_shape =
    AId of string
  | AVal
  | AIdList of string
  | AIdPairs of string * string
  | AStrIdPairs of string
  | AName
  | ANameList

datatype arg_role =
    RNormal
  | RNewType
  | RNewConst
  | RNewConsts

type arg_spec = {
  label : string,
  shape : arg_shape,
  role  : arg_role
}

type opcode_desc = {
  tag     : string,
  results : string list,
  args    : arg_spec list
}

datatype arg_val =
    VId         of int
  | VVal        of int
  | VIdList     of int list
  | VIdPairs    of (int * int) list
  | VStrIdPairs of (string * int) list
  | VName       of string
  | VNameList   of string list

(* Convenience constructors for building descriptor tables. *)
local
  fun mk lbl sh = {label = lbl, shape = sh, role = RNormal}
in
  fun id lbl ns        = mk lbl (AId ns)
  fun ids lbl ns       = mk lbl (AIdList ns)
  fun pairs lbl (a, b) = mk lbl (AIdPairs (a, b))
  fun strids lbl ns    = mk lbl (AStrIdPairs ns)
  fun ty_name lbl      = {label = lbl, shape = AName, role = RNewType}
  fun c_name lbl       = {label = lbl, shape = AName, role = RNewConst}
  fun c_names lbl      = {label = lbl, shape = ANameList, role = RNewConsts}
end

val hol4_descs : (int * opcode_desc) list = [
  (0x10, {tag="REFL",          results=["th"],
          args=[id "tm" "tm"]}),
  (0x11, {tag="ALPHA",         results=["th"],
          args=[id "tm1" "tm", id "tm2" "tm"]}),
  (0x12, {tag="ASSUME",        results=["th"],
          args=[id "tm" "tm"]}),
  (0x13, {tag="BETA_CONV",     results=["th"],
          args=[id "tm" "tm"]}),
  (0x14, {tag="EQ_MP",         results=["th"],
          args=[id "eq" "th", id "th" "th"]}),
  (0x15, {tag="MP",            results=["th"],
          args=[id "imp" "th", id "ant" "th"]}),
  (0x16, {tag="SYM",           results=["th"],
          args=[id "th" "th"]}),
  (0x17, {tag="TRANS",         results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x18, {tag="CONJ",          results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x19, {tag="CONJUNCT1",     results=["th"],
          args=[id "th" "th"]}),
  (0x1A, {tag="CONJUNCT2",     results=["th"],
          args=[id "th" "th"]}),
  (0x1B, {tag="DISCH",         results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x1C, {tag="DISJ1",         results=["th"],
          args=[id "th" "th", id "tm" "tm"]}),
  (0x1D, {tag="DISJ2",         results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x1E, {tag="DISJ_CASES",    results=["th"],
          args=[id "disj" "th", id "left" "th", id "right" "th"]}),
  (0x1F, {tag="NOT_ELIM",      results=["th"],
          args=[id "th" "th"]}),
  (0x20, {tag="NOT_INTRO",     results=["th"],
          args=[id "th" "th"]}),
  (0x21, {tag="CCONTR",        results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x22, {tag="EXISTS",        results=["th"],
          args=[id "tm1" "tm", id "tm2" "tm", id "th" "th"]}),
  (0x23, {tag="CHOOSE",        results=["th"],
          args=[id "var" "tm", id "existence" "th", id "body" "th"]}),
  (0x24, {tag="GEN",           results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x25, {tag="SPEC",          results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x26, {tag="Specialize",    results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x27, {tag="GENL",          results=["th"],
          args=[id "th" "th", ids "tms" "tm"]}),
  (0x28, {tag="ABSL",          results=["th"],
          args=[id "th" "th", ids "tms" "tm"]}),
  (0x29, {tag="GEN_ABS",       results=["th"],
          args=[id "th" "th", id "tm" "tm", ids "tms" "tm"]}),
  (0x30, {tag="ABS_THM",       results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x31, {tag="AP_TERM",       results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x32, {tag="AP_THM",        results=["th"],
          args=[id "th" "th", id "tm" "tm"]}),
  (0x33, {tag="MK_COMB",       results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x34, {tag="Beta",          results=["th"],
          args=[id "th" "th"]}),
  (0x35, {tag="Mk_abs",        results=["th"],
          args=[id "eq" "th", id "body" "th"]}),
  (0x36, {tag="Mk_comb",       results=["th"],
          args=[id "eq" "th", id "rator" "th", id "rand" "th"]}),
  (0x37, {tag="EQ_IMP_RULE1",  results=["th"],
          args=[id "th" "th"]}),
  (0x38, {tag="EQ_IMP_RULE2",  results=["th"],
          args=[id "th" "th"]}),
  (0x39, {tag="INST",          results=["th"],
          args=[id "th" "th", pairs "subst" ("tm","tm")]}),
  (0x3A, {tag="INST_TYPE",     results=["th"],
          args=[id "th" "th", pairs "subst" ("ty","ty")]}),
  (0x3B, {tag="SUBST",         results=["th"],
          args=[id "template" "tm", id "th" "th",
                pairs "subst" ("tm","th")]}),
  (0x3C, {tag="deductAntisym", results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x40, {tag="DEF_TYOP",      results=["th"],
          args=[id "th" "th", ty_name "name"]}),
  (0x41, {tag="DEF_SPEC",      results=["th"],
          args=[id "th" "th", c_names "names"]}),
  (0x42, {tag="DEF_SPEC_GEN",  results=["th"],
          args=[id "th" "th", c_names "names"]}),
  (0x43, {tag="COMPUTE_INIT",  results=["ci"],
          args=[id "num_ty" "ty", id "cval_ty" "ty",
                strids "char_eqns" "th",
                strids "cval_terms" "tm"]}),
  (0x44, {tag="COMPUTE",       results=["th"],
          args=[id "ci" "ci", id "tm" "tm", ids "ths" "th"]})
]

val candle_descs : (int * opcode_desc) list = [
  (0x10, {tag="REFL",                results=["th"],
          args=[id "tm" "tm"]}),
  (0x11, {tag="TRANS",               results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x12, {tag="MK_COMB",             results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x13, {tag="ABS_THM",             results=["th"],
          args=[id "tm" "tm", id "th" "th"]}),
  (0x14, {tag="BETA",                results=["th"],
          args=[id "tm" "tm"]}),
  (0x15, {tag="ASSUME",              results=["th"],
          args=[id "tm" "tm"]}),
  (0x16, {tag="EQ_MP",               results=["th"],
          args=[id "eq" "th", id "th" "th"]}),
  (0x17, {tag="DEDUCT_ANTISYM_RULE", results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x18, {tag="INST",                results=["th"],
          args=[id "th" "th", pairs "subst" ("tm","tm")]}),
  (0x19, {tag="INST_TYPE",           results=["th"],
          args=[id "th" "th", pairs "subst" ("ty","ty")]}),
  (0x20, {tag="SYM",                 results=["th"],
          args=[id "th" "th"]}),
  (0x21, {tag="PROVE_HYP",           results=["th"],
          args=[id "th1" "th", id "th2" "th"]}),
  (0x30, {tag="new_specification",   results=["th"],
          args=[id "th" "th", c_names "names"]}),
  (0x31, {tag="new_type_definition", results=["th","th"],
          args=[id "th" "th",
                ty_name "tyname",
                c_name "absname",
                c_name "repname"]}),
  (0x40, {tag="COMPUTE_INIT",        results=["ci"],
          args=[ids "ths" "th"]}),
  (0x41, {tag="COMPUTE",             results=["th"],
          args=[id "ci" "ci", id "tm" "tm", ids "ths" "th"]})
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
