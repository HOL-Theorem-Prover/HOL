val _ = qload "testutils";
val _ = qload "PFTWriter";
open testutils

val tmpdir = OS.FileSys.tmpName () (* abuse tmpName for a unique prefix *)

fun tmpfile s = tmpdir ^ "-" ^ s
fun readFile f = let
  val s = TextIO.openIn f
  val t = TextIO.inputAll s
in TextIO.closeIn s; t end
fun readBinFile f = let
  val s = BinIO.openIn f
  val v = BinIO.inputAll s
in BinIO.closeIn s; Byte.bytesToString v end
fun cleanup f = OS.FileSys.remove f handle OS.SysErr _ => ()

(* --- Text format tests (JSON Lines) -------------------------------------- *)

val _ = tprint "Text: header + footer with basic commands"
val () = let
  val f = tmpfile "basic.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyvar out 0 "alpha"
  val () = PFTWriter.tyop out 1 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.HOL4.refl out 0 0
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=1, n_th=1, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":0,\"name\":\"alpha\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":1,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"REFL\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":2,\"n_tm\":1,\"n_th\":1,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: JSON string escaping"
val () = let
  val f = tmpfile "escape.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyvar out 0 ""               (* empty string *)
  val () = PFTWriter.tyvar out 1 "a b"            (* space is fine in JSON *)
  val () = PFTWriter.tyvar out 2 "a\\b"           (* backslash escaped *)
  val () = PFTWriter.tyvar out 3 "a\"b"           (* quote escaped *)
  val () = PFTWriter.tyvar out 4 "bool$/\\"       (* /\ with trailing \ *)
  val () = PFTWriter.closeOut out {n_ty=5, n_tm=0, n_th=0, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":0,\"name\":\"\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":1,\"name\":\"a b\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":2,\"name\":\"a\\\\b\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":3,\"name\":\"a\\\"b\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":4,\"name\":\"bool$/\\\\\"}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":5,\"n_tm\":0,\"n_th\":0,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got ^ "expected:\n" ^ expected);
  cleanup f
end

val _ = tprint "Text: theorem commands"
val () = let
  val f = tmpfile "thm.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "p" 0
  val () = PFTWriter.var out 1 "q" 0
  val () = PFTWriter.HOL4.assume out 0 0
  val () = PFTWriter.HOL4.assume out 1 1
  val () = PFTWriter.HOL4.conj out 2 0 1
  val () = PFTWriter.HOL4.conjunct1 out 3 2
  val () = PFTWriter.HOL4.conjunct2 out 4 2
  val () = PFTWriter.HOL4.disch out 5 0 1
  val () = PFTWriter.HOL4.mp out 6 5 0
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=2, n_th=7, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"p\",\"ty\":0}\n\
    \{\"cmd\":\"VAR\",\"id\":1,\"name\":\"q\",\"ty\":0}\n\
    \{\"cmd\":\"ASSUME\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"ASSUME\",\"id\":1,\"tm\":1}\n\
    \{\"cmd\":\"CONJ\",\"id\":2,\"th1\":0,\"th2\":1}\n\
    \{\"cmd\":\"CONJUNCT1\",\"id\":3,\"th\":2}\n\
    \{\"cmd\":\"CONJUNCT2\",\"id\":4,\"th\":2}\n\
    \{\"cmd\":\"DISCH\",\"id\":5,\"tm\":0,\"th\":1}\n\
    \{\"cmd\":\"MP\",\"id\":6,\"imp\":5,\"ant\":0}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":1,\"n_tm\":2,\"n_th\":7,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: variable-length commands"
val () = let
  val f = tmpfile "varlen.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.tyop out 1 "fun" [0,0]
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.var out 1 "y" 0
  val () = PFTWriter.HOL4.refl out 0 0
  val () = PFTWriter.HOL4.genl out 1 0 [0, 1]
  val () = PFTWriter.HOL4.inst out 2 0 [(0,1),(1,0)]
  val () = PFTWriter.HOL4.inst_type out 3 0 [(0,1)]
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=2, n_th=4, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"TYOP\",\"id\":1,\"name\":\"fun\",\"args\":[0,0]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"VAR\",\"id\":1,\"name\":\"y\",\"ty\":0}\n\
    \{\"cmd\":\"REFL\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"GENL\",\"id\":1,\"th\":0,\"tms\":[0,1]}\n\
    \{\"cmd\":\"INST\",\"id\":2,\"th\":0,\"subst\":[{\"redex\":0,\"residue\":1},{\"redex\":1,\"residue\":0}]}\n\
    \{\"cmd\":\"INST_TYPE\",\"id\":3,\"th\":0,\"subst\":[{\"redex\":0,\"residue\":1}]}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":2,\"n_tm\":2,\"n_th\":4,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: del, save, load"
val () = let
  val f = tmpfile "meta.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.HOL4.refl out 0 0
  val () = PFTWriter.save out "myThm" 0
  val () = PFTWriter.del out "th" 0
  val () = PFTWriter.del_range out "tm" 0 5
  val () = PFTWriter.load out 1 "myThm"
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=2, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"REFL\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"SAVE\",\"name\":\"myThm\",\"th\":0}\n\
    \{\"cmd\":\"DEL\",\"ns\":\"th\",\"id\":0}\n\
    \{\"cmd\":\"DEL\",\"ns\":\"tm\",\"id\":0,\"upto\":5}\n\
    \{\"cmd\":\"LOAD\",\"id\":1,\"name\":\"myThm\"}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":1,\"n_tm\":1,\"n_th\":2,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: axiom and def commands"
val () = let
  val f = tmpfile "defs.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.HOL4.refl out 0 0
  val () = PFTWriter.HOL4.axiom out 1 0 (SOME "my_axiom")
  val () = PFTWriter.HOL4.axiom out 2 0 NONE
  val () = PFTWriter.HOL4.def_spec out 3 0 ["foo", "bar"]
  val () = PFTWriter.HOL4.def_tyop out 4 0 "mytype"
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=5, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"hol4\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"REFL\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"AXIOM\",\"id\":1,\"tm\":0,\"name\":\"my_axiom\"}\n\
    \{\"cmd\":\"AXIOM\",\"id\":2,\"tm\":0}\n\
    \{\"cmd\":\"DEF_SPEC\",\"id\":3,\"th\":0,\"names\":[\"foo\",\"bar\"]}\n\
    \{\"cmd\":\"DEF_TYOP\",\"id\":4,\"th\":0,\"name\":\"mytype\"}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":1,\"n_tm\":1,\"n_th\":5,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

(* --- Candle text format tests --------------------------------------------- *)

val _ = tprint "Text (Candle): core rules"
val () = let
  val f = tmpfile "candle-core.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="candle"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.tyop out 1 "fun" [0,0]
  val () = PFTWriter.var out 0 "p" 0
  val () = PFTWriter.var out 1 "q" 0
  val () = PFTWriter.Candle.refl out 0 0
  val () = PFTWriter.Candle.assume out 1 0
  val () = PFTWriter.Candle.assume out 2 1
  val () = PFTWriter.Candle.sym out 3 0
  val () = PFTWriter.Candle.trans out 4 0 3
  val () = PFTWriter.Candle.eq_mp out 5 0 1
  val () = PFTWriter.Candle.deduct_antisym_rule out 6 1 2
  val () = PFTWriter.Candle.mk_comb out 7 0 0
  val () = PFTWriter.Candle.abs out 8 0 0
  val () = PFTWriter.Candle.prove_hyp out 9 1 2
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=2, n_th=10, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"candle\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"TYOP\",\"id\":1,\"name\":\"fun\",\"args\":[0,0]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"p\",\"ty\":0}\n\
    \{\"cmd\":\"VAR\",\"id\":1,\"name\":\"q\",\"ty\":0}\n\
    \{\"cmd\":\"REFL\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"ASSUME\",\"id\":1,\"tm\":0}\n\
    \{\"cmd\":\"ASSUME\",\"id\":2,\"tm\":1}\n\
    \{\"cmd\":\"SYM\",\"id\":3,\"th\":0}\n\
    \{\"cmd\":\"TRANS\",\"id\":4,\"th1\":0,\"th2\":3}\n\
    \{\"cmd\":\"EQ_MP\",\"id\":5,\"eq\":0,\"th\":1}\n\
    \{\"cmd\":\"DEDUCT_ANTISYM_RULE\",\"id\":6,\"th1\":1,\"th2\":2}\n\
    \{\"cmd\":\"MK_COMB\",\"id\":7,\"th1\":0,\"th2\":0}\n\
    \{\"cmd\":\"ABS\",\"id\":8,\"tm\":0,\"th\":0}\n\
    \{\"cmd\":\"PROVE_HYP\",\"id\":9,\"th1\":1,\"th2\":2}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":2,\"n_tm\":2,\"n_th\":10,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text (Candle): beta, inst, inst_type, alpha_thm"
val () = let
  val f = tmpfile "candle-misc.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="candle"}
  val () = PFTWriter.tyvar out 0 "A"
  val () = PFTWriter.tyop out 1 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.Candle.beta out 0 0
  val () = PFTWriter.Candle.inst out 1 0 [(0,0)]
  val () = PFTWriter.Candle.inst_type out 2 0 [(0,1)]
  val () = PFTWriter.Candle.alpha_thm out 3 0 [0,0] 0
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=1, n_th=4, n_ci=0}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"candle\"}\n\
    \{\"cmd\":\"TYVAR\",\"id\":0,\"name\":\"A\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":1,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"BETA\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"INST\",\"id\":1,\"th\":0,\"subst\":[{\"redex\":0,\"residue\":0}]}\n\
    \{\"cmd\":\"INST_TYPE\",\"id\":2,\"th\":0,\"subst\":[{\"redex\":0,\"residue\":1}]}\n\
    \{\"cmd\":\"ALPHA_THM\",\"id\":3,\"th\":0,\"tms\":[0,0],\"tm\":0}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":2,\"n_tm\":1,\"n_th\":4,\"n_ci\":0}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text (Candle): axioms, definitions, compute"
val () = let
  val f = tmpfile "candle-defs.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="candle"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.Candle.new_axiom out 0 0
  val () = PFTWriter.Candle.new_specification out 1 0
  val () = PFTWriter.Candle.new_type_definition out 2 0 "mid" "mid_ABS" "mid_REP"
  val () = PFTWriter.Candle.compute_init out 0 [0, 1, 2]
  val () = PFTWriter.Candle.compute out 4 0 0 [0]
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=5, n_ci=1}
  val got = readFile f
  val expected =
    "{\"cmd\":\"PFT\",\"version\":1,\"ruleset\":\"candle\"}\n\
    \{\"cmd\":\"TYOP\",\"id\":0,\"name\":\"bool\",\"args\":[]}\n\
    \{\"cmd\":\"VAR\",\"id\":0,\"name\":\"x\",\"ty\":0}\n\
    \{\"cmd\":\"new_axiom\",\"id\":0,\"tm\":0}\n\
    \{\"cmd\":\"new_specification\",\"id\":1,\"th\":0}\n\
    \{\"cmd\":\"new_type_definition\",\"id\":2,\"th\":0,\"tyname\":\"mid\",\"absname\":\"mid_ABS\",\"repname\":\"mid_REP\"}\n\
    \{\"cmd\":\"COMPUTE_INIT\",\"id\":0,\"ths\":[0,1,2]}\n\
    \{\"cmd\":\"COMPUTE\",\"id\":4,\"ci\":0,\"tm\":0,\"ths\":[0]}\n\
    \{\"cmd\":\"LIMITS\",\"n_ty\":1,\"n_tm\":1,\"n_th\":5,\"n_ci\":1}\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Binary (Candle): core rules"
val () = let
  val f = tmpfile "candle-core.bpft"
  val out = PFTWriter.openOut {file=f, binary=true, version=1, ruleset="candle"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "p" 0
  val () = PFTWriter.Candle.refl out 0 0
  val () = PFTWriter.Candle.assume out 1 0
  val () = PFTWriter.Candle.sym out 2 0
  val () = PFTWriter.Candle.trans out 3 0 2
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=4, n_ci=0}
  val got = readBinFile f
  val expected = String.implode (map Char.chr [
    0x50, 0x46, 0x54, 0x00,       (* magic *)
    0x01,                          (* version=1 *)
    0x06, 0x63, 0x61, 0x6E, 0x64, 0x6C, 0x65, (* "candle" *)
    (* TYOP 0 "bool" [] *)
    0x02, 0x00, 0x04, 0x62, 0x6F, 0x6F, 0x6C, 0x00,
    (* VAR 0 "p" 0 *)
    0x03, 0x00, 0x01, 0x70, 0x00,
    (* REFL 0 0 *)
    0x10, 0x00, 0x00,
    (* ASSUME 1 0 *)
    0x15, 0x01, 0x00,
    (* SYM 2 0 *)
    0x20, 0x02, 0x00,
    (* TRANS 3 0 2 *)
    0x11, 0x03, 0x00, 0x02,
    (* footer: 1 1 4 0, len=4 *)
    0x01, 0x01, 0x04, 0x00,
    0x04, 0x00
  ])
in
  if got = expected then OK()
  else die ("binary mismatch, got " ^ Int.toString (size got) ^ " bytes");
  cleanup f
end

(* --- Binary format tests (HOL4) ----------------------------------------- *)

val _ = tprint "Binary: header + footer with basic commands"
val () = let
  val f = tmpfile "basic.bpft"
  val out = PFTWriter.openOut {file=f, binary=true, version=1, ruleset="hol4"}
  val () = PFTWriter.tyvar out 0 "alpha"
  val () = PFTWriter.tyop out 1 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.HOL4.refl out 0 0
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=1, n_th=1, n_ci=0}
  val got = readBinFile f
  val expected = String.implode (map Char.chr [
    0x50, 0x46, 0x54, 0x00,    (* magic *)
    0x01,                       (* version=1 *)
    0x04, 0x68, 0x6F, 0x6C, 0x34, (* "hol4" *)
    (* commands *)
    0x01, 0x00, 0x05, 0x61, 0x6C, 0x70, 0x68, 0x61, (* TYVAR 0 "alpha" *)
    0x02, 0x01, 0x04, 0x62, 0x6F, 0x6F, 0x6C, 0x00, (* TYOP 1 "bool" 0args *)
    0x03, 0x00, 0x01, 0x78, 0x00, (* VAR 0 "x" 0 *)
    0x10, 0x00, 0x00,          (* REFL 0 0 *)
    (* footer: n_ty=2 n_tm=1 n_th=1 n_ci=0, then uint16le length=4 *)
    0x02, 0x01, 0x01, 0x00,
    0x04, 0x00
  ])
in
  if got = expected then OK()
  else die ("binary mismatch, got " ^ Int.toString (size got) ^ " bytes");
  cleanup f
end
