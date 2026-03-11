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

(* --- Text format tests --------------------------------------------------- *)

val _ = tprint "Text: header + footer with basic commands"
val () = let
  val f = tmpfile "basic.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyvar out 0 "alpha"
  val () = PFTWriter.tyop out 1 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.refl out 0 0
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=1, n_th=1, n_ci=0}
  val got = readFile f
  val expected =
    "PFT 1 hol4\n\
    \TYVAR 0 alpha\n\
    \TYOP 1 bool\n\
    \VAR 0 x 0\n\
    \REFL 0 0\n\
    \2 1 1 0\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: name escaping"
val () = let
  val f = tmpfile "escape.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  (* SML string    -> actual chars -> PFT output *)
  val () = PFTWriter.tyvar out 0 ""           (* empty -> \_ *)
  val () = PFTWriter.tyvar out 1 "a b"        (* "a b" -> a\ b *)
  val () = PFTWriter.tyvar out 2 "a\\b"       (* "a\b" -> a\b (no escape needed) *)
  val () = PFTWriter.tyvar out 3 "a\\ "       (* "a\ " -> a\\\ (both escaped) *)
  val () = PFTWriter.tyvar out 4 "a\\"        (* "a\" -> a\\ (trailing \ escaped) *)
  val () = PFTWriter.tyvar out 5 "\\_"        (* "\_" -> \\_ (reserved token) *)
  val () = PFTWriter.closeOut out {n_ty=6, n_tm=0, n_th=0, n_ci=0}
  val got = readFile f
  (* Build expected with String.concat to keep SML escaping clear.
     Each line shows: PFT output chars | SML literal *)
  val expected = String.concat [
    "PFT 1 hol4\n",
    "TYVAR 0 \\_\n",                  (* PFT: \_       *)
    "TYVAR 1 a\\ b\n",               (* PFT: a\ b     *)
    "TYVAR 2 a\\b\n",                (* PFT: a\b      *)
    "TYVAR 3 a\\\\\\ \n",            (* PFT: a\\\sp   *)
    "TYVAR 4 a\\\\\n",               (* PFT: a\\      *)
    "TYVAR 5 \\\\_\n",               (* PFT: \\_      *)
    "6 0 0 0\n"
  ]
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
  val () = PFTWriter.assume out 0 0
  val () = PFTWriter.assume out 1 1
  val () = PFTWriter.conj out 2 0 1
  val () = PFTWriter.conjunct1 out 3 2
  val () = PFTWriter.conjunct2 out 4 2
  val () = PFTWriter.disch out 5 0 1
  val () = PFTWriter.mp out 6 5 0
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=2, n_th=7, n_ci=0}
  val got = readFile f
  val expected =
    "PFT 1 hol4\n\
    \TYOP 0 bool\n\
    \VAR 0 p 0\n\
    \VAR 1 q 0\n\
    \ASSUME 0 0\n\
    \ASSUME 1 1\n\
    \CONJ 2 0 1\n\
    \CONJUNCT1 3 2\n\
    \CONJUNCT2 4 2\n\
    \DISCH 5 0 1\n\
    \MP 6 5 0\n\
    \1 2 7 0\n"
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
  val () = PFTWriter.refl out 0 0
  val () = PFTWriter.genl out 1 0 [0, 1]
  val () = PFTWriter.inst out 2 0 [(0,1),(1,0)]
  val () = PFTWriter.inst_type out 3 0 [(0,1)]
  val () = PFTWriter.closeOut out {n_ty=2, n_tm=2, n_th=4, n_ci=0}
  val got = readFile f
  val expected =
    "PFT 1 hol4\n\
    \TYOP 0 bool\n\
    \TYOP 1 fun 0 0\n\
    \VAR 0 x 0\n\
    \VAR 1 y 0\n\
    \REFL 0 0\n\
    \GENL 1 0 0 1\n\
    \INST 2 0 0 1 1 0\n\
    \INST_TYPE 3 0 0 1\n\
    \2 2 4 0\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

val _ = tprint "Text: del, save, load, comment"
val () = let
  val f = tmpfile "meta.pft"
  val out = PFTWriter.openOut {file=f, binary=false, version=1, ruleset="hol4"}
  val () = PFTWriter.tyop out 0 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.refl out 0 0
  val () = PFTWriter.comment out "test comment"
  val () = PFTWriter.save out "myThm" 0
  val () = PFTWriter.del out "th" 0
  val () = PFTWriter.del_range out "tm" 0 5
  val () = PFTWriter.load out 1 "myThm"
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=2, n_ci=0}
  val got = readFile f
  val expected =
    "PFT 1 hol4\n\
    \TYOP 0 bool\n\
    \VAR 0 x 0\n\
    \REFL 0 0\n\
    \# test comment\n\
    \SAVE myThm 0\n\
    \DEL th 0\n\
    \DEL tm 0 5\n\
    \LOAD 1 myThm\n\
    \1 1 2 0\n"
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
  val () = PFTWriter.refl out 0 0
  val () = PFTWriter.axiom out 1 0 (SOME "my_axiom")
  val () = PFTWriter.axiom out 2 0 NONE
  val () = PFTWriter.def_spec out 3 0 ["foo", "bar"]
  val () = PFTWriter.def_tyop out 4 0 "mytype"
  val () = PFTWriter.closeOut out {n_ty=1, n_tm=1, n_th=5, n_ci=0}
  val got = readFile f
  val expected =
    "PFT 1 hol4\n\
    \TYOP 0 bool\n\
    \VAR 0 x 0\n\
    \REFL 0 0\n\
    \AXIOM 1 0 my_axiom\n\
    \AXIOM 2 0\n\
    \DEF_SPEC 3 0 foo bar\n\
    \DEF_TYOP 4 0 mytype\n\
    \1 1 5 0\n"
in
  if got = expected then OK()
  else die ("got:\n" ^ got);
  cleanup f
end

(* --- Binary format tests ------------------------------------------------- *)

val _ = tprint "Binary: header + footer with basic commands"
val () = let
  val f = tmpfile "basic.bpft"
  val out = PFTWriter.openOut {file=f, binary=true, version=1, ruleset="hol4"}
  val () = PFTWriter.tyvar out 0 "alpha"
  val () = PFTWriter.tyop out 1 "bool" []
  val () = PFTWriter.var out 0 "x" 0
  val () = PFTWriter.refl out 0 0
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

val _ = tprint "Binary: comments are ignored"
val () = let
  val f1 = tmpfile "nocomment.bpft"
  val out1 = PFTWriter.openOut {file=f1, binary=true, version=1, ruleset="hol4"}
  val () = PFTWriter.refl out1 0 0
  val () = PFTWriter.closeOut out1 {n_ty=0, n_tm=0, n_th=1, n_ci=0}
  val f2 = tmpfile "withcomment.bpft"
  val out2 = PFTWriter.openOut {file=f2, binary=true, version=1, ruleset="hol4"}
  val () = PFTWriter.comment out2 "this should be ignored"
  val () = PFTWriter.refl out2 0 0
  val () = PFTWriter.closeOut out2 {n_ty=0, n_tm=0, n_th=1, n_ci=0}
  val b1 = readBinFile f1
  val b2 = readBinFile f2
in
  if b1 = b2 then OK()
  else die "binary output differs with comment";
  cleanup f1; cleanup f2
end
