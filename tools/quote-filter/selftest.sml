(* Regression tests for quotefix.run and for the HOL-to-SML translator.
   All work is inside main so the file can be loaded without side
   effects; polyc wires main as the entry point of the resulting
   executable, and the Mosml driver calls main () at the end of the
   linked program. *)

fun stringReader src = let
  val pos = ref 0
  val sz = size src
in
  fn _ => if !pos >= sz then "" else
          let val out = String.substring (src, !pos, sz - !pos)
          in pos := sz; out end
end

(* U+2018, U+2019, U+201C, U+201D as UTF-8 byte sequences *)
val lsquo = "\226\128\152"
val rsquo = "\226\128\153"
val ldquo = "\226\128\156"
val rdquo = "\226\128\157"

fun main () = let
  val buf : string list ref = ref []
  fun writer s = buf := s :: !buf
  fun reset () = buf := []
  fun result () = String.concat (List.rev (!buf))

  val failures = ref 0
  fun fail name msgs =
      (print ("FAIL  " ^ name ^ "\n");
       List.app (fn m => print ("  " ^ m ^ "\n")) msgs;
       failures := !failures + 1)
  fun check name input expected = let
    val () = reset ()
    val gotExn =
        (quotefix.run (stringReader input) writer; NONE)
        handle e => SOME e
    val got = result ()
  in
    case gotExn of
      SOME e =>
        (print ("FAIL  " ^ name ^ ": exception " ^ exnMessage e ^ "\n");
         failures := !failures + 1)
    | NONE =>
        if got = expected then print ("OK    " ^ name ^ "\n")
        else (print ("FAIL  " ^ name ^ "\n");
              print ("  input    = " ^ input ^ "\n");
              print ("  expected = " ^ expected ^ "\n");
              print ("  got      = " ^ got ^ "\n");
              failures := !failures + 1)
  end

  fun isSubstring pat s = let
    val (n, m) = (size pat, size s)
    fun go i = i + n <= m andalso
               (String.substring (s, i, n) = pat orelse go (i + 1))
    in go 0 end

  (* Diagnostics from the parser arrive on the `print` callback; the
     result is the expanded SML. *)
  fun translate input = let
    val errs = ref ([]: string list)
    val sml = HOLSource.fromString
                {quietOpen = true, print = fn s => errs := s :: !errs} input
    in (sml, String.concat (List.rev (!errs))) end

  fun translates name input expected = let
    val (sml, errs) = translate input
    in
      if errs <> "" then fail name ["unexpected diagnostics: " ^ errs]
      else if not (isSubstring expected sml) then
        fail name ["expected substring = " ^ expected, "got = " ^ sml]
      else print ("OK    " ^ name ^ "\n")
    end

  fun rejects name input = let
    val (_, errs) = translate input
    in
      if errs = "" then fail name ["expected a diagnostic, got none"]
      else print ("OK    " ^ name ^ "\n")
    end

  (* `translate` goes through `HOLSource.fromString`, which supplies no
     file name, so it cannot reach the checks that compare a theory name
     against the file it is declared in.  `inputToReader` takes one
     without needing a file on disk. *)
  fun translateIn fname input = let
    val errs = ref ([]: string list)
    val {read, ...} =
      HOLSource.inputToReader
        {quietOpen = true, print = fn s => errs := s :: !errs}
        fname (stringReader input)
    fun drain acc = case read () of
                        NONE => String.concat (List.rev acc)
                      | SOME c => drain (str c :: acc)
    val sml = drain []
    in (sml, String.concat (List.rev (!errs))) end

  (* The theory header alone is not a whole file; `Ancestors`-free and
     `[bare]` so the expansion stays small and needs nothing loaded. *)
  fun theoryIn fname name = translateIn fname ("Theory" ^ name ^ "[bare]\n")

  fun headerOK name fname thyname = let
    val (_, errs) = theoryIn fname (" " ^ thyname)
    in
      if errs = "" then print ("OK    " ^ name ^ "\n")
      else fail name ["unexpected diagnostics: " ^ errs]
    end

  fun headerRejects name fname thyname expected = let
    val (_, errs) = theoryIn fname (" " ^ thyname)
    in
      if errs = "" then fail name ["expected a diagnostic, got none"]
      else if not (isSubstring expected errs) then
        fail name ["expected substring = " ^ expected, "got = " ^ errs]
      else print ("OK    " ^ name ^ "\n")
    end
in
  check "backtick pair"      ("`foo`\n")       (lsquo ^ "foo" ^ rsquo ^ "\n");
  check "double backtick"    ("``foo``\n")     (ldquo ^ "foo" ^ rdquo ^ "\n");
  check "in val binding"     ("val x = `f`\n")
        ("val x = " ^ lsquo ^ "f" ^ rsquo ^ "\n");
  check "no-quote passthrough" ("no quotes here\n") ("no quotes here\n");
  check "two quotes in a row"
        ("`f` `g`\n")
        (lsquo ^ "f" ^ rsquo ^ " " ^ lsquo ^ "g" ^ rsquo ^ "\n");
  (* Issue #2022: an old-style `Datatype `...`` whose `Datatype` sits at
     column zero (the `val _ =` on the preceding line) must be treated as
     the ordinary bossLib.Datatype function applied to a quotation, not as
     the modern `Datatype: ... End` keyword -- the latter has no backtick
     quotation and left the parser in a state that raised Unreachable. *)
  check "col-0 old-style Datatype"
        ("Datatype\n`repro = RP (bool)`\n")
        ("Datatype\n" ^ lsquo ^ "repro = RP (bool)" ^ rsquo ^ "\n");
  check "col-0 old-style Datatype, one line"
        ("Datatype `x = X`\n")
        ("Datatype " ^ lsquo ^ "x = X" ^ rsquo ^ "\n");
  (* A quoted body stops at a column-0 SML keyword so that an unclosed
     Definition or Theorem doesn't swallow the rest of the file.  A Quote
     body is verbatim material for a user-supplied parser, so that
     heuristic must not fire there, and nothing but its own End closes
     it: every other column-0 keyword is quoted material. *)
  translates "verbatim Quote body at column 0"
        ("Quote I:\nfun foo n = Test.bar n\nProof\nQED\nTermination\nEnd\n")
        "fun foo n = Test.bar n\\nProof\\nQED\\nTermination\\n";
  (* ... but it must still fire for a body of HOL terms. *)
  rejects "unclosed Definition body"
        ("Definition foo:\n  f x = x\nfun bar y = y\n");

  (* A script's file name is the authority on its theory name: Holmake
     demands `fooTheory.*` from `fooScript.sml` whatever the header
     says, so a header that disagrees is reported where it is written
     rather than later, as a product that failed to appear. *)
  headerOK "theory name agreeing with the file" "fooScript.sml" "foo";
  headerOK "theory name agreeing, with a directory"
           "/a/b/fooScript.sml" "foo";
  (* The LSP passes a URI here rather than a path. *)
  headerOK "theory name agreeing, given a URI"
           "file:///a/b/fooScript.sml" "foo";
  headerOK "theory name agreeing, given a Windows path"
           "C:\\a\\fooScript.sml" "foo";
  headerRejects "theory name disagreeing with the file"
                "fooScript.sml" "bar" "does not match file";
  headerRejects "theory name disagreeing, named in the message"
                "fooScript.sml" "bar" "fooScript.sml";
  (* Only a script file names a theory after itself.  Everything else --
     an ordinary .sml file, and the callers that supply no file name at
     all -- is left alone. *)
  headerOK "theory name in a non-script file" "scratch.sml" "bar";
  headerOK "theory name with no file name at all" "" "bar";
  (* To build an article, Holmake hard-links `fooScript.sml` to
     `foo.artScript.sml` and compiles that, so the synthesised name
     reaches the parser attached to the original header.  Its stem could
     not be a theory name, so the file names no theory to disagree
     with. *)
  headerOK "theory name under an article script alias"
           "sat.artScript.sml" "sat";

  (* A half-typed header: the parser already says `expected identifier`,
     and `new_theory ""` would raise on top of that, saying the same
     thing less clearly.  Neither it nor `set_grammar_ancestry` is
     emitted, so there is nothing left to raise. *)
  let val (sml, errs) = translateIn "fooScript.sml" "Theory\n"
  in
    if not (isSubstring "expected identifier" errs) then
      fail "nameless header still reports a parse error"
           ["got = " ^ errs]
    else if isSubstring "new_theory" sml then
      fail "nameless header emits no new_theory" ["got = " ^ sml]
    else if isSubstring "does not match file" errs then
      fail "nameless header does not also report a mismatch"
           ["got = " ^ errs]
    else print ("OK    nameless header: one diagnostic, no new_theory\n")
  end;

  OS.Process.exit
    (if !failures = 0 then OS.Process.success else OS.Process.failure)
end
