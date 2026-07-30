(* Regression test for quotefix.run.  All work is inside main so the file
   can be loaded without side effects; polyc wires main as the entry point
   of the resulting executable, and the Mosml driver calls main () at the
   end of the linked program. *)

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
  OS.Process.exit
    (if !failures = 0 then OS.Process.success else OS.Process.failure)
end
