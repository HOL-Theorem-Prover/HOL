(* unquote-init.sml - Moscow ML Quotation Filter Support
   =====================================================

   This file defines the QUse structure which provides a version of "use"
   that automatically filters HOL quotations (terms and types enclosed
   in backticks). Files containing quotations are preprocessed through
   bin/unquote before being passed to Moscow ML.

   This is loaded during Moscow ML interactive session initialization
   (from tools/std.prelude via the generated hol shell script).

   For Poly/ML, quotation handling is done via a modified copy of Poly/ML's
   REPL code in tools-poly/holrepl.ML (called from tools-poly/hol.ML).
*)

(*---------------------------------------------------------------------------*
 * A version of "use" that filters quotations. The native MoscowML version   *
 * of "use" is found in the "Meta" structure.                                *
 *---------------------------------------------------------------------------*)

structure QUse =
struct
  local
  (* used to stand for "has double quote", but the same analysis is necessary
     even for files that contain single quotes because of the special
     treatment that the filter gives to things like `s1 ^ s2`
  *)
  fun has_dq file =
      let
        val istrm = TextIO.openIn file
        fun loop() =
            case TextIO.input1 istrm of
              NONE => false
            | SOME #"`" => true
            | SOME c => Char.ord c > 127 orelse loop()
      in
        loop() before TextIO.closeIn istrm
      end handle Io _ => false
  infix ++
  fun p1 ++ p2 = Path.concat (p1, p2)
  fun unquote_to file1 file2 =
      Systeml.systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2]
  fun with_flag (r,v) f x =
      let val old = !r
      in
        let
          val _ = r := v
          val res = f x
        in
          r := old;
          res
        end handle e => (r := old; raise e)
      end
in
fun use s =
  let
    val full = OS.Path.mkCanonical
                 (OS.Path.mkAbsolute{path = s, relativeTo = FileSys.getDir()})
    val fileDir = OS.Path.dir full
    val oldDir = FileSys.getDir()
    val _ = if fileDir <> "" then FileSys.chDir fileDir else ()
  in
    ((if has_dq full then
        let
          val filename = FileSys.tmpName()^".hol"
        in
          if Process.isSuccess (unquote_to full filename) then
            (Meta.use filename; FileSys.remove filename)
            handle e => (FileSys.remove filename handle _ => (); raise e)
          else (TextIO.output(TextIO.stdOut,
                              ("Failed to translate file: "^s^"\n"));
                raise Fail "use")
        end
      else Meta.use full);
     FileSys.chDir oldDir)
    handle e => (FileSys.chDir oldDir handle _ => (); raise e)
  end

fun prim_use {quietOpen} s =
    with_flag (Meta.quietdec, quietOpen) use s
end; (* local *)

end; (* struct *)
val use = QUse.use;
