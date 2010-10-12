(*---------------------------------------------------------------------------*
 * A version of "use" that filters quotations. The native MoscowML version   *
 * of "use" is found in the "Meta" structure.                                *
 *---------------------------------------------------------------------------*)

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
            | SOME _ => loop()
      in
        loop() before TextIO.closeIn istrm
      end handle Io _ => false
  infix ++
  fun p1 ++ p2 = Path.concat (p1, p2)
  fun unquote_to file1 file2 =
      Systeml.systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2]
in
fun use s =
  if has_dq s then
    let
      val filename = FileSys.tmpName()^".hol"
    in
      if Process.isSuccess (unquote_to s filename) then
        (Meta.use filename; FileSys.remove filename)
        handle e => (FileSys.remove filename handle _ => (); raise e)
      else (TextIO.output(TextIO.stdOut,
                          ("Failed to translate file: "^s^"\n"));
            raise Fail "use")
    end
  else Meta.use s
end;

(*---------------------------------------------------------------------------*
 *  Make the pretty-printer print terms and types with `` .... `` syntax.    *
 *---------------------------------------------------------------------------*)

val _ =
  (term_pp_prefix := "``";   term_pp_suffix := "``";
  type_pp_prefix  := "``";   type_pp_suffix := "``");
