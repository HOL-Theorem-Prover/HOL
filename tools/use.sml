val _ = quietdec := true;
val _ = print "Rebinding \"use\" for quotation pre-processing.\n"

(*---------------------------------------------------------------------------*
 * A version of "use" that filters quotations. The native MoscowML version   *
 * of "use" is found in the "Meta" structure.                                *
 *---------------------------------------------------------------------------*)

local fun has_dq file =
       let val istrm = TextIO.openIn file
           fun loop() =
             case TextIO.input1 istrm
              of NONE => false
               | SOME #"`" => 
                   (case TextIO.input1 istrm 
                     of NONE => false | SOME #"`" => true | _ => loop())
               | SOME _ => loop()
           val status = loop()
       in 
          TextIO.closeIn istrm;
          status
       end
       fun unquote_to file1 file2 =
         Process.system (String.concat
             [Path.concat(HOLDIR, "bin/unquote"), " ",file1, " ",file2])
in
fun use s = 
  if has_dq s
  then let val filename = FileSys.tmpName()^".hol98"
       in 
         if unquote_to s filename = Process.success
         then 
            (Meta.use filename; FileSys.remove filename)
             handle e => (FileSys.remove filename handle _ => (); raise e)
         else (TextIO.output(TextIO.stdOut,
                 ("Failed to translate file: "^s^"\n")); raise Fail "use")
       end
  else Meta.use s
end;

val _ = quietdec := false;
