structure FNameToUnquotedDeps :> FNameToUnquotedDeps =
struct

fun uqfname_holdep fname = let
  open OS.FileSys Systeml
  val op ^ = OS.Path.concat
  val unquote = xable_string(Systeml.HOLDIR ^ "bin" ^ "unquote")
  val actualfile =
      if access (unquote, [A_EXEC]) then let
          val newname = tmpName()
        in
          if OS.Process.isSuccess (Systeml.systeml [unquote, fname, newname])
          then newname
          else fname
        end
      else fname
  val is = TextIO.openIn actualfile
  fun cleanup() =
    (TextIO.closeIn is;
     if actualfile <> fname then OS.FileSys.remove actualfile handle _ => ()
     else ())
  (* though the analysis may be of an unquoted copy, we lie to stream_deps
     about what the name of the file is so that any error messages have a
     chance of being useful *)
in
  Holdep_tokens.stream_deps(fname,is) before cleanup()
end



end (* struct *)
