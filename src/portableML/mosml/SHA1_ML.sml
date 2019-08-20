structure SHA1_ML :> SHA1_ML =
struct

  fun sha1_file {filename} =
      if OS.FileSys.access("/usr/bin/shasum", [OS.FileSys.A_EXEC]) then
          case Mosml.run "/usr/bin/shasum" [Systeml.protect filename] "" of
              Mosml.Success s => hd (String.tokens Char.isSpace s)
            | Mosml.Failure _ => raise Fail ("Calling shasum {filename=\"" ^ filename ^ "} failed")
      else
        raise Fail "shasum not installed"

end (* struct *)
