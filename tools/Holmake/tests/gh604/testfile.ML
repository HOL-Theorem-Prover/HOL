val _ = case List.find (String.isSuffix "base") (!loadPath) of
            NONE => OS.Process.exit OS.Process.failure
          | _ => OS.Process.exit OS.Process.success
