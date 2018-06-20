if String.isPrefix "Fail: " (General.exnMessage (General.Fail ""))
   then use "tools/configure-mosml.sml"
else use "tools-poly/smart-configure.sml"
     handle e =>
       if String.isPrefix "Io" (General.exnMessage e) then
          TextIO.print
             "\n\n** You must do\n     poly < tools/smart-configure.sml\n\
             \** from the root HOL directory\n\n"
       else ()
