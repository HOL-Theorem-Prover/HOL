if (let fun f r = (r := !r + 1; (fn y => y)) val r = ref 3 in f r (!r) end) = 3
then
  use "tools/configure-mosml.sml"
else
  use "tools-poly/smart-configure.sml"
  handle e =>
        if String.isPrefix "Io" (exnMessage e) then
          print "\n\n** You must do\n     poly < tools/smart-configure.sml\n\
                \** from the root HOL directory\n\n"
        else ()
;
