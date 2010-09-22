let
  fun fact n acc = if n <= 1 then acc else fact (n - 1) (n * acc)
in
  fact 21 1;
  use "polysysinfo.sml"
     handle e =>
        if String.isPrefix "Io" (exnMessage e) then
          print "\n\n** You must do\n     poly < mlsysinfo.sml\n\
                \** from the HOL/developers directory\n\n"
        else ()
end
handle Overflow => use "mosmlsysinfo.sml";
