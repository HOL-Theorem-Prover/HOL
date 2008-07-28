let
  fun fact n acc = if n <= 1 then acc else fact (n - 1) (n * acc) 
in
  fact 21 1;  
  use "tools-poly/smart-configure.sml"
     handle e =>
        if String.isPrefix "Io" (exnMessage e) then
          print "\n\n** You must do\n     poly < tools/smart-configure.sml\n\
                \** from the root HOL directory\n\n"
        else ()
end 
handle Overflow => use "tools/configure-mosml.sml"; 
