if String.isPrefix "Fail: " (General.exnMessage (General.Fail ""))
  (* At this point, the user could have used MoscowML or SML/NJ.
     To differentiate between these, we (ab)use a bug in MoscowML.
     Thanks to Michael Norrish to making us aware of this. *)
   then let
     val name = ref ""
     fun f _ = (name := "mosml"; fn _ => ())
     val _ = f () (name := "smlnj")
     val script = if !name = "mosml" then "tools/configure-mosml.sml"
                  else if !name = "smlnj" then "tools-smlnj/smart-configure.sml"
                  else raise Fail "unreachable"
    in use script end
else use "tools-poly/smart-configure.sml"
     handle e =>
       if String.isPrefix "Io" (General.exnMessage e) then
          TextIO.print
             "\n\n** You must do\n     poly < tools/smart-configure.sml\n\
             \** from the root HOL directory\n\n"
       else ()
