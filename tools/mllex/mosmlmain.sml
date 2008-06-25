structure mosmlmain =
struct

val name = CommandLine.name()
val _ = case CommandLine.arguments() of
          [] => (TextIO.output(TextIO.stdErr, name ^ ": no arguments\n");
                 OS.Process.exit OS.Process.failure)
        | args => List.app LexGen.lexGen args

end
