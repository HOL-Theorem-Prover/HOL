(* this is an -*- sml -*- file*)
local
infix ++
fun p1 ++ p2 = OS.Path.concat (p1,p2)
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun readchomp () =
    Option.map (fn s => String.substring(s,0,size s - 1))
               (TextIO.inputLine TextIO.stdIn)
val name = case readchomp() of
             NONE => die "No heap name"
           | SOME s => s
fun load_stdin_deps () =
    case readchomp() of
      NONE => ()
    | SOME s => (load s ; load_stdin_deps())
val _ = load_stdin_deps();
fun main () =
  (List.app use (CommandLine.arguments ());
   PolyML.rootFunction ());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export (name, main);
in
val _ = ()
end;
