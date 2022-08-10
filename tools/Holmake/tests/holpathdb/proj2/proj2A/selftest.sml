open testutils

infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)

val _ = tprint "Checking holpathdb bindings make it into interactive sessions"

val _ = Systeml.system_ps (Globals.HOLDIR ++ "bin" ++ "hol.bare" ^ " < input > /dev/null 2>&1")

exception InternalDie of string

val _ = let
  val istrmr = Exn.capture TextIO.openIn "output"
  val istrm = case istrmr of
                  Res i => i
                | Exn e => raise InternalDie
                                 ("Exception: "^General.exnMessage e)
in
  case TextIO.inputLine istrm of
      SOME s =>
      if String.isSubstring "tools/Holmake/tests/holpathdb/proj2" s then
        OK()
      else die ("Saw:\n  "^ s)
    | NONE => die "Nothing in \"output\""
end handle InternalDie s => die s;
