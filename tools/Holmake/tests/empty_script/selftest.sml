open testutils
val cd = OS.FileSys.chDir

infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)

val _ = cd "dir";

val _ = Systeml.systeml ["Holmake", "cleanAll"]

fun pluckk P k l =
  case l of
      [] => NONE
    | h::t => if P h then SOME (k h t)
              else pluckk P (fn h' => fn t => k h' (h::t)) t
fun pluck P l = pluckk P (fn h => fn t => (h, t)) l

fun grep pats f =
  let
    val istrm = TextIO.openIn f
    fun return b = (TextIO.closeIn istrm; b)
    fun recurse pats =
      case pats of
          [] => return true
        | _ =>
          let
            fun checking () =
              case TextIO.inputLine istrm of
                  NONE => return false
                | SOME line =>
                  (case pluck (fn p => String.isSubstring p line) pats of
                       NONE => checking()
                     | SOME (_, t) => recurse t)
          in
            checking()
          end
  in
    recurse pats
  end

val pats = ["Couldn't find required output file: emptyTheory",
            "Couldn't find required output file: noproductTheory"]

val desc = "failing Holmake with empty/non-producing scripts"
val _ = if Systeml.ML_SYSNAME = "poly" then
          let
            val _ = tprint ("Checking parallel "^desc)
            val res = Systeml.systeml_out {outfile="make.log"}
                            ["Holmake", "--qof", "-k", "-j4", "--holstate",
                             Globals.HOLDIR ++ "bin" ++ "hol.state0"]
          in
            if OS.Process.isSuccess res then die "Holmake succeeded incorrectly"
            else if grep pats "make.log" then OK()
            else die "Couldn't see 'Couldn't find required output' output"
          end
        else ()

val _ = tprint ("Checking sequential " ^ desc)
val res = Systeml.systeml_out {outfile="make.log"}
                              ["Holmake", "--qof", "-k", "--holstate",
                               Globals.HOLDIR ++ "bin" ++ "hol.state0", "-j1"]

val _ = if OS.Process.isSuccess res then die "Holmake succeeded incorrectly"
        else if grep pats "make.log" then OK()
        else die "Couldn't see 'Couldn't find required output' output"
