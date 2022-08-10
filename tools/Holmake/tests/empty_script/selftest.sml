open testutils
val cd = OS.FileSys.chDir

infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)

val _ = cd "dir";

val hm = Globals.HOLDIR ++ "bin" ++ "Holmake"

val _ = Systeml.systeml [hm, "cleanAll"]

fun pluckk P k l =
  case l of
      [] => NONE
    | h::t => if P h then SOME (k h t)
              else pluckk P (fn h' => fn t => k h' (h::t)) t
fun pluck P l = pluckk P (fn h => fn t => (h, t)) l

fun find1 s ss =
    let val (_, rest) = Substring.position s ss
    in
      if Substring.isPrefix s rest then SOME rest else NONE
    end

fun find_all [] ss = true
  | find_all (s::rest) ss =
      case find1 s ss of
          NONE => false
        | SOME ss' => find_all rest ss'

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
                  (case pluck (fn p => String.isSubstring (hd p) line) pats of
                       NONE => checking()
                     | SOME (p, t) =>
                       if find_all p (Substring.full line) then recurse t
                       else checking())
          in
            checking()
          end
  in
    recurse pats
  end

val pats = [["Couldn't find required output file:", "emptyTheory"],
            ["Couldn't find required output file:", "noproductTheory"]]

val desc = "failing Holmake with empty/non-producing scripts"
val holstate_sfx = ["--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]
val _ = if Systeml.ML_SYSNAME = "poly" then
          let
            val _ = tprint ("Checking parallel "^desc)
            val res = Systeml.systeml_out {outfile="make.log"}
                                          ([hm, "--qof", "-k", "-j4"] @
                                           holstate_sfx)
          in
            if OS.Process.isSuccess res then die "Holmake succeeded incorrectly"
            else if grep pats "make.log" then OK()
            else die "Couldn't see 'Couldn't find required output' output"
          end
        else ()

val _ = tprint ("Checking sequential " ^ desc)
val res = Systeml.systeml_out {outfile="make.log"}
                              ([hm, "--qof", "-k", "-j1"] @
                               (if Systeml.ML_SYSNAME = "poly" then
                                  holstate_sfx
                                else []))

val _ = if OS.Process.isSuccess res then die "Holmake succeeded incorrectly"
        else if grep pats "make.log" then OK()
        else die "Couldn't see 'Couldn't find required output' output"
