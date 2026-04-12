fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

structure FileSys = OS.FileSys
structure Process = OS.Process
structure Path = OS.Path

(* utility functions *)
fun readdir s = let
  val ds = FileSys.openDir s
  fun recurse acc =
      case FileSys.readDir ds of
        NONE => acc
      | SOME s => recurse (s::acc)
in
  recurse [] before FileSys.closeDir ds
end;

fun mem x [] = false
  | mem x (h::t) = x = h orelse mem x t

fun frontlast [] = raise Fail "frontlast: failure"
  | frontlast [h] = ([], h)
  | frontlast (h::t) = let val (f,l) = frontlast t in (h::f, l) end;

(* returns a function of type unit -> int, which returns time elapsed in
   seconds since the call to start_timer() *)
fun start_timer() = let
  val timer = Timer.startRealTimer()
in
  fn () => let
       val time_now = Timer.checkRealTimer timer
     in
       Real.floor (Time.toReal time_now)
     end handle Time.Time => 0
end

(* busy loop sleeping *)
fun delay limit action = let
  val timer = start_timer()
  fun loop last = let
    val elapsed = timer()
  in
    if elapsed = last then loop last
    else (action elapsed; if elapsed >= limit then () else loop elapsed)
  end
in
  action 0; loop 0
end;

fun determining s = print (s^" ");

(* action starts here *)
print "\nHOL smart configuration.\n\n";

print "Determining configuration parameters: ";
determining "OS";

val currentdir = FileSys.getDir()

val OS =
  (* Derived getOSName return values from SML/NJ's getOSKind implemention in
     sysinfo.sml *)
  case SMLofNJ.SysInfo.getOSName() of
    "Solaris" => "solaris"
  | "AIX" => "unix"
  | "Linux" => "linux"
  | "BSD" => "unix"
  | "Darwin" => "macosx"
  | "Cygwin" => "unix"
  | "Win32" => "winNT"
  | s => raise Fail ("unknown OS: " ^ s);

fun findpartial f [] = NONE
  | findpartial f (h::t) =
    case f h of NONE => findpartial f t | x => x

fun which arg =
  let
    open OS.FileSys
    val sepc = if OS = "winNT" then #";" else #":"
    fun check p =
      let
        val fname = OS.Path.concat(p, arg)
      in
        if access (fname, [A_READ, A_EXEC]) then
          SOME
            (OS.Path.mkAbsolute{path = fname, relativeTo = OS.FileSys.getDir()})
        else NONE
      end
  in
    case OS.Process.getEnv "PATH" of
        SOME path =>
        let
          val paths = (if OS = "winNT" then ["."] else []) @
                      String.fields (fn c => c = sepc) path
        in
          findpartial check paths
        end
      | NONE => if OS = "winNT" then check "." else NONE
  end

val holdir = let
  val _ = determining "holdir"
  val cdir_files = readdir currentdir
in
  if mem "sigobj" cdir_files andalso mem "tools" cdir_files then
    currentdir
  else if mem "smart-configure.sml" cdir_files andalso
          mem "configure.sml" cdir_files
  then let
      val {arcs, isAbs, vol} = Path.fromString currentdir
      val (arcs', _) = frontlast arcs
    in
      Path.toString {arcs = arcs', isAbs = isAbs, vol = vol}
    end
  else (print "\n\n*** Couldn't determine holdir; ";
        print "please run me from the root HOL directory\n";
        Process.exit Process.failure)
end;

val DOT_PATH = SOME "";
val GNUMAKE = "";
val SHASUM = "";

val _ = let
  val override = Path.concat(holdir, "config-override")
in
  if FileSys.access (override, [FileSys.A_READ]) then
    (print "\n[Using override file!]\n\n";
     use override)
  else ()
end;

val DOT_PATH = if DOT_PATH = SOME "" then which "dot" else DOT_PATH;
val GNUMAKE = if GNUMAKE = "" then
                (determining "GNUMAKE";
                 case OS.Process.getEnv "MAKE" of
                     NONE => "make"
                   | SOME s => s)
              else GNUMAKE;

fun find_in_likelies_or_path dirs s =
    let
      fun findexec s dir =
          let
            val p = OS.Path.concat(dir,s)
          in
            if OS.FileSys.access(p, [OS.FileSys.A_EXEC]) then
              SOME p
            else NONE
          end
    in
      case List.mapPartial (findexec s) dirs of
          h :: _ => SOME (h, true)
        | [] =>
          case which s of
              NONE => NONE
            | SOME p => SOME (p, false)
    end

fun find_multinamed corename dirs names =
    case List.mapPartial (find_in_likelies_or_path dirs) names of
        [] => die ("Couldn't find executable `" ^ corename ^ "'.")
      | h :: _ => h

fun find_in_bin_or_path s =
    case find_in_likelies_or_path ["/bin"] s of
        SOME r => r
      | NONE => die ("Couldn't find executable `" ^ s ^ "'.")

val _ = print "\n";

fun verdict (prompt, value) =
    (print (StringCvt.padRight #" " 20 (prompt^":"));
     print value;
     print "\n");

fun optverdict (prompt, optvalue) =
  (print (StringCvt.padRight #" " 20 (prompt ^ ":"));
   print (case optvalue of NONE => "NONE" | SOME p => "SOME "^p);
   print "\n");

fun dfltverdict (prompt, (value, dflt)) =
    if dflt then value
    else (print (StringCvt.padRight #" " 20 (prompt ^ ":") ^ value); value);


verdict ("OS", OS);
verdict ("holdir", holdir);
verdict ("GNUMAKE", GNUMAKE);
optverdict ("DOT_PATH", DOT_PATH);
val MV = dfltverdict ("MV", find_in_bin_or_path "mv");
val CP = dfltverdict ("CP", find_in_bin_or_path "cp");
val SHASUM =
    if SHASUM = "" then
      dfltverdict (
        "SHASUM",
        find_multinamed "shasum" ["/usr/bin", "/usr/sbin"] ["sha1sum", "shasum"]
      )
    else SHASUM;

print "\nConfiguration will begin with above values.  If they are wrong\n";
print "press Control-C.\n\n";

delay 3
      (fn n => print ("\rWill continue in "^Int.toString (3 - n)^" seconds."))
      handle Interrupt => (print "\n"; Process.exit Process.failure);

print "\n";

val configfile = Path.concat (Path.concat (holdir, "tools-smlnj"), "configure.sml");


use configfile;
