quietdec := true;
app load ["Mosml", "Process", "Path", "FileSys", "Timer", "Real", "Int",
          "Bool", "OS", "CommandLine"] ;
open Mosml;

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

(* Thanks to Ken Friis Larsen for this very cute trick *)
val version_string =
    List.nth([], 1) handle Option => "2.01" | Subscript => "2.10";

val _ = if version_string = "2.01" then
          die "HOL requires at least Moscow ML 2.10"
        else ();

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

fun determining s =
    (print (s^" "); delay 1 (fn _ => ()));

(* action starts here *)
print "\nHOL smart configuration.\n\n";

print "Determining configuration parameters: ";
determining "OS";

val currentdir = FileSys.getDir()

val OS = let
  val {vol,...} = Path.fromString currentdir
in
  if vol = "" then (* i.e. Unix *)
    case Mosml.run "uname" ["-a"] "" of
      Success s => if String.isPrefix "Linux" s then
                     "linux"
                   else if String.isPrefix "SunOS" s then
                     "solaris"
                   else if String.isPrefix "Darwin" s then
                     "macosx"
                   else
                     "unix"
    | Failure s => (print "\nRunning uname failed with message: ";
                    print s;
                    Process.exit Process.failure)
  else "winNT"
end;

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

val exe_ext = if OS = "winNT" then ".exe" else "";
determining "mosmldir";

fun check_mosml candidate = let
  open FileSys
in
  access(Path.concat(candidate,"mosml"^exe_ext), [A_EXEC])
end

fun mosml_from_loadpath () = let
  val libdir = hd (!Meta.loadPath)
  val () = print ("\nMosml library directory (from loadPath) is "^libdir)
  val {arcs, isAbs, vol} = Path.fromString libdir
  val _ = isAbs orelse
          (print "\n\n*** ML library directory not specified with absolute";
           print "filename --- aborting\n";
           Process.exit Process.failure)
  val arcs = case frontlast arcs of
                 (arcs,  "lib") => arcs
               | ([],  ult)     => [ult]
               | (arcs,"mosml") => (* default since 2.10 *)
                 let val (arcs', pen) = frontlast arcs in
                     (if pen = "lib" then arcs' else arcs)
                 end
               | (arcs, _)      =>
                 (print "\nMosml library directory (from loadPath) not .../lib -- weird!\n";
                  arcs)
  val candidate =
      Path.toString {arcs = arcs @ ["bin"], isAbs = true, vol = vol}
  val _ = print ("\nUsing "^candidate^" for mosml directory (from loadPath)\n")
in
  if check_mosml candidate then candidate
  else (print "\nCan't find mosml -- hope you have it in a \
              \config-override file\n";
        "")
end;

fun dirify {arcs,isAbs,vol} =
    OS.Path.toString {arcs = #1 (frontlast arcs), isAbs = isAbs, vol = vol}


val mosmldir = let
  val nm = CommandLine.name()
  val p as {arcs, isAbs, vol} = OS.Path.fromString nm
  val cand =
      if isAbs then SOME (dirify p)
      else if length arcs > 1 then
        SOME (Path.mkAbsolute {path = dirify p,
                               relativeTo = OS.FileSys.getDir()})
      else (* examine PATH variable *)
        case OS.Process.getEnv "PATH" of
          NONE => NONE
        | SOME elist => let
            val sep = case OS of "winNT" => #";" | _ => #":"
            val search_these = String.fields (fn c => c = sep) elist
          in
            List.find check_mosml search_these
          end
in
  case cand of
    NONE => mosml_from_loadpath ()
  | SOME c => if check_mosml c then c else mosml_from_loadpath ()
end;

determining "holdir";

val holdir = let
  val cdir_files = readdir currentdir
in
  if mem "sigobj" cdir_files andalso mem "std.prelude" cdir_files then
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

determining "dynlib_available";

val dynlib_available = (load "Dynlib"; true) handle _ => false;

print "\n";

val DOT_PATH = SOME "";

val _ = let
  val override = Path.concat(holdir, "config-override")
in
  if FileSys.access (override, [FileSys.A_READ]) then
    (print "\n[Using override file!]\n\n";
     use override)
  else ()
end;

val DOT_PATH = if DOT_PATH = SOME "" then which "dot" else DOT_PATH;

fun verdict (prompt, value) =
    (print (StringCvt.padRight #" " 20 (prompt^":"));
     print value;
     print "\n");

fun optverdict (prompt, optvalue) =
  (print (StringCvt.padRight #" " 20 (prompt ^ ":"));
   print (case optvalue of NONE => "NONE" | SOME p => "SOME "^p);
   print "\n");

verdict ("OS", OS);
verdict ("mosmldir", mosmldir);
verdict ("holdir", holdir);
verdict ("dynlib_available", Bool.toString dynlib_available);
optverdict ("DOT_PATH", DOT_PATH);

val _ = let
  val mosml' = if OS = "winNT" then "mosmlc.exe" else "mosmlc"
in
  if FileSys.access (Path.concat(mosmldir, mosml'), [FileSys.A_EXEC]) then
    ()
  else (print ("\nCouldn't find executable mosmlc in "^mosmldir^"\n");
        print ("Giving up - please use config-override file to fix\n");
        Process.exit Process.failure)
end;

print "\nConfiguration will begin with above values.  If they are wrong\n";
print "press Control-C.\n\n";

delay 3
      (fn n => print ("\rWill continue in "^Int.toString (3 - n)^" seconds."))
      handle Interrupt => (print "\n"; Process.exit Process.failure);

print "\n";

val configfile = Path.concat (Path.concat (holdir, "tools"), "configure.sml");


use configfile;
