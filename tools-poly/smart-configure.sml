(*quietdec := true;
app load ["Mosml", "Process", "Path", "FileSys", "Timer", "Real", "Int",
          "Bool", "OS"] ;
open Mosml;
*)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

(* utility functions *)
fun readdir s = let
  val ds = OS.FileSys.openDir s
  fun recurse acc =
      case OS.FileSys.readDir ds of
        NONE => acc
      | SOME s => recurse (s::acc)
in
  recurse [] before OS.FileSys.closeDir ds
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

val currentdir = OS.FileSys.getDir();

fun dirify {arcs,isAbs,vol} =
    OS.Path.toString {arcs = #1 (frontlast arcs), isAbs = isAbs, vol = vol};

determining "holdir";

val holdir = let
  val cdir_files = readdir currentdir
in
  if mem "sigobj" cdir_files andalso mem "std.prelude" cdir_files then
    currentdir
  else if mem "smart-configure.sml" cdir_files andalso
          mem "configure.sml" cdir_files
  then dirify (OS.Path.fromString currentdir)
  else (print "\n\n*** Couldn't determine holdir; ";
        print "please run me from the root HOL directory\n";
        OS.Process.exit OS.Process.failure)
end;

val _ = let
in
  OS.FileSys.chDir (OS.Path.concat (holdir, "tools-poly"));
  use "poly/poly-init.ML";
  OS.FileSys.chDir currentdir
end;

determining "OS";
val OS = let
  val {vol,...} = OS.Path.fromString currentdir
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
                    OS.Process.exit OS.Process.failure)
  else "winNT"
end;


determining "poly";

fun check_poly candidate = let
  open OS.FileSys
in
  access(OS.Path.concat(candidate,"poly"), [A_EXEC])
end

val poly = let
  val nm = CommandLine.name()
  val p as {arcs, isAbs, vol} = OS.Path.fromString nm
  val cand =
      if isAbs then SOME (dirify p)
      else if length arcs > 1 then
        SOME (OS.Path.mkAbsolute { path = dirify p,
                                   relativeTo = OS.FileSys.getDir()})
      else (* examine PATH variable *)
        case OS.Process.getEnv "PATH" of
          NONE => NONE
        | SOME elist => let
            val sep = case OS of "winNT" => #";" | _ => #":"
            val search_these = String.fields (fn c => c = sep) elist
          in
            List.find check_poly search_these
          end
in
  case cand of
    NONE => ""
  | SOME c => if check_poly c then OS.Path.concat(c,"poly")
              else (print "Couldn't figure out location of poly executable\
                          \ - hope you have poly-includes.ML to specify it";
                    "")
end;


determining "dynlib_available";

(*
val dynlib_available = (load "Dynlib"; true) handle _ => false;
*)

val dynlib_available = false;

print "\n";

val polymllibdir = "";
val _ = let
  val override = OS.Path.concat(holdir, "tools-poly/poly-includes.ML")
in
  if OS.FileSys.access (override, [OS.FileSys.A_READ]) then
    (print "\n[Using override file!]\n\n";
     use override)
  else ()
end;

fun verdict (prompt, value) =
    if value = "" then
      (print ("\n*** No value for "^prompt^
              "!!  Use tools-poly/poly-includes.ML to fix this\n");
       OS.Process.exit OS.Process.failure)
    else
      (print (StringCvt.padRight #" " 20 (prompt^":"));
       print value;
       print "\n");

verdict ("OS", OS);
verdict ("poly", poly);
verdict ("polymllibdir", polymllibdir);
verdict ("holdir", holdir);
verdict ("dynlib_available", Bool.toString dynlib_available);

print "\nConfiguration will begin with above values.  If they are wrong\n";
print "press Control-C.\n\n";

delay 3
      (fn n => print ("\rWill continue in "^Int.toString (3 - n)^" seconds."))
      handle Interrupt => (print "\n"; OS.Process.exit OS.Process.failure);

print "\n";

val configfile = OS.Path.concat (OS.Path.concat (holdir, "tools-poly"), "configure.sml");


use configfile;
