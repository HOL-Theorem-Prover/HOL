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

(* sleeping, with an action every second *)
fun delay limit action = let
  fun loop cnt =
      if cnt >= limit then ()
      else (action cnt;
            Posix.Process.sleep (Time.fromSeconds 1);
            loop (cnt + 1))
in
  loop 0
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

fun check_dir nm privs candidate = let
  open OS.FileSys
  val p = OS.Path.concat(candidate,nm)
in
  if access(p, privs) then SOME (OS.Path.dir (fullPath p)) else NONE
end
val check_poly = check_dir "poly" [OS.FileSys.A_EXEC]
val check_libpoly = check_dir "libpolymain.a" [OS.FileSys.A_READ]

fun findpartial f [] = NONE
  | findpartial f (h::t) =
    case f h of NONE => findpartial f t | x => x

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
            findpartial check_poly search_these
          end
in
  case cand of
    NONE => ""
  | SOME c => let
    in
      case check_poly c of
        SOME p => OS.Path.concat(p,"poly")
      | NONE =>
        (print "\nCouldn't figure out location of poly executable\n\
               \Please write file tools-poly/poly-includes.ML to specify it.\n\
               \This file should include a line of the form\n\
               \  val poly = \"path-to-poly\";\n";
         "")
    end
end;

val polymllibdir =
    if poly <> "" then let
        val _ = determining "polymllibdir"
        val p as {arcs,isAbs,vol} = OS.Path.fromString poly
        val (dirname, _) = frontlast arcs
        val (parent, probably_bin) = frontlast dirname
        val _ = if probably_bin <> "bin" then
                  print "\nSurprised that poly is not in a \"bin\" directory\n"
                else ()
        val candidate = OS.Path.toString { arcs = parent @ ["lib"], vol = vol,
                                           isAbs = isAbs }
      in
        case check_libpoly candidate of
          SOME c => c
        | NONE =>
          (print
               "\nCouldn't find libpolymain.a in sister lib directory\n\
               \Please write file tools-poly/poly-includes.ML to specify it.\n\
               \This file should include a line of the form\n\
               \  val polymllibdir = \"path-to-libpolymain.a\";\n";
           "")
      end
    else "";

val dynlib_available = false;

print "\n";

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
              "!!  Write a tools-poly/poly-includes.ML file to fix this\n");
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
