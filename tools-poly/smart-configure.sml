(*quietdec := true;
app load ["Mosml", "Process", "Path", "FileSys", "Timer", "Real", "Int",
          "Bool", "OS"] ;
open Mosml;
*)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;

(* utility functions *)
fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")
fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)

val _ = if PolyML.Compiler.compilerVersionNumber < 551 then
          die "Must be running PolyML with version >= 5.5.1\n"
        else ()

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

fun check_dir nm privs candidate = let
  open OS.FileSys
  val p = OS.Path.concat(candidate,nm)
in
  if access(p, privs) then SOME (OS.Path.dir (fullPath p)) else NONE
end
val check_poly = check_dir "poly" [OS.FileSys.A_EXEC]
val check_libpoly = check_dir "libpolymain.a" [OS.FileSys.A_READ]
fun check_polyc c =
  Option.map (fn p => OS.Path.concat(p,"polyc"))
             (check_dir "polyc" [OS.FileSys.A_EXEC] c)

fun findpartial f [] = NONE
  | findpartial f (h::t) =
    case f h of NONE => findpartial f t | x => x

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

fun determining s = print (s^" ");

(* action starts here *)
print "\nHOL smart configuration.\n\n";

val poly = ""
val polyc = NONE : string option
val polymllibdir = "";
val DOT_PATH = SOME "";
val MLTON = SOME "";
val GNUMAKE = "";
val POLY_LDFLAGS = [] : string list;
val EXTRA_POLY_LDFLAGS = [] : string list;
val POLY_LDFLAGS_STATIC = [] : string list;

val _ = let
  val override = "tools-poly/poly-includes.ML"
in
  if OS.FileSys.access (override, [OS.FileSys.A_READ]) then
    (print ("[Using override file "^override^"]\n\n");
     use override)
  else ()
end;

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
  else die "\n\n*** Couldn't determine holdir; \
            \please run me from the root HOL directory"
end;

val _ = let
in
  OS.FileSys.chDir (OS.Path.concat (holdir, "tools-poly"));
  use "poly/Mosml.sml";
  OS.FileSys.chDir currentdir
end;

val OS = let
  val _ = determining "OS"
  val {vol,...} = OS.Path.fromString currentdir
in
  if vol = "" then (* i.e. Unix *)
    case Mosml.run "uname" ["-a"] "" of
      Mosml.Success s => if String.isPrefix "Linux" s then
                     "linux"
                   else if String.isPrefix "SunOS" s then
                     "solaris"
                   else if String.isPrefix "Darwin" s then
                     "macosx"
                   else
                     "unix"
    | Mosml.Failure s => (print "\nRunning uname failed with message: ";
                    print s;
                    OS.Process.exit OS.Process.failure)
  else "winNT"
end

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

val polyinstruction =
    "Please write file tools-poly/poly-includes.ML to specify it \
    \properly.\n\
    \This file should include a line of the form\n\n\
    \  val poly = \"path-to-poly\";"
val (poly,polycopt) =
    if poly = "" then let
        val _ = determining "poly"
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
          NONE => die
                   ("\n\nYou ran poly on the commandline, but it doesn't seem \
                    \to be in your PATH.\n\
                    \I need to know where your poly executable is.\n" ^
                    polyinstruction)
        | SOME c => let
          in
            case check_poly c of
              SOME p => (OS.Path.concat(p,"poly"), check_polyc p)
            | NONE =>
              die ("\n\nI tried to figure out where your poly executable is\
                   \n\by examining your command-line.\n\
                   \But directory "^c^
                   "doesn't seem to contain a poly executable after \
                   \all\n" ^
                   polyinstruction)
          end
      end
    else
      case check_poly (OS.Path.dir poly) of
        NONE => die ("\n\nYour overrides file specifies bogus location '"
                     ^poly^
                     "'\nas the location of the poly executable.\n"^
                     polyinstruction)
      | SOME p => (OS.Path.concat(p, "poly"), check_polyc p)

val polyc =
    case polycopt of
        NONE => die ("Couldn't find polyc executable\n" ^ polyinstruction)
      | SOME p => p

val polylibsister = let
  val p as {arcs,isAbs,vol} = OS.Path.fromString poly
  val (dirname, _) = frontlast arcs
  val (parent, probably_bin) = frontlast dirname
  val _ = if probably_bin <> "bin" then
            warn "\nSurprised that poly is not in a \"bin\" directory"
          else ()
in
  OS.Path.toString { arcs = parent @ ["lib"], vol = vol, isAbs = isAbs }
end

val GNUMAKE:string  =
    if GNUMAKE = "" then
      let
        val _ = determining "GNUMAKE"
      in
        case OS.Process.getEnv "MAKE" of
            NONE => "make"
          | SOME s => s
      end
    else GNUMAKE

val polylibinstruction =
    "Please write file tools-poly/poly-includes.ML to specify it.\n\
    \This file should include a line of the form\n\n\
    \  val polymllibdir = \"path-to-dir-containing-libpolymain.a\";"

val polymllibdir =
    if polymllibdir = "" then let
        val _ = determining "polymllibdir"
      in
        case check_libpoly polylibsister of
          SOME c => c
        | NONE => die ("\n\nLooked in poly's sister lib directory "^
                       polylibsister ^
                       "\nand couldn't find libpolymain.a\n" ^
                       polylibinstruction)

      end
    else
      case check_libpoly polymllibdir of
        SOME c => c
      | NONE => die ("\n\nYour overrides file specifies bogus location '"
                     ^polymllibdir ^
                     "'\nas the location of libpolymain.a\n" ^
                     polylibinstruction);

val DOT_PATH = if DOT_PATH = SOME "" then which "dot" else DOT_PATH;

fun find_in_bin_or_path s =
    let
      val binpath = OS.Path.concat("/bin", s)
    in
      if OS.FileSys.access (binpath, [OS.FileSys.A_EXEC]) then
        (binpath, true)
      else
        case which s of
            NONE => die ("Couldn't find `" ^ s ^
                         "' executable. Please edit\n\
                         \tools-poly/poly-includes to include\n\
                         \  val " ^ String.translate (str o Char.toUpper) s ^
                         " = \"...\"")
          | SOME s => (s, false)
    end


val dynlib_available = false;

val MLTON = if MLTON = SOME "" then which "mlton" else MLTON;

print "\n";

fun verdict (prompt, value) =
    if value = "" then
      (print ("\n*** No value for "^prompt^
              "!!  Write a tools-poly/poly-includes.ML file to fix this\n");
       OS.Process.exit OS.Process.failure)
    else
      (print (StringCvt.padRight #" " 20 (prompt^":"));
       print value;
       print "\n");

fun optverdict (prompt, optvalue) =
  (print (StringCvt.padRight #" " 20 (prompt ^ ":"));
   print (case optvalue of NONE => "NONE" | SOME p => "SOME "^p);
   print "\n");

fun dfltverdict (prompt, (value, dflt)) =
    if dflt then value
    else (print (StringCvt.padRight #" " 20 (prompt ^ ":") ^ value ^ "\n"); value);

verdict ("OS", OS);
verdict ("poly", poly);
verdict ("polyc", polyc);
verdict ("polymllibdir", polymllibdir);
verdict ("holdir", holdir);
optverdict ("DOT_PATH", DOT_PATH);
optverdict ("MLTON", MLTON);
verdict ("GNUMAKE", GNUMAKE);

val MV = dfltverdict ("MV", find_in_bin_or_path "mv");
val CP = dfltverdict ("CP", find_in_bin_or_path "cp");

print "\nConfiguration will begin with above values.  If they are wrong\n";
print "press Control-C.\n\n";

delay 3
      (fn n => print ("\rWill continue in "^Int.toString (3 - n)^" seconds."))
      handle Interrupt => (print "\n"; OS.Process.exit OS.Process.failure);

print "\n";

val configfile = OS.Path.concat (OS.Path.concat (holdir, "tools-poly"), "configure.sml");


use configfile handle Fail s => die s;
