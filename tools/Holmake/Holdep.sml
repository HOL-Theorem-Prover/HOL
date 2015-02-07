(* Holdep -- computing dependencies for a (list of) Moscow ML
   source files. Also has knowledge of HOL script and theory files.
   Handles strings and nested comments correctly;

   DOES NOT normalize file names under DOS. (yet)

  This has been adapted from the mosmldep in the MoscowML compiler
  sources, first by Ken Larsen and later by Konrad Slind and
  Michael Norrish.
*)
structure Holdep :> Holdep =
struct

structure Process = OS.Process
structure Path = OS.Path
structure FileSys = OS.FileSys
exception Holdep_Error of string

fun normPath s = Path.toString(Path.fromString s)
fun manglefilename s = normPath s
fun errMsg str = TextIO.output(TextIO.stdErr, str ^ "\n\n")

fun addExt s ""  = normPath s
  | addExt s ext = normPath s^"."^ext;
fun addDir dir s = Path.joinDirFile{dir=normPath dir,file=s}

val space = " ";
fun spacify [] = []
  | spacify [x] = [x]
  | spacify (h::t) = h::space::spacify t;

fun access {assumes, includes} cdir s ext = let
  val sext = addExt s ext
  fun inDir dir = FileSys.access (addDir dir sext, [])
in
  if inDir cdir orelse List.exists (fn nm => nm = sext) assumes then SOME s
  else
    case List.find inDir includes of
      SOME dir => SOME(addDir dir s)
    | NONE     => NONE
end

fun isTheory s =
  case List.rev(String.explode s) of
    #"y" :: #"r" :: #"o" :: #"e" :: #"h" :: #"T" :: n::ame =>
      SOME(String.implode(List.rev (n::ame)))
  | _ => NONE

fun addThExt s s' ext = addExt (addDir (Path.dir s') s) ext
fun outname (rcd as {assumes,includes}) cdir (s, res) =
  case isTheory s of
    SOME n => let
    in
      (* allow a dependency on a theory if we can see a script.sml file *)
      case access rcd cdir (n^"Script") "sml" of
        SOME s' => addThExt s s' "ui" :: res
      | NONE => let
        in
          (* or, if we can see the theory.ui file already; which might
             happen if the theory file is in sigobj *)
          case access rcd cdir (n^"Theory") "ui" of
            SOME s' => addThExt s s' "ui" :: res
          | NONE => res
        end
    end
  | _ => let
    in
      case access rcd cdir s "sig" of
        SOME s' => addExt s' "ui" :: res
      | _       => let
        in
          case access rcd cdir s "sml" of
            (* this case handles the situation where there is no .sig file
               locally, but a .sml file instead; compiling this will generate
               the .ui file too.  We have to say that we're dependent
               on the .uo file because the automatic logic will then
               correctly hunt back to the .sml file *)
            SOME s' => addExt s' "uo" :: res
          | _       => let
            in
              (* this case added to cover the situations where we think we
                 are dependent on module foo, but we can't find foo.sml or
                 foo.sig.  This can happen when foo.sml exists in some
                 HOL directory but no foo.sig.  In this situation, the HOL
                 build process only copies foo.ui and foo.uo across to
                 sigobj (and not the .sig file that we usually find there),
                 so making the dependency analysis ignore foo.  We cover
                 this possibility by looking to see if we can see a .ui
                 file; if so, we can retain the dependency *)
              case access rcd cdir s "ui" of
                SOME s' => addExt s' "ui" :: res
              | NONE => res
            end
        end
    end

fun beginentry objext target = let
  val targetname = addExt target objext
in
  (targetname,
   if objext = "uo" andalso FileSys.access(addExt target "sig", []) then
     [addExt target "ui"]
   else [])
end;

val escape_space = let
  fun translation c = if c = #" " then "\\ "
                      else if c = #"\\" then "\\\\"
                      else str c
in
  String.translate translation
end
val escape_spaces = map escape_space


fun encode_for_HOLMKfile {tgt, deps} =
    if null deps then ""
    else
      escape_space tgt ^ ": " ^
      String.concat (spacify (rev ("\n" :: escape_spaces deps)))

fun scanFile {fname,actualfname} = let
  open Holdep_tokens
  val is = TextIO.openIn actualfname
in
  stream_deps (fname, is) before TextIO.closeIn is
end

fun read {assumes, includes, srcext, objext, filename} = let
  open OS.FileSys Systeml
  val op ^ = Path.concat
  val unquote = xable_string(Systeml.HOLDIR ^ "bin" ^ "unquote")
  val file0 = addExt filename srcext
  val actualfile =
      if access (unquote, [A_EXEC]) then let
          val newname = tmpName()
        in
          if Process.isSuccess (Systeml.systeml [unquote, file0, newname]) then
            newname
          else file0
        end
      else file0
  val mentions = scanFile {actualfname = actualfile, fname = file0}
  val _        = if actualfile <> file0 then
                   FileSys.remove actualfile handle _ => ()
                 else ()
  val curr_dir = Path.dir filename
  val outrcd = {assumes = assumes, includes = includes}
  val (targetname, res0) = beginentry objext (manglefilename filename);
  val res = Binaryset.foldl
              (fn (s, acc) => outname outrcd curr_dir (manglefilename s, acc))
              res0
              mentions
in
  {tgt = targetname, deps = res}
end

fun processfile {assumes, includes, fname = filename, diag} =
    let
	val {base, ext} = Path.splitBaseExt filename
    in
	case ext of
	    SOME "sig" => read {assumes = assumes, srcext = "sig", objext = "ui",
                                filename = base, includes = includes}
	  | SOME "sml" => read {assumes = assumes, srcext = "sml", objext = "uo",
                                filename = base, includes = includes}
	  | _          => {tgt = filename, deps = []}
    end

(* assumes parameter is a list of files that we assume can be built in this
   directory *)
fun main (r as {assumes, diag, includes, fname}) =
  let
    val results = processfile r
  in
    diag ("Holdep: " ^ #tgt results ^ ": " ^
          String.concatWith ", " (#deps results) ^ "\n");
    results
  end
   handle e as OS.SysErr (str, _) => (errMsg str; raise e)

end (* struct *)
