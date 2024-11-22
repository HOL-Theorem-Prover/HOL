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
exception Holdep_Error of string
open HOLFileSys
structure FileSys = HOLFileSys

fun normPath s = Path.toString(Path.fromString s)
fun manglefilename s = normPath s
fun errMsg str = stdErr_out (str ^ "\n\n")

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
end handle OS.Path.InvalidArc =>
  raise Holdep_Error ("Bad module name \"" ^ s ^ "\"")

fun isTheory s =
    if String.isSuffix "Theory" s andalso size s > 6 then
      SOME (String.substring(s, 0, size s - 6))
    else NONE

fun addThExt s s' ext = addExt (addDir (Path.dir s') s) ext
fun outname (rcd as {assumes,includes}) cdir linenum (s, res) =
  case isTheory s of
    SOME n =>
    let
    in
      (* allow a dependency on a theory if we can see a script.sml file *)
      case access rcd cdir (n^"Script") "sml" of
        SOME s' => addThExt s s' "uo" :: res
      | NONE => let
        in
          (* or, if we can see the theory.ui file already; which might
             happen if the theory file is in sigobj *)
          case access rcd cdir (n^"Theory") "ui" of
            SOME s' => addThExt s s' "uo" :: res
          | NONE => res
        end
    end
  | _ =>
    let
    in
      case access rcd cdir s "sig" of
        SOME s' => addExt s' "uo" :: res
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
                SOME s' => addExt s' "uo" :: res
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

fun uqfname_holdep fname =
  let
    val reader = HolParser.fileToReader fname
  in
    Holdep_tokens.reader_deps (fname, #read reader)
  end

fun read {assumes, includes, srcext, objext, filename} = let
  val mentions = uqfname_holdep (addExt filename srcext)
  val curr_dir = Path.dir filename
  val outrcd = {assumes = assumes, includes = includes}
  val (targetname, res0) = beginentry objext (manglefilename filename)
  val res = Binarymap.foldl
              (fn (s, linenum, acc) =>
                  outname outrcd curr_dir linenum (manglefilename s, acc))
              res0
              mentions
in
  {tgt = targetname, deps = res}
end handle Holdep_Error s => raise Holdep_Error (filename ^ ": " ^ s)
         | Holdep_tokens.LEX_ERROR s => raise Holdep_Error s;

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
    diag (fn () => "Holdep: " ^ #tgt results ^ ": " ^
                   String.concatWith ", " (#deps results));
    results
  end
   handle e as OS.SysErr (str, _) => (errMsg str; raise e)

end (* struct *)
