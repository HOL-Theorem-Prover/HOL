(* Scenario "shadowed-load" of the fresh-load suite, kept in its own launcher
   so the sealed selftest.sml is unchanged.  Before any extension module is
   loaded, each basis name that HOL libraries re-export for toplevel `open`
   is rebound with an incompatible type; every added module must still load.
   Deliberately no static dependency on the simplifier. *)
open HolKernel testutils

val _ = boolTheory.TRUTH

fun obs key value = print ("OBS " ^ key ^ "=" ^
  String.translate (fn #"\n" => "\\n" | c => str c) value ^ "\n")
fun check label ok =
  (tprint label; if ok then OK () else die label)
fun env s =
  case OS.Process.getEnv s of
      SOME v => v
    | NONE => raise Fail ("missing environment variable " ^ s)
val scenario = env "SIMP_COMPAT_SCENARIO"
val _ = obs "scenario" scenario
val _ = check "scenario is shadowed-load" (scenario = "shadowed-load")
val _ = check "fail-fast test mode" (!diemode = ProcessExit)

fun observed stage f =
  let
    val old = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    val _ = Feedback.WARNING_outstream :=
      (fn s => (warnings := s :: !warnings; old s))
    val result = (SOME (f ()) handle e =>
      (obs (stage ^ ".exception")
         (General.exnName e ^ ": " ^ Feedback.exn_to_string e); NONE))
    val _ = Feedback.WARNING_outstream := old
    val _ = if Option.isSome result then obs (stage ^ ".exception") "none"
            else ()
    val _ = obs (stage ^ ".warnings") (Int.toString (length (!warnings)))
  in
    (Option.isSome result, null (!warnings))
  end
fun require_result label (succeeded,silent) =
  (check (label ^ " succeeds") succeeded;
   check (label ^ " without warnings") silent)

(* Basis names rebound by libraries designed for toplevel `open`.  size
   (patriciaLib) and concat (hurdUtils) are type-incompatible re-exports, so
   an unqualified use in a module compiled by `load` after such an open
   fails to compile.  foldr (liteLib, same type) is kept defensively by
   decision.  Not every re-export is listed: liteLib.foldl and hurdUtils.map
   are compatible with the basis and are excluded.  `load` compiles modules
   absent from the heap in the user's toplevel, so these names must be
   qualified there. *)
val shadowed = ["size", "concat", "foldr"]

fun compile_string src =
  let
    val pos = ref 0
    fun next () =
      if !pos < String.size src
      then SOME (String.sub (src, !pos)) before pos := !pos + 1
      else NONE
  in
    PolyML.compiler
      (next, [PolyML.Compiler.CPNameSpace PolyML.globalNameSpace,
              PolyML.Compiler.CPOutStream (fn _ => ())]) ()
  end
fun compiles src = (compile_string src; true) handle _ => false

(* The extension modules: every source of this directory matching one of
   ext_patterns (`*` only), minus theory scripts.  The same patterns appear
   in the Holmakefile wildcard FRESH_EXT_UO; the static check compares both
   with the added modules. *)
val ext_patterns = ["*Ext*", "split*", "SplitData"]
fun glob [] [] = true
  | glob (#"*" :: ps) s =
      glob ps s orelse (case s of [] => false | _ :: t => glob (#"*" :: ps) t)
  | glob (p :: ps) (c :: cs) = p = c andalso glob ps cs
  | glob _ _ = false
fun is_extension f =
  let val {base,ext} = OS.Path.splitBaseExt f
  in
    ext = SOME "sml" andalso not (String.isSuffix "Script" base) andalso
    List.exists (fn p => glob (String.explode p) (String.explode base))
                ext_patterns
  end
fun extension_modules dir =
  let
    val d = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir d of
          NONE => acc
        | SOME f => loop (if is_extension f then #base (OS.Path.splitBaseExt f)
                                                :: acc else acc)
    val names = loop [] before OS.FileSys.closeDir d
  in Listsort.sort String.compare names end

fun shadowed_load () =
  let
    val dir = OS.Path.dir (env "SIMP_COMPAT_PATH")
    val modules = extension_modules dir
    val _ = check "extension modules found" (not (null modules))
    val _ = List.app (fn n => obs "shadowed.module" n) modules
    (* HOL sources outside the added set use these names unqualified,
       and are out of scope here: src/HolSat/dimacsTools.sml:147,149
       (foldr, via tautLib) and src/combin/combinpp.sml:196 (size, via
       combinTheory).  Load them before shadowing so only the added modules
       are tested. *)
    val _ = List.app Meta.load ["tautLib", "combinTheory"]
    val _ = check "no extension module is preloaded" (List.all (fn m =>
      not (List.exists (fn l => l = m) (Meta.loaded ()))) modules)
    val _ = check "shadowing compiles" (List.all (fn n =>
      compiles ("val " ^ n ^ " = ();")) shadowed)
    (* One declaration per call: the first failure would hide the rest. *)
    val _ = check "size no longer compiles at the basis type"
      (not (compiles "val _ = size \"x\";"))
    val _ = check "concat no longer compiles at the basis type"
      (not (compiles "val _ = concat [\"a\"];"))
    val _ = check "foldr no longer compiles at the basis type"
      (not (compiles "val _ = foldr op+ 0 [1];"))
  in
    List.app (fn m =>
      require_result ("shadowed-toplevel load of " ^ m)
        (observed ("load." ^ m)
           (fn () => Meta.load (OS.Path.concat (dir, m)))))
      modules
  end

val _ = shadowed_load ()
val _ = obs "result" "pass"
val _ = OS.Process.exit OS.Process.success
