structure HFS_NameMunge :> HFS_NameMunge =
struct

val HOLOBJDIR = "."

exception DirNotFound

infix ++
val op++ = OS.Path.concat

fun HOLtoFS nm = NONE

fun toFSfn writep f nm = f nm

(* Moscow ML builds keep products beside their sources; there is no
   separate artifact root. *)
type layout = {srcroot : string, objroot : string}
fun configure NONE = ()
  | configure (SOME _) =
    (TextIO.output (TextIO.stdErr,
                    "Artifact layout unsupported under Moscow ML; ignored\n");
     TextIO.flushOut TextIO.stdErr)
fun current_layout () = NONE : layout option
fun layout_from_env () = NONE : layout option
fun owned_by_layout _ = false
fun objdir_for d = d
fun depdir_for d = d ++ ".hol/make-deps"
fun logdir_for d = d ++ ".hol/logs"
fun lockdir_for d = d ++ ".hol/locks"
fun docsdir_for d = d ++ ".hol/docs"
fun project_state_dir r = r ++ ".hol"
fun holobjdir_var_for _ = HOLOBJDIR
fun artifact_dirs_for _ = [] : string list
fun FStoHOL p = SOME p

type dirstream = OS.FileSys.dirstream

val openDir = OS.FileSys.openDir
val readDir = OS.FileSys.readDir
val closeDir = OS.FileSys.closeDir

fun read_files_with_objs {dirname} P action a0 =
    let
      open OS.FileSys
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop a0 =
          case readDir ds of
              NONE => (closeDir ds; a0)
            | SOME nextfile =>
              loop (if P nextfile then
                      action {physdir=dirname,base=nextfile} a0
                    else a0)
    in
      loop a0 handle e => (closeDir ds; raise e) before
      closeDir ds
    end

fun clean_last () = ()

end (* struct *)
