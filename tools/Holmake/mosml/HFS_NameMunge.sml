structure HFS_NameMunge :> HFS_NameMunge =
struct

val HOLOBJDIR = "."

exception DirNotFound


fun HOLtoFS nm = NONE

fun toFSfn writep f nm = f nm

type dirstream = OS.FileSys.dirstream

val openDir = OS.FileSys.openDir
val readDir = OS.FileSys.readDir
val closeDir = OS.FileSys.closeDir

fun read_files_with_objs {dirname} P action =
    let
      open OS.FileSys
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop () =
          case readDir ds of
              NONE => closeDir ds
            | SOME nextfile =>
              (if P nextfile then action nextfile else (); loop())
    in
      loop() handle e => (closeDir ds; raise e);
      closeDir ds
    end

fun clean_last () = ()

end (* struct *)
