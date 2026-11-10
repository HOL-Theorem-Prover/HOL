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

fun read_files_with_objs {dirname} P action a0 =
    let
      open OS.FileSys
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop a0 =
          case readDir ds of
              NONE => (closeDir ds; a0)
            | SOME nextfile =>
              loop (if P nextfile then
                      action {fakearcs=[],base=nextfile} a0
                    else a0)
    in
      (* loop closes ds itself when readDir runs out; this covers the
         exception path only.  `handle' binds looser than `before', so a
         trailing `before closeDir ds' here would sit inside the handler
         arm after the raise, and never run. *)
      loop a0 handle e => (closeDir ds; raise e)
    end

fun clean_last () = ()

end (* struct *)
