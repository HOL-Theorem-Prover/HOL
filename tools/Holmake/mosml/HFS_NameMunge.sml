structure HFS_NameMunge :> HFS_NameMunge =
struct

val HOLOBJDIR = "."


fun HOLtoFS nm = NONE

fun toFSfn writep f nm = f nm

type dirstream = OS.FileSys.dirstream

val openDir = OS.FileSys.openDir
val readDir = OS.FileSys.readDir
val closeDir = OS.FileSys.closeDir

end (* struct *)
