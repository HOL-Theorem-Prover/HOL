structure LTSprimitives =
struct


infix ++
val op++ = OS.Path.concat

fun primLink {from,to} =
    let
    in
      if OS.FileSys.access(to, []) then
        OS.FileSys.remove to
      else ();
      Posix.FileSys.symlink{old=from,new=to}
    end

fun appendToSRCFILES paths =
    let val srcfiles = Systeml.HOLDIR ++ "sigobj" ++ "SRCFILES"
        open Posix.IO Posix.FileSys
        val srcfd =
            createf (srcfiles, O_WRONLY, O.append, S.flags [S.irusr,S.iwusr])
        val lock = FLock.flock{
              ltype = F_WRLCK, whence = SEEK_CUR, len = 0, start = 0, pid = NONE
            }
        val _ = setlkw(srcfd,lock)
        fun writeLine p =
            writeVec(
              srcfd,
              Word8VectorSlice.slice(Byte.stringToBytes (p ^ "\n"), 0, NONE)
            )
    in
      List.app (ignore o writeLine) paths;
      close srcfd
    end


end
