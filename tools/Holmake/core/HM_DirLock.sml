structure HM_DirLock :> HM_DirLock =
struct

datatype lockhandle = RealLock of Posix.IO.file_desc
                    | DummyLock

fun is_real (RealLock _) = true
  | is_real DummyLock = false

fun release (RealLock fd) = (Posix.IO.close fd handle OS.SysErr _ => ())
  | release DummyLock = ()

fun ensure_hol_dir dir =
    let val holdir = OS.Path.concat(dir, ".hol")
    in
      if OS.FileSys.access(holdir, []) then ()
      else OS.FileSys.mkDir holdir
           handle OS.SysErr _ => () (* may race with another process *)
    end

fun acquire {dir, warn} =
    if not Systeml.isUnix then DummyLock
    else
      let
        val _ = ensure_hol_dir dir
        val lockpath = OS.Path.concat(OS.Path.concat(dir, ".hol"),
                                      "holmake.lock")
        open Posix.FileSys
        val fd = createf (lockpath, O_WRONLY, O.flags [O.trunc],
                          S.flags [S.irusr, S.iwusr])
        open Posix.IO
        val lock = FLock.flock {
              ltype = F_WRLCK, whence = SEEK_SET,
              start = 0, len = 0, pid = NONE
            }
      in
        setlkw (fd, lock);
        (* Write our PID into the lock file for diagnostics *)
        (let val pidstr = SysWord.toString
                            (Posix.Process.pidToWord (Posix.ProcEnv.getpid()))
                          ^ "\n"
         in
           ignore (writeVec (fd,
                     Word8VectorSlice.slice(
                       Byte.stringToBytes pidstr, 0, NONE)))
         end handle _ => ());
        RealLock fd
      end
      handle OS.SysErr (msg, _) =>
             (warn ("Failed to acquire directory lock in " ^ dir ^
                    ": " ^ msg ^ " (proceeding without lock)");
              DummyLock)

end
