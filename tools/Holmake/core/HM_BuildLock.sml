structure HM_BuildLock :> HM_BuildLock =
struct

datatype lockhandle = RealLock of {fd: Posix.IO.file_desc,
                                   lockpath: string,
                                   diag: string -> unit}
                    | DummyLock

val nolock = DummyLock

fun is_real (RealLock _) = true
  | is_real DummyLock = false

fun release (RealLock {fd, lockpath, diag}) =
      (diag ("releasing lock " ^ lockpath);
       Posix.IO.close fd handle OS.SysErr _ => ())
  | release DummyLock = ()

infix ++
fun p1 ++ p2 = OS.Path.concat(p1, p2)

fun sanitize_key key =
    String.translate
      (fn c => if Char.isAlphaNum c orelse c = #"_" orelse c = #"."
                  orelse c = #"-"
               then str c
               else "_")
      key

fun acquire {dir, key, warn, diag} =
  let
    fun no_lock e =
      (warn ("Failed to acquire build lock for " ^ key ^ " in " ^
             dir ^ ": " ^ General.exnMessage e ^
             " (proceeding without lock)");
       DummyLock)
  in
    if not Systeml.isUnix then DummyLock
    else
      let
        val lockdir = HFS_NameMunge.lockdir_for dir
        val _ = HOLFS_dtype.createDirIfNecessary lockdir
        val lockpath = lockdir ++ (sanitize_key key ^ ".lock")
        val _ = diag ("blocking on lock " ^ lockpath)
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
        diag ("acquired lock " ^ lockpath);
        (* Write our PID into the lock file for diagnostics *)
        (let val pidstr = SysWord.toString
                            (Posix.Process.pidToWord (Posix.ProcEnv.getpid()))
                          ^ "\n"
         in
           ignore (writeVec (fd,
                     Word8VectorSlice.slice(
                       Byte.stringToBytes pidstr, 0, NONE)))
         end handle _ => ());
        RealLock {fd = fd, lockpath = lockpath, diag = diag}
      end
      handle e as OS.SysErr _ => no_lock e
           | e as Fail _ => no_lock e
  end

end
