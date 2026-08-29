structure HMTestPaths =
struct

(* A fresh temp directory, named as Holmake will name it.

   OS.FileSys.tmpName can hand back a path reached through a symbolic
   link -- on macOS it yields /var/tmp/MLTEMPxxxxxx, and /var is itself
   a link to /private/var.  Holmake seeds its upward walk for a project
   root with getcwd(3), which has no link components, so a test that
   compares a tmpName-derived string against Holmake's output fails on
   those platforms alone unless it canonicalises first. *)
fun mk_root () =
    let
      val nm = OS.FileSys.tmpName ()
      val _ = OS.FileSys.remove nm handle OS.SysErr _ => ()
      val _ = OS.FileSys.mkDir nm
    in
      OS.FileSys.fullPath nm
    end

end
