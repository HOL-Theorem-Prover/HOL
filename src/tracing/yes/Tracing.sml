structure Tracing :> Tracing =
struct
open TheoryPP

fun export (file, x: 'a) = let
  val () = PolyML.shareCommonData x
  open Posix
  val {infd = pipeRead, outfd = pipeWrite} = IO.pipe ()
  val pid = case Process.fork () of SOME pid => pid | NONE => let
    val () = IO.dup2 {old = pipeRead, new = FileSys.stdin}
    val fd = FileSys.createf (file, FileSys.O_WRONLY, FileSys.O.trunc,
      let open FileSys.S in flags [irusr, iwusr, irgrp, iwgrp, iroth] end)
    val () = IO.dup2 {old = fd, new = FileSys.stdout}
    val () = app IO.close [pipeRead, pipeWrite, fd]
    in Process.exec ("/usr/bin/gzip", []) end
  val fd_int = SysWord.toInt (FileSys.fdToWord pipeWrite)
  val () = PolyML.exportSmallToFD (fd_int, x)
  val () = app IO.close [pipeRead, pipeWrite]
  val _ = Process.waitpid (Process.W_CHILD pid, [])
  in () end

fun trace_theory name args = export(concat[".hol/objs/",name,".tr.gz"], args)

end
