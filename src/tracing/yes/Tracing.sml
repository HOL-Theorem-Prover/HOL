structure Tracing :> Tracing =
struct
open TheoryPP

fun export (file, x: 'a) = let
  val () = PolyML.shareCommonData x
  val body = PolyML.exportSmall x
  open Posix
  val {infd = pipeRead, outfd = pipeWrite} = IO.pipe ()
  val pid = case Process.fork () of SOME pid => pid | NONE => let
    val () = IO.dup2 {old = pipeRead, new = FileSys.stdin}
    val fd = FileSys.createf (file, FileSys.O_WRONLY, FileSys.O.trunc,
      let open FileSys.S in flags [irusr, iwusr, irgrp, iwgrp, iroth] end)
    val () = IO.dup2 {old = fd, new = FileSys.stdout}
    val () = app IO.close [pipeRead, pipeWrite, fd]
    in Process.exec ("/usr/bin/gzip", []) end
  fun writeAll slice = if Word8VectorSlice.length slice = 0 then () else let
    val n = IO.writeVec (pipeWrite, slice)
    in writeAll (Word8VectorSlice.subslice (slice, n, NONE)) end
  val () = writeAll (Word8VectorSlice.full body)
  val () = app IO.close [pipeRead, pipeWrite]
  val _ = Process.waitpid (Process.W_CHILD pid, [])
  in () end

fun trace_theory name args = export(concat[".hol/objs/",name,".tr.gz"], args)

end
