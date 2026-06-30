structure Tracing :> Tracing =
struct
open TheoryPP

(* When true, trace_theory recodes the PolyML heap dump from 64-bit to 32-bit
   before gzipping. Produces a backward-incompatible format marked by an
   8-byte magic "TR32\0\0\0\xFF". *)
val recode_32bit = true

infix ++
fun p1 ++ p2 = OS.Path.concat (p1,p2)
val recode32_path = Systeml.HOLDIR ++ "bin" ++ "recode32"

fun export (file, x: 'a) = let
  val () = PolyML.shareCommonData x
  open Posix
  val {infd = pipeRead, outfd = pipeWrite} = IO.pipe ()
  fun gzip read fds = case Process.fork () of SOME pid => pid | NONE => let
    val () = IO.dup2 {old = read, new = FileSys.stdin}
    val fd = FileSys.createf (file, FileSys.O_WRONLY, FileSys.O.trunc,
      let open FileSys.S in flags [irusr, iwusr, irgrp, iwgrp, iroth] end)
    val () = IO.dup2 {old = fd, new = FileSys.stdout}
    val () = app IO.close (read::fd::fds)
    in Process.exec ("/usr/bin/gzip", []) end
  val pids = if recode_32bit then let
    val {infd = recRead, outfd = recWrite} = IO.pipe ()
    val gzipPid = gzip recRead [pipeRead, pipeWrite, recWrite]
    val recPid = case Process.fork () of SOME pid => pid | NONE => let
      val () = IO.dup2 {old = pipeRead, new = FileSys.stdin}
      val () = IO.dup2 {old = recWrite, new = FileSys.stdout}
      val () = app IO.close [pipeRead, pipeWrite, recRead, recWrite]
      in Process.exec (recode32_path, []) end
    val () = app IO.close [recRead, recWrite]
    in [recPid, gzipPid] end
  else [gzip pipeRead [pipeWrite]]
  val () = IO.close pipeRead
  val () = PolyML.exportSmallToFD (pipeWrite, x)
  val () = IO.close pipeWrite
in app (fn pid => ignore (Process.waitpid (Process.W_CHILD pid, []))) pids end

fun trace_theory name args = export(concat[".hol/objs/",name,".tr.gz"], args)

fun export_proof {file, tag} th =
  case !TraceMode.mode of
    TraceMode.NoTrace => ()
  | _ => let
      val prf = Thm.proof th
    in
      export (file, prf);
      Thm.set_exported th (file, tag)
    end

end
