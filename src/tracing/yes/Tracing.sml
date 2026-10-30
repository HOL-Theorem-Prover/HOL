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
    in Process.exec ("/usr/bin/gzip", ["gzip"]) end
  val pids = if recode_32bit then let
    val {infd = recRead, outfd = recWrite} = IO.pipe ()
    val gzipPid = gzip recRead [pipeRead, pipeWrite, recWrite]
    val recPid = case Process.fork () of SOME pid => pid | NONE => let
      val () = IO.dup2 {old = pipeRead, new = FileSys.stdin}
      val () = IO.dup2 {old = recWrite, new = FileSys.stdout}
      val () = app IO.close [pipeRead, pipeWrite, recRead, recWrite]
      in Process.exec (recode32_path, ["recode32"]) end
    val () = app IO.close [recRead, recWrite]
    in [recPid, gzipPid] end
  else [gzip pipeRead [pipeWrite]]
  val () = IO.close pipeRead
  val () = PolyML.exportSmallToFD (pipeWrite, x)
  val () = IO.close pipeWrite
in app (fn pid => ignore (Process.waitpid (Process.W_CHILD pid, []))) pids end

fun signature_ids ctxt = let
  val types = Context.typesig ctxt
  fun current_type (Type_dtype.Tyv _) = true
    | current_type (Type_dtype.Tyapp ((id,_), args)) =
        KernelSig.uptodate_id types id andalso List.all current_type args
  val const_ids = KernelSig.foldl (fn (_, (id, ty), ids) =>
    if current_type (Type_dtype.to_hol_type ty) then id :: ids else ids)
    [] (Context.termsig ctxt)
  val type_ids = KernelSig.foldl (fn (_, (id, _), ids) => id :: ids)
    [] types
in (const_ids, type_ids) end

val const_origins = ref (Redblackmap.mkDict KernelSig.id_compare)
val type_origins = ref (Redblackmap.mkDict KernelSig.id_compare)

fun record_signature {theory, hash} = let
  val (const_ids, type_ids) = signature_ids (Context.snapshot ())
  (* The first successful export/import owns this identity, even after a
     restore. A same-named declaration with another epoch is a different key. *)
  fun record origins id =
    if #Thy (KernelSig.name_of_id id) <> theory orelse
       Redblackmap.inDomain (!origins, id) then ()
    else origins := Redblackmap.insert (!origins, id, (theory, hash))
in
  List.app (record const_origins) const_ids;
  List.app (record type_origins) type_ids
end

fun trace_theory name args = let
  val (const_ids, type_ids) = signature_ids (Context.snapshot ())
in
  export (concat[".hol/objs/",name,".tr.gz"],
          (1, const_ids, type_ids,
           Redblackmap.listItems (!const_origins),
           Redblackmap.listItems (!type_origins), args))
end

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
