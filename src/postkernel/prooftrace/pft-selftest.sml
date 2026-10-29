fun check name ok =
  if ok then print (name ^ ": OK\n")
  else (print (name ^ ": FAILED\n"); OS.Process.exit OS.Process.failure)

val temp = OS.FileSys.tmpName ()
val () = if OS.FileSys.access(temp, []) then OS.FileSys.remove temp else ()
val proof_file = temp ^ ".pft"
val proof_out = PFTWriter.openOut
  {file=proof_file, version="0.1.0", ruleset="hol4"}
val () = PFTWriter.tyop proof_out 0 "min$bool" []
val () = PFTWriter.var proof_out 0 "p" 0
val () = PFTWriter.HOL4.assume proof_out 0 0
val () = PFTWriter.save proof_out "writer$assumption" 0
val () = PFTWriter.closeOut proof_out {n_ty=1,n_tm=1,n_th=1}

(* COMPUTE_INIT no longer creates a fourth namespace. *)
val () = check "writer uses semver header and three namespace limits"
  (PFTReader.read_header {file=proof_file,binary=true} =
     {version="0.1.0",ruleset="hol4"} andalso
   PFTReader.read_limits {file=proof_file,binary=true} =
     {n_ty=1,n_tm=1,n_th=1})
val db = PFTReplay.replay PFTReplay.empty_trDB proof_file
val th = valOf (PFTReplay.lookup db "writer$assumption")
val p = Term.mk_var("p",Type.bool)
val () = check "written theorem replays with its hypothesis"
  (length (Thm.hyp th) = 1 andalso Term.aconv (hd (Thm.hyp th)) p
   andalso Term.aconv (Thm.concl th) p)
val old_out = BinIO.openOut proof_file
val () = BinIO.output(old_out, Byte.stringToBytes "PFT\000\001\004hol4")
val () = BinIO.closeOut old_out
val () = check "old integer-version trace is rejected"
  ((PFTReader.read_header {file=proof_file,binary=true}; false)
   handle Fail _ => true)
val () = OS.FileSys.remove proof_file

val () = OS.Process.exit OS.Process.success
