signature ThmSrc_tr =
sig

  (* Load a theory's theorems via proof trace replay instead of from .dat
     files. Has the same signature as TheoryReader.load_thydata: reads
     metadata (parents, types, constants, thydata) from the .dat file,
     but replays theorems from .tr.gz trace files via ProofTraceReplay
     instead of using Thm.disk_thm. *)
  val load_thydata : {thyname:string, path:string, hash:string} ->
                     (Thm.thm * DB_dtype.thminfo) Symtab.table

end
