open testutilsBase

val reader_files = ref ([] : string list)
fun reader_temp () =
  let val base = OS.FileSys.tmpName ()
      val file = base ^ ".pft"
      val () = if OS.FileSys.access(base, []) then
                 OS.FileSys.remove base else ()
  in reader_files := file :: !reader_files; file end

fun reader_bytes file =
  let val ins = BinIO.openIn file
  in BinIO.inputAll ins before BinIO.closeIn ins end

fun reader_file bytes =
  let val file = reader_temp ()
      val out = BinIO.openOut file
  in BinIO.output(out, bytes); BinIO.closeOut out; file end

fun reader_fail f = (f (); false) handle Fail _ => true
fun reader_test name f =
  (tprint name; if f () then OK () else die "unexpected reader result")

val dispatches = ref 0
fun dispatched _ = dispatches := !dispatches + 1
val reader_fh : PFTReader.format_handler =
  {tyvar=dispatched, tyop=dispatched, var=dispatched,
   const=dispatched, comb=dispatched, abs=dispatched,
   new_const=dispatched, new_type=dispatched, axiom=dispatched,
   save=dispatched, load=dispatched, del=dispatched, del_range=dispatched}
val reader_rh : PFTReader.ruleset_handler = fn _ => dispatched

fun no_dispatch file =
  (dispatches := 0;
   reader_fail (fn () => ignore (PFTReader.read
     {file=file, binary=true,
      format_handler=reader_fh, ruleset_handler=reader_rh}))
   andalso !dispatches = 0)

val reader_valid = reader_temp ()
val reader_out = PFTWriter.openOut
  {file=reader_valid, binary=true, version=1, ruleset="hol4"}
val () = PFTWriter.new_type reader_out "pft_reader_contract$unused" 0
val () = PFTWriter.closeOut reader_out {n_ty=0, n_tm=0, n_th=0, n_ci=0}
val reader_data = reader_bytes reader_valid

fun reader_change index value = reader_file
  (Word8Vector.tabulate(Word8Vector.length reader_data,
     fn i => if i = index then value else Word8Vector.sub(reader_data,i)))

fun rejects_header file =
  reader_fail (fn () => ignore (PFTReader.read_header
    {file=file, binary=true})) andalso no_dispatch file

val () = reader_test "reader rejects bad magic before dispatch"
  (fn () => rejects_header (reader_change 0 0w88))
val () = reader_test "reader rejects version 0 before dispatch"
  (fn () => rejects_header (reader_change 4 0w0))
val () = reader_test "reader rejects version 2 before dispatch"
  (fn () => rejects_header (reader_change 4 0w2))
val () = reader_test "reader rejects unknown ruleset before dispatch"
  (fn () => rejects_header (reader_change 6 0w120))

(* String-version headers belong to a different wire format. *)
val semver_file = reader_file (Word8Vector.concat
  [Byte.stringToBytes "PFT\000\0050.0.3\004hol4",
   Word8VectorSlice.vector (Word8VectorSlice.slice(reader_data,10,NONE))])
val () = reader_test "reader rejects string versions before dispatch"
  (fn () => rejects_header semver_file)

val reader_size = Word8Vector.length reader_data
val () = reader_test "reader rejects incorrect footer length before dispatch"
  (fn () => no_dispatch (reader_change (reader_size-2) 0w4))
val three_ns_file = reader_file (Word8Vector.concat
  [Word8VectorSlice.vector
     (Word8VectorSlice.slice(reader_data,0,SOME (reader_size-3))),
   Word8Vector.fromList [0w4,0w0]])
val () = reader_test "reader rejects three-namespace footer before dispatch"
  (fn () => no_dispatch three_ns_file)

val candle_file = reader_temp ()
val candle_out = PFTWriter.openOut
  {file=candle_file, binary=true, version=1, ruleset="candle"}
val rejected_type = {Thy="pft_reader_contract", Tyop="must_not_exist"}
val () = PFTWriter.new_type candle_out
  "pft_reader_contract$must_not_exist" 0
val () = PFTWriter.closeOut candle_out {n_ty=0, n_tm=0, n_th=0, n_ci=0}
val () = reader_test "HOL4 replay rejects Candle before kernel effects"
  (fn () => Type.op_arity rejected_type = NONE andalso
    reader_fail (fn () => ignore
      (PFTReplay.replay PFTReplay.empty_trDB candle_file)) andalso
    Type.op_arity rejected_type = NONE)

val () = List.app OS.FileSys.remove (!reader_files)
