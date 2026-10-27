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

val files = ref ([] : string list)
fun temp () =
  let val file = OS.FileSys.tmpName ()
  in files := file :: !files; file end

fun cleanup () = List.app OS.FileSys.remove (!files)

fun finish out = PFTWriter.closeOut out
  {n_ty=4, n_tm=4, n_th=16, n_ci=4}

fun output ruleset =
  let val file = temp ()
      val out = PFTWriter.openOut
        {file=file, binary=true, version=1, ruleset=ruleset}
  in (file, out) end

fun run_test name f =
  (tprint name; if f () then OK () else die "unexpected result")

fun fails f = (f (); false) handle Fail _ => true

(* Both implicit results must be retained when the second is referenced.
   Anonymous exports are ordinary names for cross-file resolution. *)
val (types_file, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.Candle.new_type_definition out 1 0
  "test_type" "test_abs" "test_rep"
val () = PFTWriter.save out "types$FIRST" 1
val () = PFTWriter.save out "types#0" 2
val () = finish out
val (uses_file, out) = output "candle"
val () = PFTWriter.load out 0 "types$FIRST"
val () = PFTWriter.load out 1 "types#0"
val () = PFTWriter.Candle.trans out 2 0 1
val () = PFTWriter.save out "uses$RESULT" 2
val () = finish out
val merged = temp ()
val () = PFTMerge.merge
  {inputs=[types_file, uses_file],
   targets=[PFTMerge.ThyThm("uses", "RESULT", false)],
   output=merged, binary=true}

val produced = ref ([] : int list)
val consumed = ref ([] : int list)
val loads = ref 0
val saves = ref ([] : string list)
val fh : PFTReader.format_handler =
  {tyvar=fn _ => (), tyop=fn _ => (), var=fn _ => (),
   const=fn _ => (), comb=fn _ => (), abs=fn _ => (),
   new_const=fn _ => (), new_type=fn _ => (), axiom=fn _ => (),
   save=fn (name,_) => saves := name :: !saves,
   load=fn _ => loads := !loads + 1,
   del=fn _ => (), del_range=fn _ => ()}
val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
  let val desc = PFTOpcodes.lookup_desc PFTOpcodes.candle_descs opc
      val id = #readVarint sr ()
      val args = PFTReader.read_raw_args desc sr
  in if opc = 0x31 then produced := [id, id+1]
     else if opc = 0x11 then
       consumed := map (fn PFTOpcodes.VId n => n
                         | _ => raise Fail "unexpected TRANS argument") args
     else ()
  end
val _ = PFTReader.read {file=merged, binary=true,
                        format_handler=fh, ruleset_handler=rh}
val () = run_test "merge preserves both Candle type-definition results"
  (fn () => length (!produced) = 2 andalso !produced = !consumed)
val () = run_test "merge resolves named and anonymous LOADs"
  (fn () => !loads = 0 andalso !saves = ["uses$RESULT"])

val (wrong_ruleset, out) = output "hol4"
val () = finish out
val unchanged = temp ()
val () = let val out = TextIO.openOut unchanged
         in TextIO.output(out, "unchanged"); TextIO.closeOut out end
fun unchanged_output () =
  let val ins = TextIO.openIn unchanged
  in TextIO.inputAll ins = "unchanged" before TextIO.closeIn ins end
fun reject inputs =
  fails (fn () => PFTMerge.merge
    {inputs=inputs, targets=[PFTMerge.ThyThm("uses", "RESULT", false)],
     output=unchanged, binary=true}) andalso unchanged_output ()
val () = run_test "merge rejects mixed rulesets before opening output"
  (fn () => reject [types_file, wrong_ruleset])
val () = run_test "merge rejects incorrect dependency order before output"
  (fn () => reject [uses_file, types_file])

val bad_version = temp ()
val () = let
  val ins = BinIO.openIn types_file
  val bytes = BinIO.inputAll ins before BinIO.closeIn ins
  val bytes = Word8Vector.tabulate(Word8Vector.length bytes,
    fn i => if i = 4 then 0w2 else Word8Vector.sub(bytes, i))
  val out = BinIO.openOut bad_version
  in BinIO.output(out, bytes); BinIO.closeOut out end
val () = run_test "merge rejects unsupported version before opening output"
  (fn () => reject [bad_version])

val (reused_file, out) = output "hol4"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.del out "ty" 0
val () = PFTWriter.tyvar out 0 "'b"
val () = finish out
val () = run_test "merge explicitly rejects reused input IDs"
  (fn () => reject [reused_file])

fun compute_file thy =
  let val (file, out) = output "candle"
  in PFTWriter.tyvar out 0 "'a";
     PFTWriter.var out 0 "p" 0;
     PFTWriter.Candle.assume out 0 0;
     PFTWriter.Candle.compute_init out 0 [0];
     PFTWriter.Candle.compute out 1 0 0 [];
     PFTWriter.save out (thy ^ "$COMPUTED") 1;
     finish out;
     file
  end
val compute_a = compute_file "compute_a"
val compute_b = compute_file "compute_b"
val compute_merged = temp ()
val () = PFTMerge.merge
  {inputs=[compute_a, compute_b],
   targets=[PFTMerge.ThyAll("compute_a", false),
            PFTMerge.ThyAll("compute_b", false)],
   output=compute_merged, binary=true}
val init_ids = ref ([] : int list)
val compute_ids = ref ([] : int list)
val compute_rh : PFTReader.ruleset_handler = fn opc => fn sr =>
  let val desc = PFTOpcodes.lookup_desc PFTOpcodes.candle_descs opc
      val id = #readVarint sr ()
      val args = PFTReader.read_raw_args desc sr
  in if opc = 0x40 then init_ids := id :: !init_ids
     else if opc = 0x41 then
       (case args of PFTOpcodes.VId ci :: _ =>
          compute_ids := ci :: !compute_ids
        | _ => raise Fail "unexpected COMPUTE argument")
     else ()
  end
val compute_limits = PFTReader.read
  {file=compute_merged, binary=true,
   format_handler=fh, ruleset_handler=compute_rh}
val () = run_test "merge preserves distinct explicit compute contexts"
  (fn () => !init_ids = [1,0] andalso !compute_ids = !init_ids andalso
            #n_ci compute_limits = 2)

val (unused_file, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "unused" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.save out "unused$RESULT" 0
val () = finish out
val with_unused = temp ()
val () = PFTMerge.merge
  {inputs=[unused_file, types_file, uses_file],
   targets=[PFTMerge.ThyThm("uses", "RESULT", false)],
   output=with_unused, binary=true}
val () = run_test "merge ignores unrelated exports without changing output"
  (fn () => reader_bytes with_unused = reader_bytes merged)

fun reject_unused prefix file =
  ((PFTMerge.merge
      {inputs=[types_file, uses_file, file],
       targets=[PFTMerge.ThyThm("uses", "RESULT", false)],
       output=unchanged, binary=true}; false)
   handle Fail message => String.isPrefix prefix message)
  andalso unchanged_output ()

val (missing_file, out) = output "candle"
val () = PFTWriter.var out 0 "missing" 3
val () = finish out
val () = run_test "merge rejects missing IDs in unselected files"
  (fn () => reject_unused "PFTMerge: missing or forward reference" missing_file)

val (forward_file, out) = output "candle"
val () = PFTWriter.var out 0 "forward" 1
val () = PFTWriter.tyvar out 1 "'a"
val () = finish out
val () = run_test "merge rejects forward IDs in unselected files"
  (fn () => reject_unused "PFTMerge: missing or forward reference" forward_file)

val (unused_reuse, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.del out "ty" 0
val () = PFTWriter.tyvar out 0 "'b"
val () = finish out
val () = run_test "merge rejects reused IDs after DEL in unselected files"
  (fn () => reject_unused "PFTMerge: reused input ID" unused_reuse)

val (unused_save, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "duplicate" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.save out "uses$RESULT" 0
val () = finish out
val () = run_test "merge rejects duplicate SAVEs in unselected files"
  (fn () => reject_unused "PFTMerge: duplicate SAVE" unused_save)

val (unused_implicit, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "witness" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.Candle.new_type_definition out 1 0
  "unused_type" "unused_abs" "unused_rep"
val () = PFTWriter.Candle.assume out 2 0
val () = finish out
val () = run_test "merge validates both implicit results in unselected files"
  (fn () => reject_unused "PFTMerge: reused input ID th#2" unused_implicit)

val (unused_compute, out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "compute" 0
val () = PFTWriter.Candle.compute out 0 1 0 []
val () = PFTWriter.Candle.compute_init out 1 []
val () = finish out
val () = run_test
  "merge validates compute context references in unselected files"
  (fn () => reject_unused "PFTMerge: missing or forward reference to ci#1"
                         unused_compute)

val () = cleanup ()
