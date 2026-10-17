open testutils

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

val () = cleanup ()
