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
val () = run_test "merge reuses sequential explicit compute contexts"
  (fn () => !init_ids = [0,0] andalso !compute_ids = !init_ids andalso
            #n_ci compute_limits = 1)

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

(* Every reference in merged output must name a live slot. A write over a
   live object or a second DEL is as invalid as a read after DEL. *)
fun monitor file =
  let
    fun compare ((ns, id), (ns', id')) =
      case String.compare(ns, ns') of
        EQUAL => Int.compare(id, id') | ord => ord
    val live = ref (Redblackmap.mkDict compare)
    val seen = ref (Redblackmap.mkDict compare)
    val dels = ref 0
    val reuses = ref 0
    fun read ns id =
      if isSome (Redblackmap.peek(!live, (ns, id))) then ()
      else raise Fail ("read dead " ^ ns ^ "#" ^ Int.toString id)
    fun write ns id =
      if isSome (Redblackmap.peek(!live, (ns, id))) then
        raise Fail ("overwrite live " ^ ns ^ "#" ^ Int.toString id)
      else (if isSome (Redblackmap.peek(!seen, (ns, id))) then
              reuses := !reuses + 1 else ();
            seen := Redblackmap.insert(!seen, (ns, id), ());
            live := Redblackmap.insert(!live, (ns, id), ()))
    fun del (ns, id) =
      (read ns id; live := #1 (Redblackmap.remove(!live, (ns, id)));
       dels := !dels + 1)
    val fh : PFTReader.format_handler =
      {tyvar=fn (id,_) => write "ty" id,
       tyop=fn (id,_,args) =>
         (List.app (read "ty") args; write "ty" id),
       var=fn (id,_,ty) => (read "ty" ty; write "tm" id),
       const=fn (id,_,ty) => (read "ty" ty; write "tm" id),
       comb=fn (id,a,b) =>
         (read "tm" a; read "tm" b; write "tm" id),
       abs=fn (id,a,b) =>
         (read "tm" a; read "tm" b; write "tm" id),
       new_const=fn (_,ty) => read "ty" ty,
       new_type=fn _ => (),
       axiom=fn (id,tm,_) => (read "tm" tm; write "th" id),
       save=fn (_,id) => read "th" id,
       load=fn _ => raise Fail "LOAD in merged output",
       del=del,
       del_range=fn _ => raise Fail "source DEL_RANGE in merged output"}
    val {ruleset,...} = PFTReader.read_header {file=file,binary=true}
    val descs = PFTOpcodes.descs_for_ruleset ruleset
    fun arg ({shape,...}: PFTOpcodes.arg_spec, value) =
      let open PFTOpcodes
      in case (shape,value) of
           (AId ns,VId id) => read ns id
         | (AIdList ns,VIdList ids) => List.app (read ns) ids
         | (AIdPairs (ns,ns'),VIdPairs ids) =>
             List.app (fn (a,b) => (read ns a; read ns' b)) ids
         | (AStrIdPairs ns,VStrIdPairs ids) =>
             List.app (fn (_,id) => read ns id) ids
         | _ => ()
      end
    val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
      let val desc = PFTOpcodes.lookup_desc descs opc
          val id = #readVarint sr ()
          val args = PFTReader.read_raw_args desc sr
      in ListPair.app arg (#args desc, args);
         ignore (List.foldl (fn (ns,i) => (write ns (id+i); i+1))
                   0 (#results desc))
      end
    val limits = PFTReader.read
      {file=file,binary=true,format_handler=fh,ruleset_handler=rh}
  in if Redblackmap.isEmpty (!live) then
       {limits=limits, dels= !dels, reuses= !reuses}
     else raise Fail "merged slots still live after tail SAVEs"
  end

val () = run_test "merge releases all four namespaces after final uses"
  (fn () => let val {limits,reuses,...} = monitor compute_merged
            in #n_ty limits = 1 andalso #n_tm limits = 1 andalso
               #n_ci limits = 1 andalso reuses > 0 andalso
               #dels (monitor merged) > 0
            end)

val (concurrent_compute,out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.Candle.compute_init out 0 [0]
val () = PFTWriter.Candle.compute_init out 1 [0]
val () = PFTWriter.Candle.compute out 1 0 0 []
val () = PFTWriter.Candle.compute out 2 1 0 []
val () = PFTWriter.save out "concurrent$FIRST" 1
val () = PFTWriter.save out "concurrent$SECOND" 2
val () = finish out
val concurrent_merged = temp ()
val () = PFTMerge.merge
  {inputs=[concurrent_compute],targets=[PFTMerge.ThyAll("concurrent",false)],
   output=concurrent_merged,binary=true}
val () = init_ids := []
val () = compute_ids := []
val _ = PFTReader.read {file=concurrent_merged,binary=true,
  format_handler=fh,ruleset_handler=compute_rh}
val () = run_test "merge keeps concurrently live compute contexts distinct"
  (fn () => !init_ids = [1,0] andalso !compute_ids = !init_ids andalso
            #n_ci (#limits (monitor concurrent_merged)) = 2)

fun replay_temp () =
  let val base = OS.FileSys.tmpName ()
      val file = base ^ ".pft"
      val () = if OS.FileSys.access(base, []) then
                 OS.FileSys.remove base else ()
  in files := file :: !files; file end
fun replay_output () =
  let val file = replay_temp ()
  in (file, PFTWriter.openOut
       {file=file,binary=true,version=1,ruleset="hol4"})
  end
fun exact_export left right key =
  case (PFTReplay.lookup left key, PFTReplay.lookup right key) of
    (SOME a, SOME b) =>
      Term.aconv (Thm.concl a) (Thm.concl b) andalso
      ListPair.allEq (fn (x,y) => Term.aconv x y) (Thm.hyp a, Thm.hyp b)
  | _ => false
fun replay_files inputs =
  List.foldl (fn (file, db) => PFTReplay.replay db file)
             PFTReplay.empty_trDB inputs

fun chain n =
  let val (file, out) = replay_output ()
      val () = PFTWriter.tyvar out 0 "'a"
      val () = PFTWriter.var out 0 "x" 0
      val () = PFTWriter.HOL4.refl out 0 0
      fun go i = if i > n then () else
        (PFTWriter.HOL4.sym out i (i-1); go (i+1))
      val () = go 1
      val () = PFTWriter.save out "chain$RESULT" n
      val () = PFTWriter.closeOut out
        {n_ty=1,n_tm=1,n_th=n+1,n_ci=0}
      val merged = replay_temp ()
      val () = PFTMerge.merge
        {inputs=[file],targets=[PFTMerge.ThyAll("chain",false)],
         output=merged,binary=true}
      val {limits,dels,reuses} = monitor merged
  in #n_th limits = 2 andalso dels = n+3 andalso reuses = n-1 andalso
     exact_export (replay_files [file]) (replay_files [merged])
                  "chain$RESULT"
  end
val () = run_test "merge theorem highwater plateaus along retained chains"
  (fn () => chain 8 andalso chain 128)

val (alias_a, out) = replay_output ()
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "x" 0
val () = PFTWriter.HOL4.refl out 0 0
val () = PFTWriter.save out "alias_a$SOURCE" 0
val () = finish out
val (alias_b, out) = replay_output ()
val () = PFTWriter.load out 0 "alias_a$SOURCE"
val () = PFTWriter.load out 1 "alias_a$SOURCE"
val () = PFTWriter.HOL4.trans out 2 0 0
val () = PFTWriter.HOL4.sym out 3 2
val () = PFTWriter.HOL4.trans out 4 1 3
val () = PFTWriter.HOL4.trans out 5 0 4
val () = PFTWriter.HOL4.trans out 6 1 5
val () = PFTWriter.save out "alias_b$RESULT" 6
val () = finish out
val (alias_c, out) = replay_output ()
val () = PFTWriter.load out 0 "alias_b$RESULT"
val () = PFTWriter.save out "alias_c$RESULT" 0
val () = finish out
val (alias_d, out) = replay_output ()
val () = PFTWriter.load out 0 "alias_c$RESULT"
val () = PFTWriter.HOL4.sym out 1 0
val () = PFTWriter.save out "alias_d$RESULT" 1
val () = finish out
val alias_inputs = [alias_a,alias_b,alias_c,alias_d]
val alias_db = replay_files alias_inputs
fun alias_merge pin =
  let val merged = replay_temp ()
      val targets = PFTMerge.ThyAll("alias_d",false) ::
        (if pin then [PFTMerge.ThyAll("alias_a",false)] else [])
      val () = PFTMerge.merge
        {inputs=alias_inputs,targets=targets,output=merged,binary=true}
      val {reuses,...} = monitor merged
      val db = replay_files [merged]
  in reuses > 0 andalso exact_export alias_db db "alias_d$RESULT" andalso
     (not pin orelse exact_export alias_db db "alias_a$SOURCE")
  end
val () = run_test "merge aliases share lifetime across repeated uses and files"
  (fn () => alias_merge false andalso alias_merge true)

val (deduct_file,out) = replay_output ()
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.var out 1 "q" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.HOL4.assume out 1 1
val () = PFTWriter.save out "deduct$EARLIER" 0
val () = PFTWriter.HOL4.deductAntisym out 2 0 1
val () = PFTWriter.save out "deduct$UNSUPPORTED" 2
val () = finish out
val () = run_test "HOL4 replay explicitly rejects unsupported deductAntisym"
  (fn () =>
    let val rejected =
          ((ignore (PFTReplay.replay alias_db deduct_file); false)
           handle Fail message =>
             message = "PFTReplay: deductAntisym unsupported")
    in rejected andalso
       exact_export alias_db (replay_files alias_inputs) "alias_d$RESULT" andalso
       not (isSome (PFTReplay.lookup alias_db "deduct$EARLIER")) andalso
       not (isSome (PFTReplay.lookup alias_db "deduct$UNSUPPORTED"))
    end)

(* Descriptor-only fixture: alternating first/second retained results leaves
   unused siblings to DEL. Real definition witnesses are checked in replay. *)
fun implicit_chain save_defs =
  let val (file,out) = output "candle"
      val () = PFTWriter.tyvar out 0 "'a"
      val () = PFTWriter.var out 0 "witness" 0
      val () = PFTWriter.Candle.assume out 0 0
      fun go i = if i = 8 then () else
        let val base = 1 + 2*i
            val witness = if i = 0 then 0
                          else 1 + 2*(i-1) + ((i-1) mod 2)
        in PFTWriter.Candle.new_type_definition out base witness
             ("reuse_type" ^ Int.toString i)
             ("reuse_abs" ^ Int.toString i)
             ("reuse_rep" ^ Int.toString i);
           go (i+1)
        end
      val () = go 0
      val () = PFTWriter.save out "implicit$RESULT" 16
      val () = PFTWriter.closeOut out
        {n_ty=1,n_tm=1,n_th=17,n_ci=0}
      val merged = temp ()
      val () = PFTMerge.merge
        {inputs=[file],targets=[PFTMerge.ThyAll("implicit",save_defs)],
         output=merged,binary=true}
      val {limits,reuses,...} = monitor merged
      val exported = ref ([] : string list)
      val fh : PFTReader.format_handler =
        {tyvar=fn _ => (),tyop=fn _ => (),var=fn _ => (),
         const=fn _ => (),comb=fn _ => (),abs=fn _ => (),
         new_const=fn _ => (),new_type=fn _ => (),axiom=fn _ => (),
         save=fn (name,_) => exported := name :: !exported,
         load=fn _ => (),del=fn _ => (),del_range=fn _ => ()}
      val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
        (ignore (#readVarint sr ());
         ignore (PFTReader.read_raw_args
           (PFTOpcodes.lookup_desc PFTOpcodes.candle_descs opc) sr))
      val _ = PFTReader.read
        {file=merged,binary=true,format_handler=fh,ruleset_handler=rh}
  in if save_defs then
       length (!exported) = 17 andalso #n_th limits = 17 andalso
       List.all (fn name => length (List.filter (fn n => n = name)
                                                (!exported)) = 1) (!exported)
     else #n_th limits <= 5 andalso reuses > 8
  end
val () = run_test
  "merge reuses consecutive implicit results and deletes siblings"
  (fn () => implicit_chain false)
val () = run_test "merge pins definition results until their tail SAVEs"
  (fn () => implicit_chain true)

fun preserves_linked_input options =
  let val alias = temp ()
      val original = reader_bytes types_file
      val () = if OS.FileSys.access(alias, []) then
                 OS.FileSys.remove alias else ()
      val () = if OS.Process.isSuccess
           (Systeml.systeml (["ln"] @ options @ [types_file, alias]))
        then () else raise Fail "could not create input alias"
  in fails (fn () => PFTMerge.merge
       {inputs=[types_file],targets=[PFTMerge.ThyAll("types",false)],
        output=alias,binary=true}) andalso
     reader_bytes types_file = original andalso reader_bytes alias = original
  end
val () = run_test "merge preserves input aliased by an output symlink"
  (fn () => preserves_linked_input ["-s"])
val () = run_test "merge preserves input aliased by an output hard link"
  (fn () => preserves_linked_input [])

(* CONJ names its connective through the kernel cache, not a term ID. *)
val (implicit_file,out) = output "hol4"
val () = PFTWriter.tyop out 0 "min$bool" []
val () = PFTWriter.tyop out 1 "min$fun" [0,0]
val () = PFTWriter.tyop out 2 "min$fun" [0,1]
val () = PFTWriter.new_const out "bool$/\\" 2
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.HOL4.assume out 0 0
val () = PFTWriter.HOL4.conj out 1 0 0
val () = PFTWriter.save out "implicit$RESULT" 1
val () = finish out
val implicit_merged = temp ()
val () = PFTMerge.merge
  {inputs=[implicit_file],targets=[PFTMerge.ThyAll("implicit",false)],
   output=implicit_merged,binary=true}
val implicit_names = ref ([] : string list)
val implicit_fh : PFTReader.format_handler =
  {tyvar=fn _ => (),tyop=fn _ => (),var=fn _ => (),const=fn _ => (),
   comb=fn _ => (),abs=fn _ => (),new_type=fn _ => (),
   new_const=fn (name,_) => implicit_names := name :: !implicit_names,
   axiom=fn _ => (),save=fn _ => (),load=fn _ => (),del=fn _ => (),
   del_range=fn _ => ()}
val implicit_rh : PFTReader.ruleset_handler = fn opc => fn sr =>
  (ignore (#readVarint sr ());
   ignore (PFTReader.read_raw_args
     (PFTOpcodes.lookup_desc PFTOpcodes.hol4_descs opc) sr))
val _ = PFTReader.read {file=implicit_merged,binary=true,
  format_handler=implicit_fh,ruleset_handler=implicit_rh}
val () = run_test "merge retains implicitly used conjunction declaration"
  (fn () => !implicit_names = ["bool$/\\"] andalso
            #dels (monitor implicit_merged) > 0)

(* The first producer starts in sparse storage. Later dense growth covers
   its ID with a hole: lookup must still find it, and reject a duplicate. *)
fun sparse_prefix out =
  (PFTWriter.tyvar out 2048 "'a";
   List.app (fn id => PFTWriter.tyvar out id "'unused")
     (List.tabulate(1025, fn i => i));
   PFTWriter.tyvar out 2049 "'unused")
val (sparse_file,out) = output "candle"
val () = sparse_prefix out
val () = PFTWriter.var out 0 "p" 2048
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.save out "sparse$RESULT" 0
val () = PFTWriter.closeOut out {n_ty=2050,n_tm=1,n_th=1,n_ci=0}
val (dense_file,out) = output "candle"
val () = PFTWriter.tyvar out 0 "'a"
val () = PFTWriter.var out 0 "p" 0
val () = PFTWriter.Candle.assume out 0 0
val () = PFTWriter.save out "sparse$RESULT" 0
val () = finish out
fun merge_sparse file =
  let val merged = temp ()
  in PFTMerge.merge {inputs=[file],
       targets=[PFTMerge.ThyAll("sparse",false)],output=merged,binary=true};
     merged
  end
val () = run_test "merge preserves sparse producers covered by dense growth"
  (fn () => reader_bytes (merge_sparse sparse_file) =
            reader_bytes (merge_sparse dense_file))
fun reject_sparse prefix file =
  let val before_bytes = reader_bytes file
  in reject_unused prefix file andalso reader_bytes file = before_bytes end
val (sparse_duplicate,out) = output "candle"
val () = sparse_prefix out
val () = PFTWriter.tyvar out 2048 "'duplicate"
val () = PFTWriter.closeOut out {n_ty=2050,n_tm=0,n_th=0,n_ci=0}
val () = run_test "merge rejects sparse duplicates after dense growth"
  (fn () => reject_sparse "PFTMerge: reused input ID ty#2048" sparse_duplicate)

(* Full-width sparse IDs in an unselected file must not size a dense array.
   Leave room for its footer bound even on Moscow ML's narrower int type. *)
val huge_id = valOf Int.maxInt - 1
fun huge_file mode =
  let val (file,out) = output "candle"
  in (if mode = 3 then PFTWriter.var out 0 "forward" huge_id else ());
     PFTWriter.tyvar out huge_id "'huge";
     (if mode = 2 then PFTWriter.del out "ty" huge_id else ());
     (if mode = 1 orelse mode = 2 then
        PFTWriter.tyvar out huge_id "'duplicate" else ());
     PFTWriter.closeOut out {n_ty=huge_id+1,n_tm=1,n_th=0,n_ci=0};
     file
  end
val huge_unused = huge_file 0
val () = run_test "merge preserves huge sparse IDs in unselected files"
  (fn () => let val merged_huge = temp ()
                val before_bytes = reader_bytes huge_unused
                val () = PFTMerge.merge
                  {inputs=[types_file,uses_file,huge_unused],
                   targets=[PFTMerge.ThyAll("uses",false)],
                   output=merged_huge,binary=true}
            in reader_bytes merged_huge = reader_bytes merged andalso
               reader_bytes huge_unused = before_bytes
            end)
val () = run_test "merge rejects huge sparse duplicates in unselected files"
  (fn () => reject_sparse "PFTMerge: reused input ID" (huge_file 1))
val () = run_test "merge rejects huge sparse reuse after DEL in unselected files"
  (fn () => reject_sparse "PFTMerge: reused input ID" (huge_file 2))
val () = run_test "merge rejects huge sparse forward IDs in unselected files"
  (fn () => reject_sparse "PFTMerge: missing or forward reference" (huge_file 3))

val () = cleanup ()
