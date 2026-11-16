(* Characterize the ordinary ancestry replay used before SplitData.
   Synthetic theory nodes isolate graph ordering from file import ordering. *)
open HolKernel testutils
fun check label ok = (tprint label; if ok then OK () else die label)
fun node name parents = Theory.link_parents (name, "replay-test")
  (map (fn n => (n, Theory.hash n)) parents)
val _ = node "replayBase" ["min"]
val _ = node "replayLeft" ["replayBase"]
val _ = node "replayRight" ["replayBase"]
val _ = node "replayDiamond" ["replayLeft", "replayRight"]
val _ = Theory.new_theory "replayOrder"
val trace = ref ([] : string list)
fun apply s xs = xs @ [s]
val events =
  [("replayBase", ["add base", "add alias"]),
   ("replayLeft", ["remove base", "add left"]),
   ("replayRight", ["add base", "remove alias"]),
   ("replayDiamond", ["remove left", "add diamond"])]
val data = AncestryData.fullmake
  {adinfo={tag="replay.characterization", initial_values=[("min", [])],
           apply_delta=apply},
   sexps={enc=ThyDataSexp.String, dec=ThyDataSexp.string_decode},
   globinfo={initial_value=[], thy_finaliser=NONE,
             apply_to_global=fn s => fn xs => (trace := !trace @ [s]; apply s xs)},
   uptodate_delta=K true}
val maps = {strings=fn _ => "", terms=fn _ => boolSyntax.T}
val _ = List.app (fn (thy,ds) => Theory.LoadableThyData.temp_encoded_update
  {thy=thy, thydataty="replay.characterization.deltas", shared_readmaps=maps,
   data=HOLsexp.list_encode HOLsexp.String ds}) events
fun load thy = check ("TheoryLoaded " ^ thy)
  (null (Listener.call_listener Theory.delta_hook (TheoryDelta.TheoryLoaded thy)))
val _ = List.app load ["replayBase","replayLeft","replayRight","replayDiamond"]
val _ = check "ordered events preserve duplicate aliases and sibling removals"
  (#get_global_value data () = List.concat (map #2 events))
val _ = load "replayRight"
val _ = check "repeated TheoryLoaded reapplies that theory's ordered events"
  (#get_global_value data () = List.concat (map #2 events) @ #2 (List.nth (events,2)))
val _ = print ("OBS initialization order=" ^ String.concatWith ","
  (let val g = SymGraph.make (map (fn s => ((s,()),Theory.parents s))
                                (Theory.ancestry "-"))
   in List.filter (String.isPrefix "replay")
                  (List.rev (SymGraph.topological_order g)) end) ^ "\n")
(* Allocation after imports uses the topological order above, rather than
   the order in which unrelated siblings happened to be loaded. *)
val _ = List.app (fn (thy,ds) => Theory.LoadableThyData.temp_encoded_update
  {thy=thy, thydataty="replay.initialization.deltas", shared_readmaps=maps,
   data=HOLsexp.list_encode HOLsexp.String ds}) events
val initialized = AncestryData.fullmake
  {adinfo={tag="replay.initialization", initial_values=[("min", [])],
           apply_delta=apply},
   sexps={enc=ThyDataSexp.String, dec=ThyDataSexp.string_decode},
   globinfo={initial_value=[], thy_finaliser=NONE, apply_to_global=apply},
   uptodate_delta=K true}
val _ = check "initialization visits diamond base once in characterized sibling order"
  (#get_global_value initialized () =
   List.concat (map (fn i => #2 (List.nth (events,i))) [0,2,1,3]))

(* Run the same diamond through private split persistence, with equal
   theorems under different aliases. A union of final sibling sets would
   incorrectly retain base, which the left sibling removes after right. *)
val thy = Theory.current_theory ()
val rule = splitLib.type_split_of bool
val _ = List.app (fn n => ignore (Theory.save_thm (n,rule)))
  ["base","alias","left","diamond"]
fun add n = HOLsexp.List [HOLsexp.Symbol "add",HOLsexp.String thy,HOLsexp.String n]
fun remove n = HOLsexp.List [HOLsexp.Symbol "remove",HOLsexp.String (thy ^ "$" ^ n)]
val private_events =
  [("replayBase",[add "base",add "alias"]),
   ("replayLeft",[remove "base",add "left"]),
   ("replayRight",[add "base",remove "alias"]),
   ("replayDiamond",[remove "left",add "diamond"])]
val _ = List.app (fn (thy,ds) => Theory.LoadableThyData.temp_encoded_update
  {thy=thy,thydataty="splitLib.persistent.rules.v1",shared_readmaps=maps,
   data=HOLsexp.tagged_encode "split-rules-v1" HOLsexp.List ds}) private_events
val _ = splitLib.enable_split_attribute ()
fun names () = map #1 (splitLib.named_split_thms ())
val _ = check "private initialization matches characterized ordered diamond replay"
  (names () = [thy ^ "$diamond"])
val _ = load "replayRight"
val _ = load "replayRight"
val _ = check "repeated private loads reapply ordered events without duplicate keys"
  (names () = map (fn n => thy ^ "$" ^ n) ["base","diamond"])
val _ = load "replayBase"
val _ = check "equal-theorem aliases retain distinct names"
  (names () = map (fn n => thy ^ "$" ^ n) ["alias","base","diamond"])
val _ = check "raw REMOVE keys retain their writing theory"
  (SplitData.theory_data "replayRight" =
    [SplitData.Add {Thy=thy,Name="base"},SplitData.Remove (thy ^ "$alias")])
val _ = OS.Process.exit OS.Process.success
