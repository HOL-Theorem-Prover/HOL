(* Saved snapshots include three different registry owners. All bindings
   are in the saved global namespace for the separate reload verifier. *)

structure SplitHeapState =
struct
  val before_init = initial_context
  val owned = Context.snapshot ()
  val names = map #1 (splitLib.named_split_thms ())
  val calls = ref 0
  val foreign_handlers =
    {localf=fn _ => calls := !calls + 1,
     storedf=fn _ => calls := !calls + 1}
  val _ = Context.restore before_init
  val _ = ThmAttribute.register_attribute ("split",foreign_handlers)
  val foreign = Context.snapshot ()
  val _ = Context.restore owned
end;
val _ = check "heap saves descendant rules and initialized registries"
  (SplitHeapState.names = ["splitChild$drop","splitParent$keep"]);
val _ = PolyML.SaveState.saveState (fixture "split-lifecycle.state");
val _ = print "OBS heap=saved\n";
