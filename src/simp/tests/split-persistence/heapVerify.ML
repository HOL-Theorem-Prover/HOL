open HolKernel testutils splitLib;

fun check label ok = (tprint label; if ok then OK () else die label);
fun free () = not (ThmAttribute.is_attribute "split") andalso
  not (List.exists (equal "split") (ThmSetData.all_set_types ()));
fun empty () = null (split_thms ()) andalso null (named_split_thms ());
val warnings = ref ([] : string list);
val old_warning = !Feedback.WARNING_outstream;
val _ = Feedback.WARNING_outstream :=
  (fn s => (warnings := s :: !warnings; old_warning s));
val _ = check "heap reload restores named descendant rules"
  (map #1 (named_split_thms ()) = SplitHeapState.names);
val _ = check "heap reload keeps the direct attribute and no generic set"
  (ThmAttribute.is_attribute "split" andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())));
val _ = List.app (fn (key,th) =>
  case String.fields (equal #"$") key of
      [thy,name] => check ("heap DB theorem identity: " ^ key)
        (Portable.pointer_eq (th,DB.fetch thy name))
    | _ => die "bad key") (named_split_thms ());
val owned = Context.snapshot ();
val _ = enable_split_attribute ();
val _ = check "heap opt-in remains idempotent"
  (Portable.pointer_eq (owned,Context.snapshot ()));
val _ = exclude_split "splitChild.drop";
val _ = check "heap removal handle is live"
  (map #1 (named_split_thms ()) = ["splitParent$keep"]);
val _ = Context.restore SplitHeapState.before_init;
val _ = check "heap restore before initialization discards registration"
  (free () andalso empty ());
(* splitPersistLib is already in the process module table. Its body need
   not run again: the explicit API, not a second Meta.load, must reenable. *)
val _ = Meta.load "splitPersistLib";
val _ = check "cached opt-in module does not silently reclaim namespace"
  (free () andalso empty ());
val _ = enable_split_attribute ();
val _ = check "heap can explicitly initialize after rewind" (empty ());
val _ = Context.restore SplitHeapState.foreign;
val foreign = Context.snapshot ();
val result = (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e;
val _ = check "heap foreign conflict is before any Context mutation"
  (Portable.pointer_eq (foreign,Context.snapshot ()) andalso
   (case result of SOME e =>
      Feedback.top_structure_of e = "splitLib" andalso
      Feedback.top_function_of e = "enable_split_attribute" andalso
      Feedback.message_of e = "settype or attribute split already exists"
    | NONE => false));
val _ = check "heap foreign restore keeps an attribute and empty queries"
  (empty () andalso ThmAttribute.is_attribute "split");
val _ = ThmAttribute.local_attribute
  {name="foreign",attrname="split",args=[],thm=boolTheory.TRUTH};
val _ = check "heap foreign handler remains callable"
  (!(SplitHeapState.calls) = 1);
val _ = Context.restore SplitHeapState.owned;
(* A local attribute can override an imported key only when that theory
   is current; here replay instead demonstrates ordered REMOVE application
   by replaying the parent first, restoring its removed child-facing key. *)
val _ = check "heap parent replay restores ancestor key temporarily"
  (null (Listener.call_listener Theory.delta_hook
    (TheoryDelta.TheoryLoaded "splitParent")) andalso
   List.exists (fn (key,_) => key = "splitParent$drop") (named_split_thms ()));
val _ = check "heap TheoryLoaded routing has no stale witnesses"
  (null (Listener.call_listener Theory.delta_hook
    (TheoryDelta.TheoryLoaded "splitChild")));
val _ = check "heap restored dispatcher replays ADDs and REMOVEs"
  (map #1 (named_split_thms ()) = SplitHeapState.names);
val _ = check "heap lifecycle has no replacement warnings" (null (!warnings));
val _ = Feedback.WARNING_outstream := old_warning;
val _ = print "OBS heap=reloaded\nOBS result=pass\n";
