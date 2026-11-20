open HolKernel Parse boolLib simpExtLib splitLib testutils
val bool_ss = lift_simpset boolSimps.bool_ss

val _ = Theory.new_theory "split_registration"
fun check label ok = (tprint label; if ok then OK () else die label)
fun free () = not (ThmAttribute.is_attribute "split") andalso
  not (List.exists (equal "split") (ThmSetData.all_set_types ()))
fun empty () = null (split_thms ()) andalso null (named_split_thms ())
fun same th1 th2 = aconv (concl th1) (concl th2) andalso
  ListPair.allEq (fn (a,b) => aconv a b) (hyp th1,hyp th2)
fun silent f =
  let
    val old = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    fun run () =
      (Feedback.WARNING_outstream := (fn s => (warnings := s :: !warnings;
                                               old s));
       f ())
    val result = Portable.finally
      (fn () => Feedback.WARNING_outstream := old) run ()
    val _ = check "operation emits no warnings" (null (!warnings))
  in result end
fun conflict () =
  let
    val ctxt = Context.snapshot ()
    val result =
      (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
    val _ = check "conflict leaves the entire Context unchanged"
      (Portable.pointer_eq (ctxt,Context.snapshot ()))
  in
    check "explicit conflict has library error identity"
      (case result of
           SOME e =>
             Feedback.top_structure_of e = "splitLib" andalso
             Feedback.top_function_of e = "enable_split_attribute" andalso
             Feedback.message_of e =
               "settype or attribute split already exists"
         | NONE => false)
  end

fun rejected_exclusion label =
  let
    val ctxt = Context.snapshot ()
    val result = (exclude_split "rule"; NONE) handle HOL_ERR e => SOME e
  in
    check label
      (Portable.pointer_eq (ctxt,Context.snapshot ()) andalso
       (case result of
            SOME e => Feedback.top_structure_of e = "splitLib" andalso
                      Feedback.top_function_of e = "exclude_split"
          | NONE => false))
  end

val _ = check "ordinary loading installs no private listener"
  (not (List.exists (fn (name,_) => name = "splitLib.persistence.onload")
    (Listener.listeners Theory.delta_hook)))
val unrelated_calls = ref ([] : string list)
val unrelated = ThyDataSexp.new
  {thydataty="split-test.unrelated", merge=ThyDataSexp.append_merge,
   load=fn {thyname,...} => unrelated_calls := thyname :: !unrelated_calls,
   other_tds=fn _ => NONE}
val before_hooks = Listener.listeners Theory.delta_hook
fun same_hooks xs ys = ListPair.allEq
  (fn ((n,f),(m,g)) => n = m andalso Portable.pointer_eq (f,g)) (xs,ys)
val uninitialized = Context.snapshot ()
val _ = rejected_exclusion "persistent removal never implicitly opts in"
val _ = check "ordinary static loading leaves split unclaimed" (free ())
val _ = check "uninitialized queries return no rules" (empty () andalso free ())
val rule = type_split_of ``:bool``
val goal : goal = ([],``P (if b then x:'a else y):bool``)
fun changed tac =
  case VALID tac goal (Context.snapshot ()) of
      ([(asms,result)],_) =>
        null asms andalso not (aconv result (#2 goal))
    | _ => false
val _ = check "pure conversion works before initialization"
  (not (aconv (rhs (concl (SPLIT_CONV [rule] (#2 goal)))) (#2 goal)))
val _ = check "local Split works before initialization"
  (changed (SIMP_TAC bool_ss [Split rule]))
val _ = check "TypeBase split_ss works before initialization"
  (changed (SIMP_TAC (bool_ss ++ split_ss) []))
val _ = check "extended case exclusion works before initialization"
  (not (changed (SIMP_TAC (bool_ss ++ split_ss)
                  [ExclX "case:bool"])));
val local_ss = add_split rule bool_ss
val local_exclusion = ExclX ("split:" ^ split_thm_name rule)
val _ = check "extended named exclusion removes local Split before opt-in"
  (not (changed (SIMP_TAC local_ss [local_exclusion])))
val _ = check "extended named exclusion preserves TypeBase before opt-in"
  (changed (SIMP_TAC (local_ss ++ split_ss) [local_exclusion]))
val before_unmatched = Context.snapshot ()
val unmatched =
  (ignore (changed
     (SIMP_TAC (bool_ss ++ split_ss) [ExclX "split:absent"])); NONE)
  handle HOL_ERR e => SOME e
val _ = check "unmatched explicit exclusion fails without registration"
  (Portable.pointer_eq (before_unmatched,Context.snapshot ()) andalso
   (case unmatched of SOME e =>
      Feedback.top_function_of e = "process_tags" andalso
      Feedback.message_of e = "ExclX did not match split:absent"
    | NONE => false))
val _ = check "local and TypeBase use claim no namespace"
  (free () andalso empty ())

val thy = Theory.current_theory ()
val name = {Thy=thy,Name="rule"}
val stored = save_thm ("rule",rule)
val attrarg = {name="rule",attrname="split",args=[],thm=stored}
val before_failure = Context.snapshot ()
val _ = Theory.LoadableThyData.temp_encoded_update
  {thy="bool",thydataty="splitLib.persistent.rules.v1",
   shared_readmaps={strings=fn _ => "",terms=fn _ => boolSyntax.T},
   data=HOLsexp.tagged_encode "split-rules-v1" I
     (HOLsexp.List [HOLsexp.List [HOLsexp.Symbol "add",
                                 HOLsexp.String "bool",HOLsexp.String "TRUTH"]])}
val failing_entry = Context.snapshot ()
val init_error = (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
val _ = check "failed ancestor validation rolls back allocation and new listener"
  (Portable.pointer_eq (failing_entry,Context.snapshot ()) andalso free () andalso
   same_hooks before_hooks (Listener.listeners Theory.delta_hook) andalso
   (case init_error of SOME e => Feedback.top_structure_of e = "splitLib" andalso
      Feedback.top_function_of e = "analyse_rule" | NONE => false))
val _ = Context.restore before_failure
(* Malformed versions/events are rejected, including a malformed REMOVE;
   allocation failures retain the exact entry context and unrelated hooks. *)
val _ = List.app (fn payload =>
  let
    val _ = Theory.LoadableThyData.temp_encoded_update
      {thy="bool",thydataty="splitLib.persistent.rules.v1",
       shared_readmaps={strings=fn _ => "",terms=fn _ => boolSyntax.T},data=payload}
    val entry = Context.snapshot ()
    val failure = Exn.capture enable_split_attribute ()
    val _ = check "malformed private stream fails and rolls back"
      ((case failure of Exn.Exn _ => true | _ => false) andalso
       Portable.pointer_eq (entry,Context.snapshot ()) andalso free () andalso
       same_hooks before_hooks (Listener.listeners Theory.delta_hook))
  in Context.restore before_failure end)
  [HOLsexp.List [HOLsexp.Symbol "split-rules-v0",HOLsexp.Nil],
   HOLsexp.tagged_encode "split-rules-v1" I
     (HOLsexp.List [HOLsexp.List [HOLsexp.Symbol "remove",HOLsexp.Integer 1]])]
val _ = silent enable_split_attribute
val _ = check "explicit initialization claims attribute without a generic set"
  (ThmAttribute.is_attribute "split" andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())) andalso empty ())
val _ = check "initialization preserves all unrelated listener identities and order"
  (same_hooks before_hooks (List.filter
     (fn (name,_) => name <> "splitLib.persistence.onload")
     (Listener.listeners Theory.delta_hook)))
val _ = check "unrelated theory-data hook still receives loads"
  (null (Listener.call_listener Theory.delta_hook (TheoryDelta.TheoryLoaded thy))
   andalso hd (!unrelated_calls) = thy)
val _ = ThmAttribute.store_at_attribute attrarg
fun has_rule () =
  case named_split_thms () of
      [(key,th)] => key = thy ^ "$rule" andalso same th stored
    | _ => false
val _ = check "stored attribute adds named rule and persistent ADD"
  (has_rule () andalso
   (case SplitData.current_data () of
        [SplitData.Add n] => n = name
      | _ => false))
val owned = Context.snapshot ()
val _ = exclude_split "rule"
val _ = check "persistent removal resolves unqualified names at write time"
  (empty () andalso
   (case SplitData.current_data () of
        [SplitData.Add _, SplitData.Remove key] => key = thy ^ "$rule"
      | _ => false))
val _ = Context.restore owned
val _ = check "restore recovers pre-removal data and private removal handle"
  (has_rule () andalso
   length (SplitData.current_data ()) = 1)
val _ = exclude_split (thy ^ ".rule")
val _ = check "persistent removal accepts qualified names" (empty ())
val _ = Context.restore owned
val malformed_result =
  (exclude_split "too.many.parts"; NONE) handle HOL_ERR e => SOME e
val _ = check "malformed persistent removal leaves entire Context unchanged"
  (Option.isSome malformed_result andalso
   Portable.pointer_eq (owned,Context.snapshot ()))
val _ = silent enable_split_attribute
val _ = check "idempotent opt-in leaves the entire Context unchanged"
  (Portable.pointer_eq (owned,Context.snapshot ()))
val _ = check "idempotence preserves handlers and data"
  (has_rule () andalso
   length (SplitData.current_data ()) = 1)
val _ = exclude_split (thy ^ ".rule")
val _ = check "private persistent REMOVE updates queries" (empty ())
val _ = Context.restore owned
val _ = silent (fn () => ignore (save_thm ("touch_first",TRUTH)))
val _ = check "restore after opt-in recovers handle and data" (has_rule ())
val _ = Context.restore uninitialized
val _ = check "restore before opt-in discards handle and registries"
  (free () andalso empty ())
val _ = silent (fn () => ignore (save_thm ("touch_uninitialized",TRUTH)))
val _ = silent enable_split_attribute
val _ = check "can initialize again after rewind" (empty ())
val _ = save_thm ("rule",rule)
val _ = ThmAttribute.store_at_attribute attrarg
val _ = silent (fn () => ignore (save_thm ("touch_second",TRUTH)))
val _ = check "reinitialized theory-data hook uses its own witness"
  (has_rule () andalso
   length (SplitData.current_data ()) = 1)
val _ = exclude_split (thy ^ ".rule")
val before_local = SplitData.current_data ()
val _ = ThmAttribute.local_attribute
  {name="local",attrname="split",args=[],thm=rule}
val _ = check "local attribute works without recording an ADD"
  (length (split_thms ()) = 1 andalso
   SplitData.current_data () = before_local)
val _ = Context.restore owned
val _ = silent (fn () => ignore (save_thm ("touch_restored",TRUTH)))
val _ = check "restore selects original handle and theory-data witness"
  (has_rule () andalso
   length (SplitData.current_data ()) = 1)

(* Foreign attribute alone, with no theorem-set mutation on failure. *)
(* Invalid declarations never record an event or modify live rules. *)
val _ = Context.restore owned
val _ = save_thm ("bad_rule",TRUTH)
fun rejects_attribute stored args thm =
  let
    val entry = Context.snapshot ()
    val handler = if stored then ThmAttribute.store_at_attribute
                  else ThmAttribute.local_attribute
    val result = Exn.capture handler
      {name="bad_rule",attrname="split",args=args,thm=thm}
  in
    check "invalid declaration leaves exact context and stream unchanged"
      ((case result of Exn.Exn (HOL_ERR _) => true | _ => false) andalso
       Portable.pointer_eq (entry,Context.snapshot ()))
  end
val _ = rejects_attribute true [] TRUTH
val _ = rejects_attribute false [] TRUTH
val _ = rejects_attribute false ["unexpected"] rule
val _ = Context.restore owned
val _ = exclude_split "preserved_remove"
val _ = Theory.delete_binding "rule"
val _ = check "deleted binding invalidates recorded ADD but preserves REMOVE"
  (SplitData.current_data () = [SplitData.Remove (thy ^ "$preserved_remove")])
val _ = check "recorded invalidation preserves prior live rule behavior"
  (has_rule ())
val _ = Context.restore owned
(* Type and constant changes prune only recorded stale ADDs. *)
val _ = Theory.new_type ("split_retired_type",0)
val retired_type = mk_thy_type {Thy=thy,Tyop="split_retired_type",Args=[]}
val typed_rule = INST_TYPE [alpha |-> retired_type] rule
val _ = save_thm ("typed_rule",typed_rule)
val _ = ThmAttribute.store_at_attribute
  {name="typed_rule",attrname="split",args=[],thm=typed_rule}
val _ = Theory.delete_type "split_retired_type"
val _ = Theory.scrub ()
(* The theorem DB removes retired bindings at ExportTheory. As with
   AncestryData.gen_other_tds, raw ADDs are pruned after that DB update. *)
val _ = check "type retirement export hooks succeed"
  (null (Listener.call_listener Theory.delta_hook (TheoryDelta.ExportTheory thy)))
val _ = check "type retirement removes invalidated recorded ADD"
  (not (List.exists (fn SplitData.Add {Name,...} => Name = "typed_rule"
                      | _ => false) (SplitData.current_data ())))
val _ = Context.restore owned
val constant_def = new_definition ("split_retired_const_def",
  “split_retired_const b (x:'a) y = if b then x else y”)
val constant_rule = PURE_REWRITE_RULE [GSYM constant_def] rule
val _ = save_thm ("constant_rule",constant_rule)
val _ = ThmAttribute.store_at_attribute
  {name="constant_rule",attrname="split",args=[],thm=constant_rule}
val _ = Theory.delete_const "split_retired_const"
val _ = Theory.scrub ()
val _ = check "constant retirement export hooks succeed"
  (null (Listener.call_listener Theory.delta_hook (TheoryDelta.ExportTheory thy)))
val _ = check "constant retirement removes invalidated recorded ADD"
  (not (List.exists (fn SplitData.Add {Name,...} => Name = "constant_rule"
                      | _ => false) (SplitData.current_data ())))
val _ = Context.restore owned

val _ = Context.restore uninitialized
val calls = ref 0
fun foreign_attr _ = calls := !calls + 1
val foreign_handlers = {localf=foreign_attr,storedf=foreign_attr}
val _ = ThmAttribute.register_attribute ("split",foreign_handlers)
val foreign_attribute = Context.snapshot ()
val _ = rejected_exclusion "persistent removal rejects foreign attribute"
val _ = silent conflict
val _ = check "attribute conflict does not partially create a set"
  (empty () andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())))
val _ = ThmAttribute.local_attribute attrarg
val _ = check "foreign attribute behavior survives" (!calls = 1)
val _ = Context.restore owned
val _ = check "owned state still usable" (has_rule ())
val _ = Context.restore foreign_attribute
val _ = check "restore to foreign attribute never uses stale handle" (empty ())
val _ = silent conflict

(* Public exporters claim both names. Check exact foreign data/handlers. *)
val _ = Context.restore uninitialized
val _ = save_thm ("foreign",TRUTH)
val additions = ref 0
val removals = ref 0
val foreign_efns =
  {add=fn _ => additions := !additions + 1,
   remove=fn _ => removals := !removals + 1}
val foreign_set = ThmSetData.new_exporter
  {settype="split",efns=foreign_efns}
val _ = #export foreign_set "foreign"
val foreign_both = Context.snapshot ()
fun foreign_intact () =
  Portable.pointer_eq
    (foreign_efns,valOf (ThmSetData.data_exportfns {settype="split"})) andalso
  (case ThmSetData.current_data {settype="split"} of
       [ThmSetData.ADD ({Thy,Name},th)] =>
         Thy = thy andalso Name = "foreign" andalso same th TRUTH
     | _ => false)
val _ = silent conflict
val _ = check "foreign set data is neither adopted nor mutated"
  (foreign_intact () andalso empty ())
val _ = Context.restore owned
val _ = Context.restore foreign_both
val _ = check "restore to foreign set returns no library rules"
  (foreign_intact () andalso empty ())
val _ = silent conflict

val _ = #add foreign_efns {thy=thy,named_thm=(name,rule)}
val _ = #remove foreign_efns {thy=thy,remove="foreign"}
val _ = check "foreign exporter callbacks survive conflicts"
  (!additions = 2 andalso !removals = 1)
(* A foreign ancestry exporter retains generic split.deltas/parents tags.
   Private split persistence must never try to decode them. *)
val _ = Context.restore uninitialized
val foreign_ancestry = ThmSetData.export_simple_dictionary
  {settype="split",initial=[("foreign",TRUTH)]}
val _ = ThmAttribute.local_attribute
  {name="foreign_local",attrname="split",args=[],thm=TRUTH}
val foreign_ancestry_context = Context.snapshot ()
val _ = check "foreign ancestry data is not adopted"
  (empty () andalso length (#get_thms foreign_ancestry ()) = 2)
val _ = silent conflict
val _ = Context.restore owned
val _ = ThmAttribute.local_attribute
  {name="rule",attrname="split",args=[],thm=mk_asm_split rule}
val _ = check "local override changes live rule without recording removal"
  (not (has_rule ()))
fun replay () =
  check "TheoryLoaded dispatch has no stale-witness exceptions"
    (null (Listener.call_listener Theory.delta_hook
             (TheoryDelta.TheoryLoaded thy)))
val _ = silent replay
val _ = check "restored library hook replays its own ADD" (has_rule ())
val _ = Context.restore foreign_ancestry_context
val _ = silent (fn () => ignore (save_thm ("touch_foreign",TRUTH)))
val _ = silent replay
val _ = check "restored foreign ancestry hook keeps foreign data"
  (empty () andalso length (#get_thms foreign_ancestry ()) = 2)
val _ = silent conflict

(* A failed retry with the existing dispatcher must retain that dispatcher
   and restore the uninitialized context, then allow another successful try. *)
val _ = Context.restore uninitialized
val stable_hooks = Listener.listeners Theory.delta_hook
val _ = Theory.LoadableThyData.temp_encoded_update
  {thy="bool",thydataty="splitLib.persistent.rules.v1",
   shared_readmaps={strings=fn _ => "",terms=fn _ => boolSyntax.T},
   data=HOLsexp.tagged_encode "split-rules-v1" I
     (HOLsexp.List [HOLsexp.List [HOLsexp.Symbol "add",
                                 HOLsexp.String "bool",HOLsexp.String "TRUTH"]])}
val retry_entry = Context.snapshot ()
val retry_failure = Exn.capture enable_split_attribute ()
val _ = check "failed retry preserves existing dispatcher and entry context"
  ((case retry_failure of Exn.Exn (HOL_ERR _) => true | _ => false) andalso
   Portable.pointer_eq (retry_entry,Context.snapshot ()) andalso free () andalso
   same_hooks stable_hooks (Listener.listeners Theory.delta_hook))
val _ = Context.restore uninitialized
val _ = silent enable_split_attribute
val _ = check "retry after failed replay succeeds without listener replacement"
  (empty () andalso same_hooks stable_hooks (Listener.listeners Theory.delta_hook))

(* Listener-name conflicts are also preflighted before ancestry slots or
   loadable-data operations are allocated; retry after removal must work. *)
val _ = Context.restore uninitialized
val hookname = "splitLib.persistence.onload"
val dispatcher = valOf (Listener.remove_listener Theory.delta_hook hookname)
val _ = Theory.register_hook (hookname,K ())
val no_listener_context = Context.snapshot ()
val listener_error =
  (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
val _ = check "foreign listener rejected without partial Context mutation"
  (Portable.pointer_eq (no_listener_context,Context.snapshot ()) andalso
   free () andalso empty () andalso
   (case listener_error of
        SOME e => Feedback.top_structure_of e = "SplitData" andalso
                  Feedback.top_function_of e = "initialize"
      | NONE => false))
val _ = Context.restore owned
val listener_owned_entry = Context.snapshot ()
val listener_owned_error = Exn.capture enable_split_attribute ()
val _ = check "owned initialization also rejects a replaced private listener"
  (Portable.pointer_eq (listener_owned_entry,Context.snapshot ()) andalso
   (case listener_owned_error of Exn.Exn (HOL_ERR e) =>
      Feedback.top_structure_of e = "SplitData" andalso
      Feedback.top_function_of e = "initialize" | _ => false))
val _ = Context.restore uninitialized
val _ = Listener.remove_listener Theory.delta_hook hookname
val _ = Theory.register_hook (hookname,dispatcher)
val _ = silent enable_split_attribute
val _ = check "opt-in succeeds after foreign listener removal" (empty ())
val _ = Context.restore owned
val _ = check "final restoration recovers library rules" (has_rule ())
val _ = silent enable_split_attribute
val _ = Context.restore uninitialized
val _ = ThmAttribute.reserve_word "split"
val _ = silent conflict
val _ = check "reserved word conflict creates neither registry"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = ThmAttribute.define_abbreviation {abbrev="split",expansion=[]}
val _ = silent conflict
val _ = check "abbreviation conflict creates neither registry"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = ThmAttribute.define_abbreviation
  {abbrev="split",expansion=[("split",[])]}
val _ = silent conflict
val _ = check "cyclic abbreviation rejected without expansion"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = Context.with_context owned (fn () =>
  (check "pinned queries select owned snapshot" (has_rule ());
   check "pinned owned initialization rejects"
     (not (can enable_split_attribute ()));
   rejected_exclusion "pinned removal rejects without changing pinned view")) ()
val _ = check "pinned opt-in/removal do not mutate entire live context"
  (Portable.pointer_eq (uninitialized,Context.snapshot ()) andalso
   free () andalso empty ())
val _ = Context.restore owned
val _ = Context.with_context uninitialized (fn () =>
  let
    val _ = check "pinned pre-opt-in queries ignore live owned handle"
      (empty ())
    val result =
      (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
  in
    check "new initialization rejects pinned context"
      (case result of SOME e =>
         Feedback.top_function_of e = "enable_split_attribute" andalso
         Feedback.message_of e = "cannot initialize in a pinned context"
       | NONE => false)
  end) ()
val _ = check "rejected pinned initialization leaves live ownership intact"
  (has_rule ())
val _ = OS.Process.exit OS.Process.success
