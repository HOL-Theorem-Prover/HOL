(* Explicit tracked source, view and prepared-bundle contracts. *)
structure sources =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure S = simpExtLib
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun result name cv tm expected = let
  val actual = QCONV (TRY_CONV cv) tm
  val ok = same actual expected
  val _ = if ok then () else
    print ("Actual: " ^ thm_to_string actual ^ "\nExpected: " ^
           thm_to_string expected ^ "\n")
in check name ok end
fun projection configured ss =
  if configured then E.XTRAVERSE (S.xtraversedata_for_ss ss) []
  else E.TRAVERSE (S.traversedata_for_ss ss) []
fun handles ss = S.rewrite_source_handles ss
fun stable (a,b) = S.same_rewrite_source (a,b) andalso
  S.rewrite_source_compare (a,b) = EQUAL
fun same_handles a b = ListPair.allEq stable (a,b)
fun input th = lhs (concl th)
fun failed name text f = check name
  (case Exn.capture f () of Exn.Exn (HOL_ERR e) =>
     String.isSubstring text (Feedback.message_of e) | _ => false)
val a = ASSUME ``(sources_a:bool -> bool) x = y``
val b = ASSUME ``(sources_b:bool -> bool) x = z``
val u = ASSUME ``(sources_u:bool -> bool) x = w``
val av = ASSUME ``(sources_av:bool -> bool) x = y``
val bv = ASSUME ``(sources_bv:bool -> bool) x = z``
val ca = CONJUNCT1 (CONJ a b)
val cb = CONJUNCT2 (CONJ a b)
val drop = S.name_ss "sources-drop" S.empty_ssfrag
fun named name th = S.named_rewrites_with_names name
  [({Thy="bool",Name=name},th)]
fun source th ss = valOf (List.find
  (fn h => same (#2 (S.source_rewrite h)) th) (handles ss))
fun attach ss = S.++ (ss,S.name_ss "sources-views"
  (S.rewrite_views [(source ca ss,av),(source cb ss,bv)]))
fun fresh prepared n = let
  val base = S.++ (ext_pure_ss,drop)
in
  if not prepared then attach (S.++ (base,
    named "sources-pair" (Ntimes (CONJ a b) n)))
  else let
    val bundle = S.prepare_rewrite_bundle base [Ntimes (CONJ a b) n]
    val [ha,hb] = #2 (hd (S.rewrite_bundle_rules bundle))
  in S.install_rewrite_bundle bundle [(ha,av),(hb,bv)] base end
end
fun inspect ss =
  (ignore (handles ss); ignore (S.rewrite_sources ss []);
   ignore (S.traversedata_for_ss ss); ignore (S.xtraversedata_for_ss ss);
   ignore (S.traverseconfig_for_ss ss);
   ignore (S.rewrite_context_changes (ss,ss)))
val traces = ref 0
fun listener (2,Trace.LZ_TEXT text) =
      if String.isPrefix "New rewrite: " (text ()) orelse
         String.isSubstring "dropped (conversion" (text ())
      then traces := !traces + 1 else ()
  | listener _ = ()
fun watched f =
  (Listener.add_listener Trace.trace_hook ("sources-compilation",listener);
   Portable.finally (fn () => ignore
     (Listener.remove_listener Trace.trace_hook "sources-compilation")) f ())

(* Inventory order is compilation order, not source_compare's serial order.
   Views are visible as installed rewrites, never as new native identities. *)
val _ = let
  val fragment = named "sources-order" (CONJ a b)
  val ss = S.++ (S.++ (ext_pure_ss,fragment),S.rewrites [u])
  val hs = handles ss
  val _ = check "new fragments prepend; conjuncts retain maker order"
    (ListPair.allEq (fn (h,th) => same (#2 (S.source_rewrite h)) th)
       (hs,[u,ca,cb]) andalso
     map (#1 o S.source_rewrite) (tl hs) =
       [SOME {Thy="bool",Name="sources-order.1"},
        SOME {Thy="bool",Name="sources-order.2"}])
  val viewed = attach ss
  val (visible,_) = S.rewrite_sources viewed []
  val _ = check "views keep native identity list but enter visible inventory"
    (same_handles hs (handles viewed) andalso
     ListPair.allEq (fn ((_,actual),expected) => same actual expected)
       (visible,[av,bv,u,ca,cb]) andalso
     map #1 (List.take (visible,2)) =
       map (#1 o S.source_rewrite) (tl hs))
  val duplicates = S.++ (S.++ (ext_pure_ss,fragment),
    S.merge_ss [fragment,fragment])
  val ds = handles duplicates
  val _ = check "merged slots and installation events remain distinct"
    (length ds = 6 andalso List.all (fn h => length (List.filter
       (fn k => S.rewrite_source_compare (h,k) = EQUAL) ds) = 1) ds)
  val ac = S.++ (S.++ (S.empty_ss,drop),
    S.merge_ss [S.ac_ss [(CONJ_COMM,CONJ_ASSOC)],S.rewrites [u]])
  val (comm,assoc,lcomm) = Drule.MK_AC_LCOMM (CONJ_COMM,CONJ_ASSOC)
  val expected = [SPEC_ALL comm,SPEC_ALL assoc,SPEC_ALL lcomm,u]
  val ah = handles ac
  val _ = check "AC comm/assoc/left-comm precede ordinary rewrites"
    (ListPair.allEq (fn (h,th) => same (#2 (S.source_rewrite h)) th)
       (ah,expected))
  val replay = S.remove_ssfrags_preserving_controls ["sources-drop"] ac
in check "AC component identities and order survive replay"
     (same_handles ah (handles replay)) end

(* Both aliases must disappear with their selected source. The sibling is
   retained, with its original actual shared conjunct/view control, not a
   replacement allowance. Exercise late extraction/application both ways. *)
fun invalidations prepared =
  (if prepared then [] else
     [("delete conjunct",fn ss => S.-* (ss,["sources-pair.1"]),true)]) @
  [("suspend conjunct",fn ss =>
      S.suspend_rewrite_sources [source ca ss] ss,true),
   ("filter source fragment",S.filter_rewrites_preserving_controls
      (fn (_,th) => not (same (#1 (BoundedRewrites.DEST_BOUNDED th))
                            (CONJ a b))),false),
   ("remove source fragment",S.remove_ssfrags_preserving_controls
      [if prepared then "PREPARED_REWRITES" else "sources-pair"],false)]
val _ = List.app (fn prepared => List.app (fn reverse =>
  List.app (fn spent =>
  List.app (fn (label,invalidate,sibling) => let
    val ss = fresh prepared 3
    val hs = handles ss
    val old = projection reverse ss
    val _ = List.app (fn _ => result (label ^ ": spend before invalidation")
      old (input av) av) (List.tabulate (spent,I))
    val removed = invalidate ss
    val replay = S.remove_ssfrags_preserving_controls ["sources-drop"] removed
    val _ = check (label ^ ": exact surviving identities/order")
      (same_handles (if sibling then [source cb ss] else []) (handles replay))
    val _ = result (label ^ ": selected original absent")
      (projection reverse replay) (input a) (REFL (input a))
    val late = watched (fn () => let
      val count = !traces
      val _ = inspect replay
      val late = projection (not reverse) replay
      val _ = check (label ^ ": late extraction has no compilation")
        (!traces = count)
    in late end)
    val _ = result (label ^ ": selected view absent")
      late (input av) (REFL (input av))
    val _ = if sibling then
      (List.app (fn i => result (label ^ ": surviving shared allowance")
         (if i mod 2 = 0 then late else old)
         (if i mod 2 = 0 then input bv else input b)
         (if i mod 2 = 0 then bv else cb))
         (List.tabulate (3-spent,I));
       result (label ^ ": old sibling shares exhaustion")
         old (input b) (REFL (input b));
       result (label ^ ": replayed sibling view shares exhaustion")
         late (input bv) (REFL (input bv)))
      else result (label ^ ": sibling view also removed")
        late (input bv) (REFL (input bv))
    val _ = check (label ^ ": inspection never mutates input inventory")
      (Portable.pointer_eq (hs,handles ss))
  in () end) (invalidations prepared)) [1,3]) [false,true]) [false,true]

(* Compatibility includes statement, hypotheses and declared bound; origin
   equality alone must neither keep an alias nor transfer a spent counter.
   A different proof of the SAME statement remains fully compatible. *)
val _ = List.app (fn mode => let
  val changed = ref false
  fun maker (th,control) =
    if not (!changed) then [(th,control)]
    else case mode of
        0 => [(EQ_MP (REFL (concl th)) th,control)]
      | 1 => [(b,control)]
      | 2 => [(ADD_ASSUM ``sources_extra:bool`` th,control)]
      | _ => [(th,BOUNDED (ref 3))]
  val seed = S.SSFRAG {name=NONE,convs=[],rewrs=[],ac=[],congs=[],
                      dprocs=[],filter=SOME maker}
  val ss = S.++ (S.++ (S.++ (S.empty_ss,seed),drop),
    S.rewrites [Once a])
  val previous = hd (handles ss)
  val viewed = S.++ (ss,S.rewrite_views [(previous,av)])
  val old = projection false viewed
  val _ = result "compatibility fixture exhausts old view" old (input av) av
  val _ = changed := true
  val replay = S.remove_ssfrags_preserving_controls ["sources-drop"] viewed
  val current = hd (handles replay)
  val _ = check "replay origin is stable independently of compatibility"
    (S.rewrite_source_compare (previous,current) = EQUAL andalso
     S.same_rewrite_source (previous,current) = (mode = 0))
  val _ = check "incompatible old handle cannot suspend replacement"
    (mode = 0 orelse Portable.pointer_eq
      (S.suspend_rewrite_sources [previous] replay,replay))
  val _ = result "changed/inactive alias cannot revive spent allowance"
    (projection true replay) (input av) (REFL (input av))
  val actual = #2 (S.source_rewrite current)
  val tm = input actual
  val _ = result "compatible replay stays spent; incompatible rule is fresh"
    (projection false replay) tm (if mode = 0 then REFL tm else actual)
  val _ = result "old projection remains independently exhausted"
    old (input a) (REFL (input a))
  val _ = check "context change observes incompatible view dependency"
    (#rebuild (S.rewrite_context_changes (viewed,replay)) = (mode <> 0))
in () end) [0,1,2,3]

(* Prepare/combine/extract must not prime collectors. Installation may, but
   must reuse compiled shapes even after an ambient maker changes. A nested
   composition contains a partially spent conjunct group, a fully spent
   group and an independent live rule. Replay either retains ACTUAL controls
   or resets declared groups, never splitting sibling/view sharing. *)
val _ = List.app (fn reverse => let
  exception Context of unit ref * thm list
  exception Forbidden
  val token = ref ()
  val calls = ref 0
  val collects = ref 0
  val blocked = ref false
  fun maker rw = (if !blocked then raise Forbidden else ();
    calls := !calls + 1; Cond_rewr.mk_cond_rewrs rw)
  val opaque = E.lift (Traverse.REDUCER
    {name=SOME "sources-opaque",initial=Context (token,[]),
     addcontext=fn (Context (r,ths),more) =>
       (if !blocked then raise Forbidden else ();
        collects := !collects + 1; Context (r,ths @ more))
       | _ => raise Forbidden,
     apply=fn _ => NO_CONV})
  val seed = S.SSFRAG {name=NONE,convs=[],rewrs=[],ac=[],congs=[],
                      dprocs=[opaque],filter=SOME maker}
  val base = S.++ (S.++ (S.empty_ss,seed),drop)
  val before_collects = !collects
  val pair = S.prepare_rewrite_bundle base [Ntimes (CONJ a b) 3]
  val spent = S.prepare_rewrite_bundle base [Once u]
  val live = S.prepare_rewrite_bundle base [Once b]
  val rules = S.rewrite_bundle_rules pair
  val [ha,hb] = #2 (hd rules)
  val spent_h = hd (#2 (hd (S.rewrite_bundle_rules spent)))
  val live_h = hd (#2 (hd (S.rewrite_bundle_rules live)))
  val _ = check "preparation invokes makers once per input, no collectors"
    (!calls = 3 andalso !collects = before_collects)
  val original = S.install_rewrite_bundle pair [(ha,av),(hb,bv)] base
  val old = projection reverse original
  val _ = result "composed pair partially consumed before combination"
    old (input av) av
  val exhausted = S.install_rewrite_bundle spent [] base
  val _ = result "composed independent binding exhausted before combination"
    (projection reverse exhausted) (input u) u
  val before_calls = !calls
  val before_collects = !collects
  val combined = watched (fn () => let
    val count = !traces
    val _ = blocked := true
    val inner = S.combine_rewrite_bundles [pair,spent]
    val combined = S.combine_rewrite_bundles
      [S.combine_rewrite_bundles [],inner,live]
    val groups = S.rewrite_bundle_rules combined
    val _ = inspect original
    val _ = check "nested composition retains input grouping and order"
      (ListPair.allEq (fn ((th,hs),(expected,origins)) =>
         same th expected andalso same_handles hs origins)
         (groups,[(Ntimes (CONJ a b) 3,[ha,hb]),
                  (Once u,[spent_h]),(Once b,[live_h])]))
    val _ = failed "nested duplicate binding is rejected" "duplicate binding"
      (fn () => S.combine_rewrite_bundles [inner,pair])
    val _ = check "composition/getters do not compile, collect or make"
      (!traces = count andalso !calls = before_calls andalso
       !collects = before_collects)
    val _ = blocked := false
  in combined end)
  val installed = S.install_rewrite_bundle combined [(ha,av),(hb,bv)] base
  val _ = check "installation reverses events, preserving each conjunct order"
    (same_handles (handles installed) [live_h,spent_h,ha,hb] andalso
     !calls = before_calls andalso !collects = before_collects + 3)
  val _ = failed "overlapping installation rejects before collectors"
    "binding already installed"
    (fn () => S.install_rewrite_bundle combined [] original)
  val _ = check "failed installation does not prime collectors"
    (!collects = before_collects + 3)
  val later = watched (fn () => let
    val count = !traces
    val _ = blocked := true
    val _ = inspect installed
    val later = projection (not reverse) installed
    val _ = check "post-consumption extraction never makes/collects/compiles"
      (!traces = count andalso !calls = before_calls andalso
       !collects = before_collects + 3)
    val _ = blocked := false
  in later end)
  val preserved = watched (fn () => let
    val count = !traces
    val replay = S.remove_ssfrags_preserving_controls ["sources-drop"]
      installed
    val _ = check "cached originals and both views replay without compilation"
      (!traces = count andalso !calls = before_calls)
  in replay end)
  val next = projection reverse preserved
  val _ = result "preserving nested composition keeps exhausted binding"
    next (input u) (REFL (input u))
  val _ = result "surviving view spends shared second conjunct use"
    later (input bv) bv
  val _ = result "old saved projection spends final conjunct use"
    old (input a) ca
  val _ = result "new replay projection observes exact exhaustion"
    next (input av) (REFL (input av))
  val _ = result "independent composed binding still has its allowance"
    next (input b) b
  val _ = result "late projection observes independent exhaustion"
    later (input b) (REFL (input b))
  val reset = watched (fn () => let
    val count = !traces
    val replay = S.remove_ssfrags ["sources-drop"] installed
    val _ = check "ordinary replay resets controls without recompiling shapes"
      (!traces = count andalso !calls = before_calls)
  in replay end)
  val _ = check "reset replay retains composed identities"
    (same_handles (handles installed) (handles reset))
  val reset_cv = projection (not reverse) reset
  val _ = result "ordinary replay resets exhausted independent binding"
    reset_cv (input u) u
  val _ = List.app (fn (tm,expected) => result
      "reset conjuncts/views share one declared group" reset_cv tm expected)
    [(input av,av),(input bv,bv),(input a,ca)]
  val _ = result "reset shared group has exactly its declared uses"
    (projection reverse reset) (input av) (REFL (input av))
  val _ = result "reset does not refill old saved projection"
    old (input av) (REFL (input av))
in () end) [false,true]

(* Failed matcher preparation is cached too. An inactive foreign handle
   must not acquire a retrospective identity or borrow an unrelated quota. *)
val _ = List.app (fn reverse => watched (fn () => let
  val base = S.++ (ext_pure_ss,drop)
  val bundle = S.prepare_rewrite_bundle base [Once a]
  val h = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val foreign = hd (handles (S.++ (base,S.rewrites [Once a])))
  val count = !traces
  val installed = S.install_rewrite_bundle bundle
    [(h,TRUTH),(foreign,av)] base
  val _ = check "rejected view attempted once; foreign binding ignored"
    (!traces = count + 1 andalso same_handles (handles installed) [h] andalso
     length (#1 (S.rewrite_sources installed [])) = 1)
  val old = projection reverse installed
  val _ = result "foreign view has no installed conversion"
    old (input av) (REFL (input av))
  val _ = result "native allowance survives rejected view" old (input a) a
  val count = !traces
  val preserved = S.remove_ssfrags_preserving_controls ["sources-drop"]
    installed
  val reset = S.remove_ssfrags ["sources-drop"] installed
  val _ = inspect preserved
  val _ = inspect reset
  val _ = check "rejected cached views never prepare again during replay"
    (!traces = count)
  val _ = result "rejected-view preserving replay stays exhausted"
    (projection (not reverse) preserved) (input a) (REFL (input a))
  val _ = result "rejected-view reset replay resets only the source control"
    (projection (not reverse) reset) (input a) a
  val _ = check "compatible rejected-view replay does not force rebuilding"
    (not (#rebuild (S.rewrite_context_changes (installed,preserved))))
in () end)) [false,true]

(* Returning a compatible source AFTER an old view event does not install
   that old view retroactively. A fresh attachment is explicit construction,
   and must still share the bundle's actual controls with saved projections. *)
val _ = List.app (fn reverse => let
  val base = S.++ (ext_pure_ss,drop)
  val bundle = S.prepare_rewrite_bundle base [Ntimes a 3]
  val h = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val installed = S.install_rewrite_bundle bundle [] base
  val viewed = S.++ (installed,S.rewrite_views [(h,av)])
  val removed = S.remove_ssfrags_preserving_controls ["PREPARED_REWRITES"]
    viewed
  val restored = S.install_rewrite_bundle bundle [] removed
  val _ = check "reinstallation returns source identity, not an old alias"
    (same_handles (handles viewed) (handles restored))
  val cv = projection reverse restored
  val _ = result "source reinstalled after view event has no alias conversion"
    cv (input av) (REFL (input av))
  val _ = check "lost view is observed despite returning compatible source"
    (#rebuild (S.rewrite_context_changes (viewed,restored)) andalso
     #rebuild (S.rewrite_context_changes (restored,viewed)))
  val attached = S.++ (restored,S.rewrite_views [(h,av)])
  val _ = result "new explicit view attachment works"
    (projection (not reverse) attached) (input av) av
  val _ = result "reinstalled original shares new view control"
    cv (input a) a
  val old = projection (not reverse) viewed
  val _ = result "saved original view shares reinstalled control"
    old (input av) av
  val _ = result "new attachment observes complete exhaustion"
    (projection reverse attached) (input av) (REFL (input av))
  val _ = result "reinstalled native observes complete exhaustion"
    cv (input a) (REFL (input a))
in () end) [false,true]

(* One prepared event can have different views in separate installations.
   Event/source/index equality must not hide changed compiled statements.
   Conversely different proofs/generalization of an identical compiled view
   must not force reconstruction. All installations still share controls. *)
val _ = List.app (fn reverse => let
  val base = ext_pure_ss
  val bundle = S.prepare_rewrite_bundle base [Ntimes a 3]
  val h = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val left = S.install_rewrite_bundle bundle [(h,av)] base
  val right = S.install_rewrite_bundle bundle [(h,bv)] base
  val proof = GEN ``sources_fresh:bool`` (EQ_MP (REFL (concl av)) av)
  val compatible = S.install_rewrite_bundle bundle [(h,proof)] base
  val extra = ADD_ASSUM ``sources_extra:bool`` av
  val hypotheses = S.install_rewrite_bundle bundle [(h,extra)] base
  val _ = check "different views retain the same bundle source identities"
    (same_handles (handles left) (handles right))
  val _ = check "same event/source/index cannot hide changed view statement"
    (#rebuild (S.rewrite_context_changes (left,right)) andalso
     #rebuild (S.rewrite_context_changes (right,left)))
  val _ = check "changed view hypotheses also demand rebuilding"
    (#rebuild (S.rewrite_context_changes (left,hypotheses)))
  val _ = check "equivalent compiled view ignores proof/generalization"
    (not (#rebuild (S.rewrite_context_changes (left,compatible))))
  val lcv = projection reverse left
  val rcv = projection (not reverse) right
  val _ = result "first installation sees only its own attached alias"
    lcv (input bv) (REFL (input bv))
  val _ = result "second installation sees only its own attached alias"
    rcv (input av) (REFL (input av))
  val _ = result "first installed alias uses shared bundle control"
    lcv (input av) av
  val _ = result "second installed alias uses same bundle control"
    rcv (input bv) bv
  val _ = result "equivalent generalized alias uses final shared allowance"
    (projection reverse compatible) (input av) av
  val _ = result "differing installations all observe exhaustion"
    rcv (input bv) (REFL (input bv))
in () end) [false,true]

(* Opaque collector contents, not just counts: suspension must remove one
   conjunct from context without deleting its sibling or losing payloads. *)
val _ = List.app (fn reverse => let
  exception Payload of unit ref * thm list
  val token = ref ()
  val seen = ref ([] : thm list)
  val intact = ref true
  val opaque = E.CONTEXT_REDUCER
    {name=SOME "sources-context",initial=Payload (token,[]),
     addcontext=fn (Payload (r,ths),more) => Payload (r,ths @ more)
       | _ => raise Fail "context identity",
     apply=fn {context,...} => fn tm =>
       (case context of Payload (r,ths) =>
          (intact := (!intact andalso Portable.pointer_eq (r,token));
           seen := List.concat (map (CONJUNCTS o SPEC_ALL o
             #1 o BoundedRewrites.DEST_BOUNDED) ths))
        | _ => raise Fail "apply identity";
        NO_CONV tm)}
  val base = S.++ (S.++ (ext_pure_ss,S.dproc_ss opaque),drop)
  val ss = attach (S.++ (base,named "sources-pair"
    (Ntimes (CONJ a b) 2)))
  val suspended = S.suspend_rewrite_sources [source ca ss] ss
  val replay = S.remove_ssfrags_preserving_controls ["sources-drop"] suspended
  val _ = result "opaque replay still rewrites surviving sibling"
    (projection reverse replay) (input bv) bv
  val _ = result "opaque replay does not resurrect selected original"
    (projection (not reverse) replay) (input a) (REFL (input a))
  val _ = check "opaque contexts retain payload and only surviving facts"
    (!intact andalso List.exists (same cb) (!seen) andalso
     not (List.exists (same ca) (!seen)))
  val delta = S.rewrite_context_changes (ss,replay)
in check "opaque context reconstruction requires rebuild"
     (#rebuild delta andalso #context_sensitive delta) end) [false,true]

val _ = let
  val batches = ref ([] : thm list list)
  exception Context
  val observer = E.CONTEXT_REDUCER
    {name=SOME "suspension context observer",initial=Context,
     addcontext=fn (ctxt,more) => (batches := more :: !batches; ctxt),
     apply=fn _ => NO_CONV}
  val base = S.++ (ext_pure_ss,S.dproc_ss observer)
  val pair = CONJ a b
  val fragment = S.rewrites [pair,TRUTH]
  val ss = S.++ (S.++ (base,fragment),S.merge_ss [fragment,fragment])
  val all = handles ss
  fun suspend requested =
    (batches := []; ignore (S.suspend_rewrite_sources requested ss);
     List.rev (!batches))
  fun same_batches expected actual =
    ListPair.allEq (ListPair.allEq (uncurry same)) (expected,actual)
  val _ = check "suspension rebuilds only affected context slots"
    (case all of [first,_,_,_,older_first,_] =>
       same_batches [[cb,TRUTH],[cb,TRUTH,pair,TRUTH]]
         (suspend [first,first,older_first])
     | _ => false)
in check "suspending every handle retains non-rewrite context facts"
     (same_batches [[TRUTH],[TRUTH,TRUTH]] (suspend all))
end

val _ = let
  val input_counter = ref NONE
  fun maker (th,tag as BoundedRewrites.BOUNDED counter) =
        (case !input_counter of
             NONE => (input_counter := SOME counter; [(th,tag)])
           | SOME first =>
               (first := 3; [(th,BoundedRewrites.BOUNDED first)]))
    | maker item = [item]
  val maker_frag = S.SSFRAG
    {name=SOME "cross-slot quota maker",convs=[],rewrs=[],ac=[],congs=[],
     dprocs=[],filter=SOME maker}
  val base = S.++ (S.++ (S.empty_ss,maker_frag),drop)
  val bundle = S.prepare_rewrite_bundle base [Ntimes a 2,Ntimes b 7]
  val installed = S.install_rewrite_bundle bundle [] base
  val _ = valOf (!input_counter) := 0
  val replay = S.remove_ssfrags ["sources-drop"] installed
  val cv = projection true replay
  val _ = result "replay resets a cross-slot quota to its first allowance"
    cv (input b) b
  val _ = result "replayed cross-slot quota remains available once"
    cv (input a) a
  val _ = result "both replayed slots consume the same quota"
    cv (input b) (REFL (input b))
in result "cross-slot quota replay leaves the installed quota alone"
     (projection true installed) (input a) (REFL (input a))
end

(* Context changes report arbitrary conversion keys in either direction;
   keyless/opaque traversal changes demand rebuilding. Native source changes
   are inspected separately, but invalidating a view must rebuild its opaque
   compiled dependency even when its containing event survives. *)
fun delta name old current keys rebuild sensitive = let
  val actual = S.rewrite_context_changes (old,current)
in check name
     (ListPair.allEq (fn ((vs,t),(ws,u)) =>
        ListPair.allEq (uncurry aconv) (vs,ws) andalso aconv t u)
        (#keys actual,keys)
      andalso #rebuild actual = rebuild andalso
      #context_sensitive actual = sensitive) end
val _ = let
  val base = S.empty_ss
  val key = ([``x:bool``],input a)
  val keyed = S.++ (base,S.conv_ss
    {name="sources-key",key=SOME key,trace=0,conv=fn _ => fn _ => NO_CONV})
  val keyless = S.++ (base,S.conv_ss
    {name="sources-keyless",key=NONE,trace=0,conv=fn _ => fn _ => NO_CONV})
  val _ = delta "identical context has no changes" base base [] false false
  val _ = delta "adding keyed conversion reports its exact key"
    base keyed [key] false false
  val _ = delta "deleting keyed conversion reports its exact key"
    keyed (S.-* (keyed,["sources-key"])) [key] false false
  val _ = delta "reverse comparison reports removed key"
    keyed base [key] false false
  val replacement_key = ([],input b)
  val replacement = S.++ (S.-* (keyed,["sources-key"]),S.conv_ss
    {name="sources-key",key=SOME replacement_key,trace=0,
     conv=fn _ => fn _ => NO_CONV})
  val _ = delta "replacement reports both old and new conversion keys"
    keyed replacement [key,replacement_key] false false
  val _ = delta "keyless addition demands rebuild" base keyless [] true false
  val _ = delta "keyless removal demands rebuild" keyless base [] true false
  val ss = fresh false 2
  val _ = result "context inspection fixture partially consumes a view"
    (projection false ss) (input av) av
  val _ = delta "consumption alone is not a structural change"
    ss ss [] false false
  val suspended = S.suspend_rewrite_sources [source ca ss] ss
  val _ = delta "suspension invalidates a surviving event's dependent view"
    ss suspended [] true false
  val deleted = S.-* (ss,["sources-pair.1"])
  val _ = delta "literal deletion invalidates dependent view"
    ss deleted [] true false
  val filtered = S.filter_rewrites_preserving_controls
    (fn (_,th) => not (same (#1 (BoundedRewrites.DEST_BOUNDED th))
                          (CONJ a b))) ss
  val _ = delta "filtering invalidates dependent views"
    ss filtered [] true false
  val removed = S.remove_ssfrags_preserving_controls ["sources-pair"] ss
  val _ = delta "source removal invalidates surviving view event"
    ss removed [] true false
  val replay = S.remove_ssfrags_preserving_controls ["sources-drop"] ss
  val _ = delta "compatible view replay needs no rebuild"
    ss replay [] false false
  val bundle = S.prepare_rewrite_bundle base [a]
  val handle_a = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val viewed = S.install_rewrite_bundle bundle [(handle_a,av)] base
  val viewed = S.++ (viewed,drop)
  val _ = delta "ordinary replay of a prepared view reports a rebuild"
    viewed (S.remove_ssfrags ["sources-drop"] viewed) [] true false
  val _ = delta "control-preserving replay of a prepared view is stable"
    viewed (S.remove_ssfrags_preserving_controls ["sources-drop"] viewed)
    [] false false
  val ac = S.++ (base,S.ac_ss [(CONJ_COMM,CONJ_ASSOC)])
  val _ = delta "AC traversal addition demands rebuild" base ac [] true false
in () end

val _ = print ("SOURCE_VIEW_BUNDLE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
