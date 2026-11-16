(* Tracked exclusions, suppression and actual replay controls. *)
structure exclusions =
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
fun result name cv tm expected =
  check name (same (QCONV (TRY_CONV cv) tm) expected)
fun projection configured ss =
  if configured then E.XTRAVERSE (S.xtraversedata_for_ss ss) []
  else E.TRAVERSE (S.traversedata_for_ss ss) []
fun args ss ths = #1 (S.prepare_rewrite_arguments ss ths)
fun handles ss = S.rewrite_source_handles ss
fun stable (a,b) = S.same_rewrite_source (a,b) andalso
  S.rewrite_source_compare (a,b) = EQUAL
fun failure name predicate f =
  check name (case Exn.capture f () of
    Exn.Exn e => predicate e | _ => false)
fun error text (HOL_ERR e) =
      Feedback.top_structure_of e = "simpLib" andalso
      String.isSubstring text (Feedback.message_of e)
  | error _ _ = false
fun scoped f = let val saved = Context.snapshot ()
  in Portable.finally (fn () => Context.restore saved) f () end
val drop = S.name_ss "exclusion-drop" S.empty_ssfrag
val a = ASSUME ``(exclusion_a:bool -> bool) x = y``
val b = ASSUME ``(exclusion_b:bool -> bool) x = z``
val u = ASSUME ``(exclusion_u:bool -> bool) x = w``
val d = ASSUME ``(exclusion_d:bool -> bool) x = v``
val alias = ASSUME ``(exclusion_alias:bool -> bool) x = z``
val ca = CONJUNCT1 (CONJ a b)
val cb = CONJUNCT2 (CONJ a b)
fun input th = lhs (concl th)
fun named name th = S.rewrites_with_names [({Thy="bool",Name=name},th)]
fun source th ss = valOf (List.find
  (fn h => aconv (concl (#2 (S.source_rewrite h))) (concl th)) (handles ss))
val removals =
  [("removal", S.remove_ssfrags_preserving_controls ["exclusion-drop"]),
   ("filter", S.filter_rewrites_preserving_controls
      (fn (_,th) => not (same th d)))]

(* A deleted conjunct must not take its sibling, alias or unrelated native
   rule with it. Every surviving runner uses the original actual counter.
   Exercise both projection orders and native/prepared unrelated sources. *)
val _ = List.app (fn prepared => List.app (fn reverse =>
  List.app (fn (label,remove) => let
    val initial = S.++ (ext_pure_ss,drop)
    val ss = S.++ (initial,named "exclusion-pair" (Ntimes (CONJ a b) 3))
    val survivor = source cb ss
    val deleted = source ca ss
    val ss = S.++ (ss,S.rewrite_views [(survivor,alias)])
    val ss = if prepared then S.install_rewrite_bundle
        (S.prepare_rewrite_bundle ss [Ntimes u 2]) [] ss
      else S.++ (ss,named "exclusion-u" (Ntimes u 2))
    val ss = S.++ (ss,S.rewrites [d])
    val unrelated = source u ss
    val first = projection reverse ss
    val _ = result (label ^ ": spend shared conjunct control")
      first (input a) ca
    val _ = result (label ^ ": spend unrelated native control")
      first (input u) u
    val {Thy,Name} = valOf (#1 (S.source_rewrite deleted))
    val key = Thy ^ "$" ^ Name
    val deletion = if prepared then S.Excl (Thy ^ "." ^ Name)
                   else S.ExclX ("rule:" ^ key)
    val removed = args ss
      [S.Excl "missing-before",deletion,
       S.Excl "missing-after",S.Excl "missing-after"]
    val removed = remove removed
    val hs = handles removed
    val _ = check (label ^ ": only selected conjunct disappears")
      (not (List.exists (fn h => stable (h,deleted)) hs) andalso
       List.exists (fn h => stable (h,survivor)) hs andalso
       List.exists (fn h => stable (h,unrelated)) hs)
    val surviving_order = List.filter
      (fn h => List.exists (fn current => stable (h,current)) hs) (handles ss)
    val _ = check (label ^ ": surviving inventory order/identity unchanged")
      (ListPair.allEq stable (hs,surviving_order))
    val second = projection (not reverse) removed
    val _ = result (label ^ ": original projection order also sees deletion")
      (projection reverse removed) (input a) (REFL (input a))
    val _ = result (label ^ ": deletion survives preserving replay")
      second (input a) (REFL (input a))
    val _ = result (label ^ ": sibling retains remaining allowance")
      second (input b) cb
    val _ = result (label ^ ": alias shares final sibling allowance")
      first (input alias) alias
    val _ = result (label ^ ": new alias is exhausted")
      second (input alias) (REFL (input alias))
    val _ = result (label ^ ": old sibling is exhausted")
      first (input b) (REFL (input b))
    val _ = result (label ^ ": unrelated survivor retains one use")
      second (input u) u
    val _ = result (label ^ ": unrelated old control also exhausted")
      first (input u) (REFL (input u))
    val late = projection reverse removed
  in result (label ^ ": late extraction never refreshes")
       late (input b) (REFL (input b)) end) removals)
  [false,true]) [false,true]

(* Failed extended resolution is not a persistent exclusion. Pending rule
   deletions mask later resolution, while unmatched literal deletions ARE
   persistent history, including when the compiler previously dropped rules. *)
val _ = List.app (fn reverse => let
  val blocker = S.SSFRAG
    {name=SOME "exclusion-blocker",convs=[],rewrs=[],ac=[],congs=[],
     dprocs=[],filter=SOME (fn _ => [])}
  val hidden = S.++ (S.++ (S.empty_ss,blocker),named "hidden" a)
  val literal = args hidden [S.Excl "hidden"]
  val _ = failure "unmatched extended target is an error"
    (error "ExclX did not match rule:hidden")
    (fn () => args hidden [S.ExclX "rule:hidden"])
  val revived = S.remove_ssfrags_preserving_controls
    ["exclusion-blocker"] hidden
  val retained = S.remove_ssfrags_preserving_controls
    ["exclusion-blocker"] literal
  val _ = result "failed extended attempt leaves history untouched"
    (projection reverse revived) (input a) a
  val _ = result "unmatched literal deletion survives maker removal"
    (projection reverse retained) (input a) (REFL (input a))
  val ss = S.++ (ext_pure_ss,
    named "exclusion-failure" (Ntimes a 2))
  val old = projection reverse ss
  val hs = handles ss
  val _ = result "spend before failed batch" old (input a) a
  val _ = failure "pending deletion masks duplicate extended request"
    (error "ExclX did not match rule:exclusion-failure")
    (fn () => args ss [S.ExclX "rule:exclusion-failure",
                       S.ExclX "rule:exclusion-failure"])
  val _ = check "failed batch retains physical inventory"
    (Portable.pointer_eq (hs,handles ss))
  val _ = result "failed batch does not spend or reset live quota"
    (projection (not reverse) ss) (input a) a
in result "saved projection observes failure's unchanged exhaustion"
     old (input a) (REFL (input a)) end) [false,true]

(* Strict and resolved histories differ after theory rewind, including on
   preserving reconstruction and failures with live/exhausted controls. *)
val _ = scoped (fn () => let
  val saved = Context.snapshot ()
  val thy = "trackedExclusionHistory"
  val _ = Theory.link_parents (thy,"selftest") []
  val ss = S.++ (S.++ (S.++ (ext_pure_ss,drop),
    named "exclusion-survivor" (Ntimes a 2)),
    S.merge_ss [S.rewrites_with_names [({Thy=thy,Name="gone"},b)],
                S.rewrites [d]])
  val old = projection false ss
  val _ = result "spend before strict/resolved history" old (input a) a
  val strict = args ss [S.Excl (thy ^ ".gone")]
  val resolved = args ss [S.ExclX ("rule:" ^ thy ^ ".gone")]
  val present = Context.snapshot ()
  val _ = Context.restore saved
  val _ = List.app (fn (_,remove) =>
    failure "strict preserving replay reparses and fails after rewind"
      (error "bad theory name") (fn () => remove strict)) removals
  val _ = result "failed replay did not reset partial control"
    (projection true strict) (input a) a
  val _ = result "saved projection shares exhaustion after replay failure"
    old (input a) (REFL (input a))
  val _ = List.app (fn (_,remove) => let
    val replay = remove resolved
    val _ = check "resolved replay preserves surviving source identities"
      (List.exists (fn h => stable (source a ss,h)) (handles replay))
    val _ = result "resolved history keeps deletion after rewind"
      (projection false replay) (input b) (REFL (input b))
  in result "resolved preserving replay cannot refresh spent quota"
       (projection true replay) (input a) (REFL (input a)) end) removals
  val _ = Context.restore present
  val replay = S.remove_ssfrags_preserving_controls ["exclusion-drop"] strict
in result "strict replay succeeds in restored naming context, still spent"
     (projection false replay) (input a) (REFL (input a)) end)

(* Prohibition is distinct from removal; force-add clears it. Makers and
   opaque collectors retain the private replay schedule and payload identity. *)
val _ = let
  exception Private of unit ref * thm list
  val token = ref ()
  val events = ref ([] : string list)
  val intact = ref true
  fun maker rw = (events := !events @ ["maker"]; Cond_rewr.mk_cond_rewrs rw)
  val opaque = E.lift (Traverse.REDUCER
    {name=SOME "exclusion-opaque",initial=Private (token,[]),
     addcontext=fn (Private (r,ths),more) =>
       (events := !events @ ["collector"];
        intact := (!intact andalso Portable.pointer_eq (r,token));
        Private (r,ths @ more))
       | _ => raise Fail "lost opaque context",
     apply=fn {context,...} => fn tm =>
       (case context of Private (r,_) =>
          intact := (!intact andalso Portable.pointer_eq (r,token))
        | _ => raise Fail "lost opaque apply context";
        NO_CONV tm)})
  val seed = S.SSFRAG
    {name=SOME "exclusion-maker",convs=[],rewrs=[],ac=[],congs=[],
     dprocs=[],filter=SOME maker}
  val fragment = S.named_rewrites "exclusion-prohibited" [Once a]
  val initial = S.++ (S.++ (S.empty_ss,seed),S.dproc_ss opaque)
  val installed = S.++ (S.++ (initial,drop),fragment)
  val _ = check "install collector/maker order"
    (!events = ["collector","maker","collector"])
  val old = projection false installed
  val _ = result "prohibited original is exhausted first" old (input a) a
  val _ = events := []
  val excluded = S.exclude_ssfrags ["exclusion-prohibited"] installed
  val _ = check "exclusion replay only primes surviving empty fragment"
    (!events = ["collector"])
  val _ = events := []
  val _ = failure "missing preserving removal is inert UNCHANGED"
    (fn Conv.UNCHANGED => true | _ => false)
    (fn () => S.remove_ssfrags_preserving_controls ["missing"] excluded)
  val unfiltered = S.filter_rewrites_preserving_controls (K true) excluded
  val _ = check "no-op preserving filter returns original without callbacks"
    (Portable.pointer_eq (excluded,unfiltered) andalso null (!events))
  val skipped = S.++ (excluded,fragment)
  val _ = check "prohibited addition is physically inert"
    (Portable.pointer_eq (excluded,skipped) andalso null (!events))
  val replay_excluded = S.remove_ssfrags_preserving_controls
    ["exclusion-drop"] excluded
  val replay_skipped = S.++ (replay_excluded,fragment)
  val _ = check "preserving replay retains named prohibition"
    (Portable.pointer_eq (replay_excluded,replay_skipped) andalso
     null (!events))
  val forced = S.force_add skipped fragment
  val _ = check "force-add compiles exactly once"
    (!events = ["maker","collector"])
  val again = S.++ (forced,fragment)
  val _ = check "force-add clears prohibition for subsequent duplicate"
    (length (handles again) = 2 andalso
     not (stable (hd (handles again),hd (tl (handles again)))) andalso
     !events = ["maker","collector","maker","collector"])
  val first = projection false again
  val _ = result "first forced occurrence spends its own allowance"
    first (input a) a
  val _ = events := []
  val preserved = S.remove_ssfrags_preserving_controls ["exclusion-drop"]
    (S.limit 7 again)
  val _ = check "preserving replay has exact maker/collector order and limit"
    (!events = ["maker","collector","maker","collector"] andalso
     #limit (S.traversedata_for_ss preserved) = SOME 7)
  val _ = result "preserving replay retains second independent occurrence"
    (projection true preserved) (input a) a
  val _ = result "forced duplicates share exhaustion across projections"
    first (input a) (REFL (input a))
  val _ = events := []
  val reset = S.remove_ssfrags ["exclusion-drop"] again
  val _ = check "ordinary replay has same callback schedule"
    (!events = ["maker","collector","maker","collector"])
  val _ = result "ordinary replay resets first declared allowance"
    (projection true reset) (input a) a
  val _ = result "ordinary replay resets second declared allowance"
    (projection false reset) (input a) a
  val _ = result "ordinary reset duplicates are bounded, not refreshed again"
    (projection true reset) (input a) (REFL (input a))
in check "opaque context identity survives every projection/replay" (!intact)
end

(* Namespace separation: split/case suppression must not suppress an ordinary
   user looper merely because its literal name equals a split display. *)
val _ = scoped (fn () => let
  val _ = new_theory "trackedExclusionNamespaces"
  val split = save_thm ("bool_split",splitLib.type_split_of ``:bool``)
  val key = current_theory () ^ "$bool_split"
  fun scenario (display,target,add) = let
    val ss = S.add_looper (display,fn _ => CONJ_TAC)
      (add (S.++ (S.empty_ss,drop)))
    val deleted = args ss [S.ExclX target]
    val _ = if String.isPrefix "case:" target then
        ignore (args deleted [S.ExclX target])
      else failure "removed local split is not a second extended target"
        (error ("ExclX did not match " ^ target))
        (fn () => args deleted [S.ExclX target])
    val later = add deleted
    val replay = S.remove_ssfrags_preserving_controls ["exclusion-drop"] later
    val goal = ([],``p /\ q``)
    fun verify ss = let
      val (goals,validate) = runtac (Tactical.VALID (S.SIMP_TAC ss [])) goal
      val proof = validate [ASSUME ``p:bool``,ASSUME ``q:bool``]
    in check "split/case target leaves colliding ordinary looper active"
      (ListPair.allEq (fn ((asl,w),tm) => null asl andalso aconv w tm)
        (goals,[``p:bool``,``q:bool``]) andalso
       same proof (CONJ (ASSUME ``p:bool``) (ASSUME ``q:bool``))) end
    val _ = List.app verify [deleted,later,replay]
    val removed = args replay [S.ExclX ("looper:" ^ display)]
    val (goals,_) = runtac (Tactical.VALID (S.SIMP_TAC removed [])) goal
  in check "explicit looper target removes only the ordinary collision"
       (case goals of [([],tm)] => aconv tm (#2 goal) | _ => false) end
  val _ = scenario ("split.case bool","case:bool",I)
  val _ = scenario ("split " ^ key,"split:" ^ key,S.add_split split)
in () end)

val _ = print ("EXTENSION_EXCLUSIONS_OK checks=" ^
               Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
