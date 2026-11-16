(* Separate tracked-construction contracts. Ordinary objects are used only
   as ordinary clients or as explicitly lifted opaque reducers. *)
structure selftest =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure S = simpExtLib
val ext_ETA_ss = simpExtLib.lift_ssfrag boolSimps.ETA_ss
val ext_bool_ss = simpExtLib.lift_simpset boolSimps.bool_ss
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val _ = APIExamples.fragments

val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected)
fun total cv = QCONV (TRY_CONV cv)
fun converted name cv input output = let
  val th = total cv input
in check name (null (hyp th) andalso aconv (lhs (concl th)) input andalso
               aconv (rhs (concl th)) output)
end
fun fails name pred f =
  check name (case Exn.capture f () of Exn.Exn e => pred e
                                    | Exn.Res _ => false)
fun scoped f = let val saved = Context.snapshot ()
  in Portable.finally (fn () => Context.restore saved) f () end
fun uses rules th =
  ListPair.allEq
    (fn (r,t) => same (SPEC_ALL r) (SPEC_ALL t)) (rules,th)

(* The standard recipe order is unchanged, and ETA stays opt-in. These are
   new tracked constructions from immutable inputs, not converted sets. *)
val _ = check "BOOL recipe keeps PURE/BOOL/NOT/CONG/UNWIND order"
  (map S.frag_name (List.rev (S.ssfrags_of ext_bool_ss)) =
   map SOME ["PURE","BOOL","NOT","CONG","UNWIND"])
val _ = converted "tracked BOOL beta and boolean rewriting"
  (S.SIMP_CONV ext_bool_ss [])
  ``(\x:bool. x /\ T) p`` ``p:bool``
val _ = converted "tracked BOOL contextual COND congruence"
  (S.SIMP_CONV ext_bool_ss [])
  ``if p then (f:bool -> bool) p else g p``
  ``if p then (f:bool -> bool) T else g F``
val _ = converted "ETA is not silently installed in BOOL"
  (S.SIMP_CONV ext_bool_ss []) ``\x:bool. f x:bool``
  ``\x:bool. f x:bool``
val _ = converted "tracked ETA is explicitly installable"
  (S.SIMP_CONV (S.++ (ext_pure_ss,ext_ETA_ss)) [])
  ``(f:(bool -> bool) -> bool) (\x. g x)`` ``f (g:bool -> bool):bool``
val _ = List.app (fn tm => converted "ETA excludes logical binders"
  (S.SIMP_CONV (S.++ (ext_pure_ss,ext_ETA_ss)) []) tm tm)
  [``!x:bool. P x``, ``?x:bool. P x``, ``@x:bool. P x``]

(* A saved NONE stays live; an explicit depth does not modify the shared
   Cond_rewr control. Assertions compare the complete theorem/hypothesis set. *)
val _ = let
  val root = ``(depth_f:bool -> bool) depth_x``
  val output = ``depth_y:bool``
  val p = ``depth_p = depth_p'``
  val q = ``depth_q = depth_q'``
  val r0 = ASSUME (mk_imp (p,mk_eq (root,output)))
  val r1 = ASSUME (mk_imp (q,mk_eq (p,T)))
  val r2 = ASSUME (mk_eq (q,T))
  val expected = MP r0 (EQT_ELIM (MP r1 (EQT_ELIM r2)))
  val ss = S.++ (ext_pure_ss,S.rewrites [r0,r1,r2])
  val saved = !Cond_rewr.stack_limit
  fun run () = let
    val _ = Cond_rewr.stack_limit := 0
    val live = E.XTRAVERSE (S.xtraversedata_for_ss ss) []
    val configured = E.XTRAVERSE
      (S.xtraversedata_for_ss (S.set_cond_depth 40 ss)) []
    val zero = E.XTRAVERSE
      (S.xtraversedata_for_ss (S.set_cond_depth 0 ss)) []
    val _ = check "saved live depth initially rejects recursive condition"
      (same (total live root) (REFL root))
    val _ = check "configured depth overrides live zero with full proof"
      (same (configured root) expected andalso !Cond_rewr.stack_limit = 0)
    val (_,tracked) = S.track (fn () => configured root) ()
    val _ = check "tracking excludes recursive side-condition rewrites"
      (uses [r0] tracked)
    val _ = Cond_rewr.stack_limit := 40
    val _ = check "saved NONE observes later shared live depth"
      (same (live root) expected)
    val _ = check "explicit zero stays zero after shared depth changes"
      (same (total zero root) (REFL root) andalso
       !Cond_rewr.stack_limit = 40)
    val _ = Cond_rewr.stack_limit := 0
  in check "saved NONE observes subsequent live depth reduction"
       (same (total live root) (REFL root)) end
in Portable.finally (fn () => Cond_rewr.stack_limit := saved) run () end

(* Lift construction and projection are inert. Collectors, private payloads,
   and saved/default versus refreshing/configured lifetimes remain explicit. *)
val _ = let
  exception Private of unit ref * thm list
  val token = ref ()
  val collects = ref 0
  val applies = ref 0
  val intact = ref true
  val fact = TRUTH
  val atom = ``lift_atom:bool``
  val r = Traverse.REDUCER
    {name=SOME "opaque lifted client",initial=Private (token,[]),
     addcontext=fn (Private (r,ths),more) =>
       (collects := !collects + 1; Private (r,ths @ more))
       | _ => raise Fail "lost lifted collector payload",
     apply=fn {context,stack,relation=(rel,refl),...} => fn tm =>
       (applies := !applies + 1;
        intact := (!intact andalso null stack andalso aconv rel equality
          andalso same (refl tm) (REFL tm) andalso
          (case context of Private (r,ths) =>
             Portable.pointer_eq (r,token) andalso uses [fact] ths
           | _ => false));
        NO_CONV tm)}
  val lifted = E.lift r
  val ss = S.++ (S.empty_ss,S.dproc_ss lifted)
  val data = S.traversedata_for_ss ss
  val xd = S.xtraversedata_for_ss ss
  val _ = check "lift/install/projections invoke no opaque callbacks"
    (!collects = 0 andalso !applies = 0 andalso
     null (S.rewrite_source_handles ss))
  val default = E.TRAVERSE data [fact]
  val _ = check "default conversion collects once at construction"
    (!collects = 1 andalso !applies = 0)
  val _ = converted "lifted default first proof" default atom atom
  val _ = converted "lifted default reused proof" default atom atom
  val _ = check "default reuse retains collector and payload"
    (!collects = 1 andalso !applies = 2 andalso !intact)
  val configured = E.XTRAVERSE xd [fact]
  val _ = check "configured conversion delays collection" (!collects = 1)
  val _ = converted "lifted configured first proof" configured atom atom
  val _ = converted "lifted configured reused proof" configured atom atom
in check "configured reuse refreshes original collector exactly once each"
     (!collects = 3 andalso !applies = 4 andalso !intact) end

(* Closed proof ingredients give distinct heads without installing their
   definitions. This keeps quota and parent/child order observations exact. *)
val _ = scoped (fn () => let
  val _ = new_theory "simpExtContracts"
  val g = new_definition ("ext_g_def", ``ext_g (x:bool) = T``)
  val h = new_definition ("ext_h_def", ``ext_h (x:bool) = T``)
  val c = new_definition ("ext_c_def", ``ext_c (x:bool) = T``)
  val k = new_definition ("ext_k_def", ``ext_k (x:bool) = T``)
  val u = new_definition ("ext_u_def", ``ext_u (x:bool) = T``)
  fun proof tm = Tactical.prove (tm,Rewrite.REWRITE_TAC [g,h,c,k,u])
  val original = proof ``!x. ext_c (ext_g x) = ext_k x``
  val view = proof ``!x. ext_c (ext_h x) = ext_k x``
  val reducer = proof ``!x. ext_g x = ext_h x``
  val tm = ``ext_c (ext_g x)``
  val alias = ``ext_c (ext_h x)``
  val output = ``ext_k x``
  val dummy = S.name_ss "removable" S.empty_ssfrag
  fun base rule = S.++ (S.++ (ext_pure_ss,dummy),
    S.named_rewrites_with_names "originals"
      [({Thy=current_theory (),Name="source"},rule)])
  fun source ss = hd (S.rewrite_source_handles ss)
  fun with_view ss = S.++ (ss,S.rewrite_views [(source ss,view)])
  fun cv ss = S.SIMP_CONV ss []

  (* Exhaust before extracting the other projection, in both directions. *)
  fun late reverse = let
    val ss = with_view (base (Once original))
    val first = if reverse then APIExamples.configured_conv ss []
                else APIExamples.default_conv ss []
    val _ = converted "first projection consumes original allowance"
      first tm output
    val second = if reverse then APIExamples.default_conv ss []
                 else APIExamples.configured_conv ss []
    val _ = converted "late projection cannot revive source" second tm tm
  in converted "late projection cannot revive attached view"
       second alias alias end
  val _ = List.app late [false,true]

  val ss = with_view (base (Ntimes original 2))
  val handle0 = source ss
  val _ = check "view is not a new source handle"
    (length (S.rewrite_source_handles ss) = 1 andalso
     #1 (S.source_rewrite handle0) =
       SOME {Thy=current_theory (),Name="source.1"})
  val _ = converted "view spends first use" (cv ss) alias output
  val replay = S.remove_ssfrags_preserving_controls ["removable"] ss
  val _ = check "preserving replay retains source identity/order"
    (S.same_rewrite_source (handle0,source replay) andalso
     S.rewrite_source_compare (handle0,source replay) = EQUAL)
  val _ = converted "preserving replay spends remaining use"
    (APIExamples.configured_conv replay []) tm output
  val _ = converted "old set shares exhausted replay control" (cv ss) tm tm
  val _ = converted "view shares exhausted replay control"
    (cv replay) alias alias
  val reset = S.remove_ssfrags ["removable"] ss
  val _ = converted "ordinary extension replay explicitly resets quota"
    (cv reset) tm output
  val _ = converted "reset replay still shares source and alias"
    (cv reset) alias output
  val _ = converted "reset replay has exactly declared allowance"
    (cv reset) tm tm
  val active = with_view (base original)
  val suspended = S.suspend_rewrite_sources [source active] active
  val _ = check "suspension removes source and aliases"
    (null (S.rewrite_source_handles suspended))
  val _ = converted "suspended original cannot fire" (cv suspended) tm tm
  val _ = converted "suspended alias cannot fire" (cv suspended) alias alias
  val _ = converted "suspension leaves older set intact" (cv active)
    alias output

  val unrelated = proof ``!x. ext_u x = ext_k x``
  val filtering = S.++ (with_view (base (Ntimes original 2)),
                        S.rewrites [unrelated])
  val _ = converted "source spends quota before preserving filter"
    (cv filtering) tm output
  val filtered = S.filter_rewrites_preserving_controls
    (fn (_,th) => not (same th unrelated)) filtering
  val _ = converted "preserving filter retains remaining alias quota"
    (cv filtered) alias output
  val _ = converted "preserving filter shares exhaustion with old set"
    (cv filtering) tm tm
  val _ = converted "preserving filter removes rejected rule"
    (cv filtered) ``ext_u x`` ``ext_u x``

  (* Getter/source extraction must not rerun the maker or compilation. *)
  val makers = ref 0
  val compilations = ref 0
  val maker = S.SSFRAG
    {name=NONE,convs=[],rewrs=[],congs=[],ac=[],dprocs=[],
     filter=SOME (fn th => (makers := !makers + 1;
                           Cond_rewr.mk_cond_rewrs th))}
  val prepared = S.++ (S.++ (S.empty_ss,maker),S.rewrites [original])
  val maker_count = !makers
  fun watch (2,Trace.LZ_TEXT text) =
        if String.isPrefix "New rewrite: " (text ()) then
          compilations := !compilations + 1 else ()
    | watch _ = ()
  fun getters () =
    (ignore (S.traversedata_for_ss prepared);
     ignore (S.xtraversedata_for_ss prepared);
     ignore (S.rewrite_source_handles prepared);
     ignore (S.rewrite_sources prepared []))
  val listener = "simp-ext inert extraction"
  val _ = Listener.add_listener Trace.trace_hook (listener,watch)
  val _ = Portable.finally
    (fn () => ignore (Listener.remove_listener Trace.trace_hook listener))
    getters ()
  val _ = check "getters do not compile, collect or rerun rewrite makers"
    (maker_count > 0 andalso !makers = maker_count andalso !compilations = 0)

  (* Prepared bundles retain existing event bindings and actual counters. *)
  val bundle = S.prepare_rewrite_bundle ext_pure_ss
    [Ntimes original 2]
  val bundle_source = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val installed = S.install_rewrite_bundle bundle [] ext_pure_ss
  val _ = converted "bundle original spends first use" (cv installed)
    tm output
  val other = S.prepare_rewrite_bundle ext_pure_ss [Once reducer]
  val combined = S.combine_rewrite_bundles [bundle,other]
  val bound = S.install_rewrite_bundle combined [(bundle_source,view)]
    ext_pure_ss
  val _ = check "combined bundle preserves original handle"
    (S.same_rewrite_source
      (bundle_source,hd (#2 (hd (S.rewrite_bundle_rules combined)))) andalso
     length (S.rewrite_bundle_rules combined) = 2)
  val _ = converted "combined view spends remaining original allowance"
    (cv bound) alias output
  val _ = converted "combination did not refresh original control"
    (cv installed) tm tm
  val _ = converted "combined view is now exhausted" (cv bound) alias alias
  val _ = fails "duplicate bundle bindings are rejected"
    (fn HOL_ERR _ => true | _ => false)
    (fn () => S.combine_rewrite_bundles [bundle,bundle])

  (* Child-first changes overlap order, while argument-only normalization
     protects the root and privately resets/restores actual bound controls. *)
  val charges = ref 0
  fun charge () = charges := !charges + 1
  val policy = E.charge_only charge
  val overlap = S.++ (ext_pure_ss,S.rewrites [original,reducer])
  val _ = converted "parent-first takes overlapping root" (cv overlap)
    tm output
  val _ = converted "child-first takes overlapping child first"
    (S.SIMP_CONV_CHILD_FIRST policy overlap []) tm alias
  val _ = check "child-first charges traversal" (!charges > 0)
  val private_ss = S.++ (ext_pure_ss,S.rewrites [Once reducer,c])
  val private = S.prepare_child_first policy private_ss
  val _ = converted "argument normalization preserves reducible root"
    (#arguments private []) tm alias
  val _ = converted "private normalization can be reused"
    (#arguments private []) tm alias
  val _ = converted "private normalization did not spend public quota"
    (cv private_ss) ``ext_g x`` ``ext_h x``
  val _ = converted "public quota is exhausted" (cv private_ss)
    ``ext_g x`` ``ext_g x``
  val _ = converted "private normalization resets exhausted quota locally"
    (#arguments private []) tm alias
  val _ = converted "private normalization restores public exhaustion"
    (cv private_ss) ``ext_g x`` ``ext_g x``
  exception Stop of unit ref
  val stop_token = ref ()
  val seen = ref false
  val abort = S.prepare_child_first_observed
    (fn _ => (seen := true; raise Stop stop_token)) policy private_ss
  val _ = fails "private observer propagates exact exception payload"
    (fn Stop r => Portable.pointer_eq (r,stop_token) | _ => false)
    (fn () => #arguments abort [] tm)
  val _ = check "private observer was called" (!seen)
  val _ = converted "observer failure restores public exhaustion"
    (cv private_ss) ``ext_g x`` ``ext_g x``

  (* Two typed Context slots: same display name, late SF resolution, then
     absent/restored snapshots. The marker theorem itself is untyped. *)
  val _ = scoped (fn () => let
    val absent = Context.snapshot ()
    val name = "same_name_in_two_typed_registries"
    val old_o = proof ``!x. ext_g x = ext_h x``
    val old_e = proof ``!x. ext_g x = ext_k x``
    val new_o = proof ``!x. ext_g x = ext_u x``
    val new_e = proof ``!x. ext_g x = ext_c x``
    val ofrag = simpLib.named_rewrites name [old_o]
    val efrag = S.named_rewrites name [old_e]
    val osf = simpLib.SF ofrag
    val esf = S.SF efrag
    val otac = simpLib.SIMP_TAC pureSimps.pure_ss [osf]
    val etac = S.SIMP_TAC ext_pure_ss [esf]
    val present = Context.snapshot ()
    fun pin label tac expected = let
      val (goals,_) = runtac (VALID tac) ([],``ext_g x``)
    in check label (list_eq goal_eq [([],expected)] goals) end
    fun missing tac = fails "saved SF fails in absent Context"
      (fn HOL_ERR e => String.isSubstring ("No frag called " ^ name)
                        (Feedback.message_of e) | _ => false)
      (fn () => runtac (VALID tac) ([],``ext_g x``))
    val _ = check "ordinary and extension SF share only marker syntax"
      (same osf esf andalso
       Option.isSome (simpLib.lookup_named_frag name) andalso
       Option.isSome (S.lookup_named_frag name))
    val _ = ignore (simpLib.register_frag
      (simpLib.named_rewrites name [new_o]))
    val _ = ignore (S.register_frag (S.named_rewrites name [new_e]))
    val _ = pin "saved ordinary SF uses latest ordinary registration"
      otac ``ext_u x``
    val _ = pin "saved extension SF uses latest extension registration"
      etac ``ext_c x``
    val _ = Context.restore present
    val _ = pin "rewind restores ordinary fragment independently"
      otac ``ext_h x``
    val _ = pin "rewind restores extension fragment independently"
      etac ``ext_k x``
    val _ = Context.restore absent
    val _ = check "rewind removes both typed registrations"
      (not (Option.isSome (simpLib.lookup_named_frag name)) andalso
       not (Option.isSome (S.lookup_named_frag name)))
    val _ = missing otac
    val _ = missing etac
    val _ = Context.restore present
    (* A marker created by either engine resolves solely in its consumer. *)
    val _ = pin "ordinary consumer of extension SF stays ordinary"
      (simpLib.SIMP_TAC pureSimps.pure_ss [esf]) ``ext_h x``
  in pin "extension consumer of ordinary SF stays tracked"
       (S.SIMP_TAC ext_pure_ss [osf]) ``ext_k x`` end)

  (* One tracking extent across the two engines. Nested tracking isolates its
     report and restores the outer slot even after a foreign exception. *)
  val ordinary = simpLib.SIMP_CONV pureSimps.pure_ss [reducer]
  val extension = S.SIMP_CONV ext_pure_ss [original]
  fun ordinary_once () = ordinary ``ext_g x``
  fun extension_once () = extension tm
  val traced = ref ([] : term list)
  fun trace_rewrite (_,Trace.REWRITING (_,tm,_)) = traced := tm :: !traced
    | trace_rewrite _ = ()
  val shared_listener = "simp-ext shared Trace identity"
  val _ = Listener.add_listener Trace.trace_hook
    (shared_listener,trace_rewrite)
  val _ = Portable.finally
    (fn () => ignore (Listener.remove_listener
                       Trace.trace_hook shared_listener))
    (fn () => (ignore (ordinary_once ()); ignore (extension_once ()))) ()
  val _ = check "one Trace listener observes both engines"
    (ListPair.allEq (fn (a,b) => aconv a b)
      (List.rev (!traced),[``ext_g x``,tm]))
  val ((oth,eth),both) = S.track (fn () =>
    (ordinary_once (),extension_once ())) ()
  val _ = check "extension track observes ordinary and extension rewrites"
    (null (hyp oth) andalso null (hyp eth) andalso
     aconv (rhs (concl oth)) ``ext_h x`` andalso
     aconv (rhs (concl eth)) output andalso uses [reducer,original] both)
  (* One extent for both engines: two distinct rules per engine, fired
     alternately, are reported in exactly their firing order, by either
     engine's track. *)
  fun fv n = mk_var (n, ``:bool -> bool``)
  fun rule f = ASSUME (mk_eq (mk_comb (fv f, ``ord_x:bool``), ``ord_y:bool``))
  val eA = rule "ord_ea" val eC = rule "ord_ec"
  val oB = rule "ord_ob" val oD = rule "ord_od"
  fun ext r = S.SIMP_CONV ext_pure_ss [r]
  fun ord r = simpLib.SIMP_CONV pureSimps.pure_ss [r]
  fun lhs_of r = lhs (concl r)
  fun interleaved () =
    (ignore (ext eA (lhs_of eA)); ignore (ord oB (lhs_of oB));
     ignore (ext eC (lhs_of eC)); ignore (ord oD (lhs_of oD)))
  val (_,order_ext) = S.track interleaved ()
  val (_,order_ord) = simpLib.track interleaved ()
  val _ = check "extension track: both engines interleaved, firing order"
    (uses [eA,oB,eC,oD] order_ext)
  val _ = check "ordinary track sees extension rewrites, firing order"
    (uses [eA,oB,eC,oD] order_ord)
  (* A nested extent of either kind takes both engines' rewrites inside it
     and hides them from the enclosing extent. *)
  fun nest outer_track inner_track =
    outer_track (fn () =>
      (ignore (ext eA (lhs_of eA));
       let val (_,inner) = inner_track (fn () =>
             (ignore (ord oB (lhs_of oB)); ignore (ext eC (lhs_of eC)))) ()
       in ignore (ord oD (lhs_of oD)); inner end)) ()
  val (inner,outer) = nest S.track simpLib.track
  val _ = check "simpLib.track nested in simpExtLib.track: inner extent only"
    (uses [oB,eC] inner andalso uses [eA,oD] outer)
  val (inner,outer) = nest simpLib.track S.track
  val _ = check "simpExtLib.track nested in simpLib.track: inner extent only"
    (uses [oB,eC] inner andalso uses [eA,oD] outer)
  val ((_,inner),outer) = simpLib.track (fn () => let
    val _ = ordinary_once ()
    val nested = S.track extension_once ()
    val _ = ordinary_once ()
  in nested end) ()
  val _ = check "nested extension tracking isolates and restores ordinary"
    (uses [original] inner andalso uses [reducer,reducer] outer)
  val ((_,inner),outer) = S.track (fn () => let
    val _ = extension_once ()
    val nested = simpLib.track ordinary_once ()
    val _ = extension_once ()
  in nested end) ()
  val _ = check "nested ordinary tracking isolates and restores extension"
    (uses [reducer] inner andalso uses [original,original] outer)
  val (_,outer) = S.track (fn () =>
    (ignore (extension_once ());
     (ignore (simpLib.track (fn () =>
        (ignore (ordinary_once ()); raise Stop stop_token)) ())
      handle Stop r => if Portable.pointer_eq (r,stop_token) then ()
                       else raise Fail "tracking changed exception payload");
     ignore (ordinary_once ()))) ()
  val _ = check "exception in nested track restores shared outer slot"
    (uses [original,reducer] outer)
in () end)

(* Compiled uses of the migrated B1 names add_relsimp, add_weakener,
   weakener_data and ssf_upd_rewrs, each called qualified from outside.
   A non-equality preorder needs relation-specific subgoal machinery that
   this suite does not load, so add_relsimp is shown with equality only. *)
exception MigState of unit
val _ = let
  val pq = ASSUME ``mig_p = mig_q:bool``
  val qr = ASSUME ``mig_p = mig_r:bool``
  val p = ``mig_p:bool``
  val data : simpExtLib.relsimpdata = {refl=boolTheory.EQ_REFL,
    trans=boolTheory.EQ_TRANS,weakenings=[],subsets=[],rewrs=[pq]}
  val ss = simpExtLib.add_relsimp data ext_pure_ss
  val _ = check ("add_relsimp installs a relsimp reducer whose rule "
                 ^ "rewrites (equality relation)")
    (same (simpExtLib.SIMP_CONV ss [] p) pq)
  val wd : simpExtLib.weakener_data = ([],[],E.lift (Traverse.REDUCER
    {name=SOME "migration weakener",initial=MigState (),
     addcontext=fn (c,_) => c,
     apply=fn _ => fn tm => if aconv tm p then pq else NO_CONV tm}))
  val plain = ext_bool_ss
  val weak = simpExtLib.add_weakener wd plain
  val _ = check "add_weakener: plain simpset leaves mig_p unchanged"
    (same (total (simpExtLib.SIMP_CONV plain []) p) (REFL p))
  val _ = check "add_weakener: its reducer rewrites what plain leaves"
    (same (simpExtLib.SIMP_CONV weak [] p) pq)
  val frag = simpExtLib.ssf_upd_rewrs (fn _ => [(NONE,qr)])
               (simpExtLib.rewrites [pq])
  val _ = check "ssf_upd_rewrs replaces the fragment rules"
    (uses [qr] (simpExtLib.frag_rewrites frag))
  val ss = simpExtLib.++ (ext_pure_ss,frag)
in check "ssf_upd_rewrs fragment rewrites mig_p to mig_r, not mig_q"
     (same (simpExtLib.SIMP_CONV ss [] p) qr) end

val _ = print ("simpExtLib focused checks: " ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
