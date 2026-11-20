(* Dynamically used after both ordinary and explicit extension imports. *)
open Parse boolLib;
structure S = simpExtLib;
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt;
fun same th expected = aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected);
fun uses expected actual = ListPair.allEq
  (fn (a,b) => same (SPEC_ALL a) (SPEC_ALL b)) (expected,actual);
fun total cv = QCONV (TRY_CONV cv);
val _ = check "extension preserves original Cond_rewr ref"
  (Portable.pointer_eq (original_stack_limit,Cond_rewr.stack_limit));
val _ = check "extension preserves original simplifier traces and hook"
  (simplifier_traces () = original_simplifier_traces andalso
   Portable.pointer_eq (original_trace_hook,Trace.trace_hook));
val _ = check "extension preserves exact original trace listeners"
  (same_hooks original_trace_listeners
    (Listener.listeners Trace.trace_hook));

(* Saved NONE reads the shared live control, explicit depth stays local.
   Compare entire kernel equalities AND hypotheses, not just changed terms. *)
val _ = let
  val root = ``(audit_depth_f:bool -> bool) audit_x``
  val output = ``audit_y:bool``
  val p = ``audit_p = audit_p'``
  val q = ``audit_q = audit_q'``
  val r0 = ASSUME (boolSyntax.mk_imp (p,boolSyntax.mk_eq (root,output)))
  val r1 = ASSUME (boolSyntax.mk_imp (q,boolSyntax.mk_eq (p,boolSyntax.T)))
  val r2 = ASSUME (boolSyntax.mk_eq (q,boolSyntax.T))
  val expected = MP r0 (EQT_ELIM (MP r1 (EQT_ELIM r2)))
  val ordinary = simpLib.SIMP_CONV pureSimps.pure_ss [r0,r1,r2]
  val ss = S.++ (ext_pure_ss,S.rewrites [r0,r1,r2])
  val live = E.XTRAVERSE (S.xtraversedata_for_ss ss) []
  val configured = E.XTRAVERSE
    (S.xtraversedata_for_ss (S.set_cond_depth 40 ss)) []
  val zero = E.XTRAVERSE
    (S.xtraversedata_for_ss (S.set_cond_depth 0 ss)) []
  val saved = !original_stack_limit
  fun run () =
    (original_stack_limit := 0;
     check "shared zero rejects ordinary and saved live extension condition"
       (same (total ordinary root) (REFL root) andalso
        same (total live root) (REFL root));
     check "explicit extension depth overrides without changing shared ref"
       (same (configured root) expected andalso !original_stack_limit = 0);
     Cond_rewr.stack_limit := 40;
     check "shared mutation enables both saved conversions with full proof"
       (same (ordinary root) expected andalso same (live root) expected);
     check "explicit zero ignores later shared mutation"
       (same (total zero root) (REFL root) andalso !original_stack_limit = 40);
     original_stack_limit := 0;
     check "later shared reduction is live in both engines"
       (same (total ordinary root) (REFL root) andalso
        same (total live root) (REFL root)))
in Portable.finally (fn () => original_stack_limit := saved) run () end;

val ordinary_rule = ASSUME
  ``(audit_of:bool -> bool) audit_x = audit_y``;
val extension_rule = ASSUME
  ``(audit_ef:bool -> bool) audit_x = audit_z``;
val ordinary_term = ``(audit_of:bool -> bool) audit_x``;
val extension_term = ``(audit_ef:bool -> bool) audit_x``;
fun ordinary_once () = simpLib.SIMP_CONV pureSimps.pure_ss
  [ordinary_rule] ordinary_term;
fun extension_once () = S.SIMP_CONV ext_pure_ss
  [extension_rule] extension_term;

(* The one simplifier.trace flag is the level both engines report at.
   The one original listener observes actual proofs from both compilers. *)
val _ = let
  val saved = HOLFlags.current_trace "simplifier.trace"
  val events = ref ([] : (term * thm) list)
  val name = "api-audit shared Trace listener"
  fun watch (_,Trace.REWRITING (_,tm,th)) = events := !events @ [(tm,th)]
    | watch _ = ()
  val _ = Listener.add_listener original_trace_hook (name,watch)
  fun run () =
    (HOLFlags.set_trace "simplifier.trace" 1;
     check "HOLFlags sets the simplifier trace level"
       (HOLFlags.current_trace "simplifier.trace" = 1);
     HOLFlags.set_trace "simplifier.trace" 0;
     check "simplifier.trace is the only simplifier trace"
       (simplifier_traces () = ["trace"] andalso
        HOLFlags.current_trace "simplifier.trace" = 0);
     check "ordinary rewrite has full expected theorem"
       (same (ordinary_once ()) ordinary_rule);
     check "extension rewrite has full expected theorem"
       (same (extension_once ()) extension_rule);
     check "one original Trace listener receives both real rewrites"
       (ListPair.allEq (fn ((tm,th),(u,expected)) =>
          aconv tm u andalso same th expected)
         (!events,[(ordinary_term,ordinary_rule),
                   (extension_term,extension_rule)])))
  fun cleanup () =
    (ignore (Listener.remove_listener original_trace_hook name);
     HOLFlags.set_trace "simplifier.trace" saved)
in Portable.finally cleanup run () end;
val _ = check "shared trace listener cleanup restores exact listener list"
  (same_hooks original_trace_listeners
    (Listener.listeners original_trace_hook));

(* A second distinct rule per engine, so that firing order is observable
   within each engine as well as across them. *)
val ordinary_rule2 = ASSUME
  ``(audit_of2:bool -> bool) audit_x = audit_y``;
val extension_rule2 = ASSUME
  ``(audit_ef2:bool -> bool) audit_x = audit_z``;
fun ordinary_twice () = simpLib.SIMP_CONV pureSimps.pure_ss
  [ordinary_rule2] ``(audit_of2:bool -> bool) audit_x``;
fun extension_twice () = S.SIMP_CONV ext_pure_ss
  [extension_rule2] ``(audit_ef2:bool -> bool) audit_x``;

val _ = let
  val (_,order) = S.track (fn () =>
    (extension_once (); ordinary_once (); extension_twice ();
     ordinary_twice ())) ()
  val _ = check "one extent: interleaved firing order across both engines"
    (uses [extension_rule,ordinary_rule,extension_rule2,ordinary_rule2]
          order)
  val (_,order') = simpLib.track (fn () =>
    (ordinary_twice (); extension_once (); ordinary_once ();
     extension_twice ())) ()
  val _ = check "simpLib.track also sees extension rewrites in order"
    (uses [ordinary_rule2,extension_rule,ordinary_rule,extension_rule2]
          order')
in () end;

val _ = let
  val ((oth,eth),both) = S.track (fn () =>
    (ordinary_once (),extension_once ())) ()
  val _ = check "extension tracking collects both engines' actual proofs"
    (same oth ordinary_rule andalso same eth extension_rule andalso
     uses [ordinary_rule,extension_rule] both)
  val ((_,inner),outer) = simpLib.track (fn () =>
    (ordinary_once (); let val nested = S.track extension_once ()
     in ordinary_once (); nested end)) ()
  val _ = check "nested extension extent isolates then restores ordinary"
    (uses [extension_rule] inner andalso
     uses [ordinary_rule,ordinary_rule] outer)
  val ((_,inner),outer) = S.track (fn () =>
    (extension_once (); let val nested = simpLib.track ordinary_once ()
     in extension_once (); nested end)) ()
  val _ = check "nested ordinary extent isolates then restores extension"
    (uses [ordinary_rule] inner andalso
     uses [extension_rule,extension_rule] outer)
  exception Stop of unit ref
  val token = ref ()
  val (_,outer) = S.track (fn () =>
    (ordinary_once ();
     (ignore (simpLib.track (fn () =>
       (extension_once (); raise Stop token)) ())
      handle Stop r => check "nested tracking preserves exception identity"
        (Portable.pointer_eq (r,token)));
     extension_once ())) ()
  val _ = check "exception restores shared outer tracking slot"
    (uses [ordinary_rule,extension_rule] outer)
  val (_,empty) = simpLib.track (fn () => ()) ()
in check "no stale tracking after nested scopes" (null empty) end;

(* Single-sided names, not two different fragments registered under one
   name.  The extension registry also resolves ordinary names (lifted);
   the ordinary registry never resolves extension names. *)
val _ = let
  val saved = Context.snapshot ()
  val oname = "api_audit_ordinary_only"
  val ename = "api_audit_extension_only"
  fun missing name tac tm =
    check ("opposite SF consumer rejects " ^ name)
      (case Exn.capture (fn () => runtac (VALID tac) ([],tm)) () of
         Exn.Exn (HOL_ERR e) =>
           String.isSubstring ("No frag called " ^ name)
             (Feedback.message_of e)
       | _ => false)
  fun run () = let
    val _ = check "both unique names initially absent in both registries"
      (List.all (fn name =>
         not (Option.isSome (simpLib.lookup_named_frag name)) andalso
         not (Option.isSome (S.lookup_named_frag name))) [oname,ename])
    val ofrag = simpLib.register_frag
      (simpLib.named_rewrites oname [ordinary_rule])
    val osf = simpLib.SF ofrag
    val _ = check "ordinary name resolves, lifted, in extension registry"
      (Option.isSome (simpLib.lookup_named_frag oname) andalso
       (case S.lookup_named_frag oname of
          SOME f => S.frag_name f = SOME oname andalso
                    Portable.pointer_eq (f, S.lift_ssfrag ofrag)
        | NONE => false))
    val efrag = S.register_frag (S.named_rewrites ename [extension_rule])
    val esf = S.SF efrag
    val _ = check "extension-only name absent in opposite registry"
      (Option.isSome (S.lookup_named_frag ename) andalso
       not (Option.isSome (simpLib.lookup_named_frag ename)))
    val _ = missing ename
      (simpLib.SIMP_TAC pureSimps.pure_ss [esf]) extension_term
    val _ = check "failed SF consumption never populates ordinary registry"
      (not (Option.isSome (simpLib.lookup_named_frag ename)))
    fun pin label tac rule tm expected = let
      val assumptions = hyp rule
      val (goals,_) = runtac (VALID tac) (assumptions,tm)
    in check label (list_eq goal_eq [(assumptions,expected)] goals) end
    val _ = pin "ordinary-only SF resolves in its own registry"
      (simpLib.SIMP_TAC pureSimps.pure_ss [osf]) ordinary_rule
      ordinary_term ``audit_y:bool``
    val _ = pin "extension-only SF resolves in its own registry"
      (S.SIMP_TAC ext_pure_ss [esf]) extension_rule
      extension_term ``audit_z:bool``
    val _ = pin "ordinary SF resolves in extension tactics"
      (S.SIMP_TAC ext_pure_ss [osf]) ordinary_rule
      ordinary_term ``audit_y:bool``
  in () end
in Portable.finally (fn () => Context.restore saved) run () end;

val _ = Documentation.run ();
val _ = check "explicit use never initializes split persistence"
  (null (splitLib.named_split_thms ()) andalso
   null (SplitData.current_data ()) andalso no_private ());
val _ = check "ordinary proof still works after all explicit extension use"
  (same (simpLib.SIMP_CONV boolSimps.bool_ss [] ordinary_input)
        ordinary_proof);
