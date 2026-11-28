(* Authoritative tracked installation and inert projections. *)
structure tracked =
struct

open HolKernel Parse boolLib boolSyntax testutils
val _ = simpExtLib.empty_ss
val _ = TraverseExt.default_config
structure S = simpExtLib
structure E = TraverseExt
val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun result name cv input expected = let
  val actual = QCONV (TRY_CONV cv) input
  val ok = same actual expected
  val _ = if ok then () else
    (print ("Actual: " ^ thm_to_string actual ^ "\n");
     print ("Expected: " ^ thm_to_string expected ^ "\n"))
in check name ok end
fun projection configured ss =
  if configured then E.XTRAVERSE (S.xtraversedata_for_ss ss) []
  else E.TRAVERSE (S.traversedata_for_ss ss) []
fun handles ss = S.rewrite_source_handles ss
fun stable (a,b) = S.same_rewrite_source (a,b) andalso
  S.rewrite_source_compare (a,b) = EQUAL
fun distinct hs = List.all (fn a =>
  length (List.filter (fn b => S.rewrite_source_compare (a,b) = EQUAL)
                      hs) = 1) hs
val rule = ASSUME ``(tracked_f:bool -> bool) x = y``
val other = ASSUME ``(tracked_g:bool -> bool) x = z``
val conjunct_rule = CONJUNCT1 (CONJ rule other)
val conjunct_other = CONJUNCT2 (CONJ rule other)
val input = lhs (concl rule)
val input2 = lhs (concl other)
val dummy = S.name_ss "tracked-removable" S.empty_ssfrag
fun frag filter ac rewrs dprocs = S.SSFRAG
  {name=NONE,convs=[],rewrs=map (pair NONE) rewrs,ac=ac,filter=filter,
   congs=[],dprocs=dprocs}
fun seed maker = S.++ (S.empty_ss,frag (SOME maker) [] [] [])
fun maker rw = Cond_rewr.mk_cond_rewrs rw
fun base th = S.++ (S.++ (seed maker,dummy),
  S.named_rewrites_with_names "tracked-rules"
    [({Thy="bool",Name="tracked-source"},th),
     ({Thy="bool",Name="tracked-other"},other)])
fun source ss = hd (handles ss)

(* A trace listener runs independently of trace display settings. Getters
   are tested while makers and collectors would raise if called. *)
val compiling = ref 0
fun watch (2,Trace.LZ_TEXT text) =
      if String.isPrefix "New rewrite: " (text ()) then
        compiling := !compiling + 1 else ()
  | watch _ = ()
fun watched f =
  (Listener.add_listener Trace.trace_hook ("tracked-compiler",watch);
   Portable.finally
     (fn () => ignore
       (Listener.remove_listener Trace.trace_hook "tracked-compiler")) f ())

(* Partial use, exhaustion and late extraction, in both directions, across
   actual persistent filtering and control-preserving history reconstruction.
   Equal source handles alone do not establish this: old saved conversions
   must see consumption by the new set, and vice versa. *)
val operations =
  [("unchanged",I),
   ("literal filtering",fn ss => S.-* (ss,["tracked-other"])),
   ("preserving filter",S.filter_rewrites_preserving_controls
      (fn (_,th) => not (same th other))),
   ("preserving replay",S.remove_ssfrags_preserving_controls
      ["tracked-removable"])]
val _ = List.app (fn reverse => List.app (fn (name,modify) => let
  val ss = base (Ntimes rule 3)
  val original = source ss
  val first = projection reverse ss
  val _ = result (name ^ ": first use") first input rule
  val derived = modify ss
  val _ = check (name ^ ": stable origin and statement")
    (stable (original,source derived))
  val _ = watched (fn () => let
    val saved = !compiling
    val second = projection (not reverse) derived
    val _ = check (name ^ ": late extraction is compilation-free")
      (!compiling = saved)
    val _ = result (name ^ ": late projection spends second use")
      second input rule
    val _ = result (name ^ ": old saved projection spends last use")
      first input rule
    val _ = result (name ^ ": new projection shares exhaustion")
      second input (REFL input)
    val late = projection reverse derived
  in result (name ^ ": extraction after exhaustion stays spent")
       late input (REFL input) end)
in () end) operations) [false,true]
val _ = List.app (fn reverse => let
  val ss = base (Once rule)
  val first = projection reverse ss
  val _ = result "first projection exhausts before other is extracted"
    first input rule
  val late = projection (not reverse) ss
in result "late opposite projection cannot refresh allowance"
     late input (REFL input) end) [false,true]
val _ = List.app (fn reverse => let
  val ss = base (Ntimes rule 2)
  val first = projection reverse ss
  val second = projection (not reverse) ss
  val _ = result "both projections extracted before first application"
    first input rule
  val _ = result "pre-extracted opposite projection shares partial quota"
    second input rule
in result "pre-extracted first projection sees exhaustion"
     first input (REFL input) end) [false,true]
val _ = List.app (fn reverse => let
  val ss = base (Ntimes rule 0)
in result "initial zero is an installed exhausted control"
     (projection reverse ss) input (REFL input) end) [false,true]

(* Duplicate occurrences and repeated installations have independent event
   identities and allowances. Conjuncts instead share one actual control. *)
val _ = let
  val fragment = S.rewrites [Once rule,Once rule]
  val ss = S.++ (S.++ (seed maker,fragment),fragment)
  val hs = handles ss
  val _ = check "four duplicate slots/installations have distinct identities"
    (length hs = 4 andalso distinct hs)
  val left = projection false ss
  val right = projection true ss
  val _ = List.app (fn cv => result "duplicate consumes its own allowance"
    cv input rule) [left,right,left,right]
in result "duplicates have exactly four uses, not eight"
     right input (REFL input) end
val _ = List.app (fn reverse => let
  val ss = S.++ (seed maker,S.rewrites [Once (CONJ rule other)])
  val hs = handles ss
  val _ = check "compiled conjunct identities are distinct"
    (length hs = 2 andalso distinct hs)
  val first = projection reverse ss
  val _ = result "first conjunct spends shared parent control"
    first input conjunct_rule
  val late = projection (not reverse) ss
in result "late projection of sibling conjunct shares exhausted control"
     late input2 (REFL input2) end) [false,true]
val _ = let
  val ss = S.++ (seed maker,S.ac_ss [(CONJ_COMM,CONJ_ASSOC)])
in check "AC components have three distinct source identities"
     (length (handles ss) = 3 andalso distinct (handles ss)) end

(* Every maker runs before every conversion; ordinary tags are all decoded
   before AC derivation or makers. Existing dprocs collect tagged originals,
   in order, after conversion compilation; new dprocs are already primed. *)
val _ = let
  exception Payload of thm list
  exception Forbidden
  val events = ref ([] : string list)
  val blocked = ref false
  val collected = ref ([] : thm list)
  val compile_stage = ref 0
  fun event e = if !blocked then raise Forbidden else events := !events @ [e]
  fun mk rw = (event "maker"; maker rw)
  fun proc name = E.lift (Traverse.REDUCER
    {name=SOME name,initial=Payload [],
     addcontext=fn (Payload previous,ths) =>
       (event name; collected := ths; compile_stage := !compiling;
        Payload (previous @ ths))
       | _ => raise Forbidden,
     apply=fn _ => NO_CONV})
  val ss = S.++ (seed mk,S.dproc_ss (proc "old collector"))
  val tagged = Ntimes rule 2
  val ss = watched (fn () => let
    val compile_count = !compiling
    val ss = S.++ (ss,frag NONE [] [tagged,other]
                            [proc "new collector"])
    val _ = check "installation compiles each accepted native rule once"
      (!compiling = compile_count + 2 andalso
       !compile_stage = !compiling)
  in ss end)
  val _ = check "all makers precede existing collector; new one not primed"
    (!events = ["maker","maker","old collector"] andalso
     ListPair.allEq (uncurry same) (!collected,[tagged,other]))
  val hs = handles ss
  val _ = blocked := true
  val _ = watched (fn () => let
    val compile_count = !compiling
    val _ = ignore (S.traversedata_for_ss ss)
    val _ = ignore (S.xtraversedata_for_ss ss)
    val _ = ignore (S.traverseconfig_for_ss ss)
    val (inventory,supplied) = S.rewrite_sources ss [tagged]
  in check "all getters inert; inventory is retained; supplied bound untagged"
       (!compiling = compile_count andalso Portable.pointer_eq (hs,handles ss)
        andalso length inventory = 2 andalso
        ListPair.allEq (uncurry same) (supplied,[rule])) end)
  val _ = blocked := false
  val malformed = ADD_ASSUM
    (mk_comb (bounded_tm,mk_var ("not_a_number",bool))) rule
  val _ = events := []
  val _ = check "malformed ordinary tag precedes AC/makers/collectors"
    (case Exn.capture
       (fn () => S.++ (ss,frag NONE [(CONJ_COMM,CONJ_ASSOC)]
                              [rule,malformed] [])) () of
         Exn.Exn Option => null (!events) | _ => false)
  val _ = blocked := true
in check "inventory getter rejects directives without installation/replay"
     (case Exn.capture (fn () => S.rewrite_sources ss [S.ExclSF "x"]) () of
          Exn.Exn (HOL_ERR _) => true | _ => false) end
val _ = let
  val events = ref ([] : string list)
  fun mk rw = (events := !events @ ["maker"]; [rw])
  val ss = seed mk
  fun observe (2,Trace.LZ_TEXT text) =
        if String.isPrefix "New rewrite: " (text ()) then
          events := !events @ ["conversion"] else ()
    | observe _ = ()
  val _ = Listener.add_listener Trace.trace_hook ("tracked-order",observe)
  val _ = Portable.finally
    (fn () => ignore
      (Listener.remove_listener Trace.trace_hook "tracked-order"))
    (fn () => ignore (S.++
      (ss,frag NONE [(CONJ_COMM,CONJ_ASSOC)] [rule,other] []))) ()
in check "AC plus ordinary: all five makers before all conversions"
     (!events = List.tabulate (5,K "maker") @
                List.tabulate (5,K "conversion")) end

val _ = let
  exception MakerStop
  exception Private
  val calls = ref 0
  val collects = ref 0
  fun mk rw = (calls := !calls + 1;
    if !calls = 2 then raise MakerStop else [rw])
  val opaque = E.lift (Traverse.REDUCER
    {name=SOME "staging",initial=Private,
     addcontext=fn (ctxt,_) => (collects := !collects + 1; ctxt),
     apply=fn _ => NO_CONV})
  val ss = S.++ (seed mk,S.dproc_ss opaque)
in watched (fn () => let
     val compile_count = !compiling
     val stopped = case Exn.capture
       (fn () => S.++ (ss,S.rewrites [rule,other])) () of
           Exn.Exn MakerStop => true | _ => false
   in check "throwing maker precedes all compilation and collector calls"
        (stopped andalso !calls = 2 andalso !collects = 0 andalso
         !compiling = compile_count) end) end

(* Rebinding cached prepared shapes must not call the compiler again, even
   when reset replay needs a new counter group. No aliases here: views/bundle
   dependency matrices are covered separately by their exhaustive suites. *)
val _ = List.app (fn reverse => let
  val calls = ref 0
  fun mk rw = (calls := !calls + 1; maker rw)
  val initial = S.++ (seed mk,dummy)
  val bundle = S.prepare_rewrite_bundle initial
    [Ntimes (CONJ rule other) 2]
  val ss = S.install_rewrite_bundle bundle [] initial
  val hs = handles ss
  val old = projection reverse ss
  val _ = result "prepared original spends first use"
    old input conjunct_rule
  val before_makers = !calls
  val (preserved,reset) = watched (fn () => let
    val before_compile = !compiling
    val preserved = S.remove_ssfrags_preserving_controls
      ["tracked-removable"] ss
    val reset = S.remove_ssfrags ["tracked-removable"] ss
    val _ = check "cached replay never prepares matcher or calls maker"
      (!calls = before_makers andalso !compiling = before_compile)
  in (preserved,reset) end)
  val _ = check "cached replay retains both conjunct identities"
    (ListPair.allEq stable (hs,handles preserved) andalso
     ListPair.allEq stable (hs,handles reset))
  val _ = result "preserved sibling spends last original use"
    (projection (not reverse) preserved) input2 conjunct_other
  val _ = result "old saved prepared projection sees exhaustion"
    old input (REFL input)
  val _ = result "late cached preserving extraction stays exhausted"
    (projection reverse preserved) input (REFL input)
  val _ = result "explicit reset has fresh allowance" (projection reverse reset)
    input conjunct_rule
  val _ = result "reset siblings still share a control"
    (projection (not reverse) reset) input2 conjunct_other
in result "reset group has two uses total"
     (projection reverse reset) input (REFL input) end) [false,true]

(* Control-preserving argument construction must not reconstruct unrelated
   history twice. Direct exclusions do not reconstruct at all. *)
val _ = let
  val calls = ref 0
  val collects = ref 0
  exception Private
  val opaque = E.lift (Traverse.REDUCER
    {name=SOME "opaque",initial=Private,
     addcontext=fn (ctxt,_) => (collects := !collects + 1; ctxt),
     apply=fn _ => NO_CONV})
  fun mk rw = (calls := !calls + 1; maker rw)
  val ss = S.++ (S.++ (S.++ (seed mk,S.dproc_ss opaque),dummy),
                       S.rewrites [Ntimes rule 2])
  val cv = projection false ss
  val _ = result "argument construction begins with partially spent quota"
    cv input rule
  val counts0 = (!calls,!collects)
  val (direct,_) = S.prepare_rewrite_arguments ss [S.Excl "absent"]
  (* Marker processing installs the original Cong/AC fragment once; that
     empty fragment primes existing opaque collectors with the empty list. *)
  val _ = check "direct exclusion causes no history recompilation"
    (!calls = #1 counts0 andalso !collects = #2 counts0 + 1)
  val counts1 = (!calls,!collects)
  val (removed,_) = S.prepare_rewrite_arguments direct
    [S.ExclSF "tracked-removable"]
  val _ = check "fragment directive reconstructs once, not twice"
    (!calls = #1 counts1 + 1 andalso !collects = #2 counts1 + 3)
  val _ = result "argument removal retains remaining actual allowance"
    (projection true removed) input rule
in result "original sees argument replay exhaustion"
     cv input (REFL input) end

(* A changed maker output has the same origin, but not a compatible source.
   It must not inherit a spent quota from an old statement. *)
val _ = let
  val changed = ref false
  fun mk (th,control) = [(if !changed then other else th,control)]
  val ss = S.++ (S.++ (seed mk,dummy),S.rewrites [Once rule])
  val old = source ss
  val _ = result "old statement exhausts" (projection false ss) input rule
  val _ = changed := true
  val replay = S.remove_ssfrags_preserving_controls
    ["tracked-removable"] ss
  val current = source replay
  val _ = check "same origin does not imply compatible changed statement"
    (S.rewrite_source_compare (old,current) = EQUAL andalso
     not (S.same_rewrite_source (old,current)))
in result "incompatible new statement has its newly declared allowance"
     (projection true replay) input2 other end

(* Rebinding is control binding, not matcher preparation, and takes the
   actual supplied zero/partially spent ref rather than its declared quota. *)
val _ = let
  val r = ref 2
  val p = Cond_rewrExt.prepare ("tracked rebind",rule) (BOUNDED r)
  val legacy = #legacy (Cond_rewrExt.runners p) (fn _ => ASSUME) []
  val _ = result "prepared matcher uses original actual ref" legacy input rule
  val zero = ref 0
  val rebound = Cond_rewrExt.rebind p (BOUNDED zero)
  val config = {solver=fn _ => ASSUME,stack=[],cond_depth=NONE,
                term_ord=Cond_rewr.ac_term_ord}
  val cv = #configured (Cond_rewrExt.runners rebound) config
  val _ = result "rebind to actual zero cannot refresh it"
    cv input (REFL input)
  val _ = zero := 1
  val _ = result "rebound matcher observes actual ref refill" cv input rule
  val _ = check "rebound runner decrements only supplied control"
    (!zero = 0 andalso !r = 1)
  val _ = check "cannot rebind bounded shape as unbounded"
    (case Exn.capture (fn () => Cond_rewrExt.rebind p UNBOUNDED) () of
         Exn.Exn (HOL_ERR _) => true | _ => false)
  val unbounded = Cond_rewrExt.prepare ("unbounded",rule) UNBOUNDED
in check "cannot rebind unbounded shape as bounded"
     (case Exn.capture
       (fn () => Cond_rewrExt.rebind unbounded (BOUNDED r)) () of
          Exn.Exn (HOL_ERR _) => !r = 1 | _ => false) end

(* Private derivation enumerates installed net controls, including aliases
   with no public source handle of their own. Restore partial/exhausted
   caller state after successful, failing, interrupted and nested scopes. *)
val alias_rule = ASSUME ``(tracked_alias:bool -> bool) x = y``
val alias_input = lhs (concl alias_rule)
val _ = List.app (fn spent => let
  exception Stop of unit ref
  val token = ref ()
  fun instance () = let
    val ss = S.++ (seed maker,S.rewrites [Ntimes rule 2])
    val ss = S.++ (ss,S.rewrite_views [(source ss,alias_rule)])
    val cv = projection false ss
    val _ = List.app (fn _ => result "spend before private scope"
      cv input rule) (List.tabulate (spent,I))
  in (ss,cv) end
  fun remaining cv =
    (List.app (fn _ => result "private scope restores partial allowance"
       cv input rule) (List.tabulate (2-spent,I));
     result "private scope restores final exhaustion" cv input (REFL input))
  val (ss,cv) = instance ()
  val _ = check "alias has no separate native inventory handle"
    (length (handles ss) = 1)
  val prepared = S.prepare_child_first (E.charge_only (fn () => ())) ss
  val _ = result "private alias works independently of spent caller quota"
    (#normalize prepared []) alias_input alias_rule
  val _ = remaining cv
  fun failure (name,error,predicate) = let
    val (ss,cv) = instance ()
    fun visit tm = if aconv tm (rhs (concl rule)) then raise error else ()
    val prepared = S.prepare_child_first_observed visit
      (E.charge_only (fn () => ())) ss
    val _ = check ("private scope propagates " ^ name)
      (case Exn.capture (#normalize prepared []) alias_input of
           Exn.Exn e => predicate e | _ => false)
  in remaining cv end
  val _ = List.app failure
    [("HOL_ERR",mk_HOL_ERR "tracked" "observer" "stop",
       fn HOL_ERR e => Feedback.message_of e = "stop"
        | _ => false),
     ("foreign exception",Stop token,
       fn Stop r => Portable.pointer_eq (r,token) | _ => false),
     ("Interrupt",Portable.Interrupt,
       fn Portable.Interrupt => true | _ => false)]
  val (ss,cv) = instance ()
  val inner = S.prepare_child_first (E.charge_only (fn () => ())) ss
  val nested = ref false
  fun visit tm = if aconv tm alias_input andalso not (!nested) then
    (nested := true;
     result "nested private normalization uses its own declared scope"
       (#normalize inner []) input rule) else ()
  val outer = S.prepare_child_first_observed visit
    (E.charge_only (fn () => ())) ss
  val _ = result "outer scope continues after nested normalization"
    (#normalize outer []) alias_input alias_rule
  val _ = remaining cv
  val (ss,cv) = instance ()
  val inner = S.prepare_child_first (E.charge_only (fn () => ())) ss
  fun cutoff () =
    (result "charge callback enters nested private scope"
       (#normalize inner []) input rule;
     raise Stop token)
  val outer = S.prepare_child_first (E.charge_only cutoff) ss
  val _ = check "nested charge cutoff retains foreign exception identity"
    (case Exn.capture (#normalize outer []) alias_input of
         Exn.Exn (Stop r) => Portable.pointer_eq (r,token) | _ => false)
in remaining cv end) [1,2]

val _ = print ("TRACKED_COMPILER_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
