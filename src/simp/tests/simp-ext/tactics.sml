(* Invocation binding, recursive directives and local replay. *)
structure tactics =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure S = simpExtLib
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val saved_context = Context.snapshot ()
val _ = new_theory "simpExtTactics"
val f_def = new_definition ("invocation_f_def",``invocation_f (x:bool) = T``)
val ambient_def = new_definition
  ("invocation_ambient_def",``invocation_ambient (x:bool) = T``)
val checks = ref 0
val validations = ref 0
fun check name ok = (checks := !checks + 1; tprint name;
  if ok then OK () else die name)
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun samegoal ((asl,w),(bsl,v)) =
  list_eq aconv asl bsl andalso aconv w v
fun proof (asl,w) = let
  fun prove w =
    if is_conj w then let val (l,r) = dest_conj w
      in CONJ (prove l) (prove r) end
    else if is_exists w then let val (v,b) = dest_exists w
      in EXISTS (w,T) (prove (subst [v |-> T] b)) end
    else if is_imp_only w then let val (p,q) = dest_imp_only w
      in DISCH p (prove q) end
    else if aconv w T then TRUTH
    else let val (p,q) = dest_disj w
      in if aconv q T then DISJ2 p TRUTH
         else SPEC p boolTheory.EXCLUDED_MIDDLE end
in List.foldl (fn (a,th) => ADD_ASSUM a th) (prove w) asl end
fun tactic name tac goal expected = let
  val (goals,validate) = runtac (VALID tac) goal
  val equal = ListPair.allEq samegoal (goals,expected)
  val _ = if equal then () else List.app
    (fn (asl,w) => print ("actual: " ^
      String.concatWith ", " (map term_to_string asl) ^ " |- " ^
      term_to_string w ^ "\n")) goals
  val _ = check (name ^ ": ordered goals") equal
  val th = validate (map proof goals)
  val _ = validations := !validations + 1
in check (name ^ ": proof and full hypotheses") (same th (proof goal)) end
fun em p = concl (SPEC p boolTheory.EXCLUDED_MIDDLE)
fun result name cv tm expected =
  check name (same (QCONV (TRY_CONV cv) tm) expected)
val cfg = {base={strip=false,elimvars=false,droptrues=false,
                oldestfirst=true},concl_in_fixpoint=true,
           imp_rebuild=true,imp_premises=true}
val policy = E.charge_only (fn () => ())
val unsafe = {safe=false}
val fT = ``(invocation_f:bool -> bool) T``
val rule = SPEC T (GEN_ALL f_def)
val left = ``?x:bool. invocation_f x \/ T``
val input = mk_conj (left,left)
val goal = ([concl rule],input)
fun brancher _ = FIRST [CONJ_TAC,EXISTS_TAC T]
val ss = S.add_looper ("invocation branches",brancher) S.empty_ss
val supplied = [markerLib.NoAsms,Once rule]
(* ALLGOALS evaluates the later branch first, retaining goal order. *)
val expected = [([concl rule],mk_disj (fT,T)),
                ([concl rule],mk_disj (T,T))]
val _ = List.app (fn (name,build) => let
  val saved = build ss supplied
  val _ = tactic (name ^ ": supplied Once across siblings") saved goal expected
in tactic (name ^ ": fresh invocation, same saved tactic") saved goal expected
end) [("parent",S.GEN_SIMP_TAC unsafe),
      ("child",S.GEN_SIMP_TAC_CHILD_FIRST policy unsafe)]

val _ = let
  val p = em ``invocation_global_p:bool``
  val q = em ``invocation_global_q:bool``
  val r = em ``invocation_global_r:bool``
  val g = ([],mk_conj (p,mk_conj (q,r)))
  val base = S.limit 1 (S.add_looper
    ("one global conjunction",fn _ => CONJ_TAC) S.empty_ss)
  val saved = S.GEN_GLOBAL_SIMP_TAC unsafe cfg base []
  val _ = tactic "global fixpoint reentry shares one looper budget"
    saved g [([],p),([],mk_conj (q,r))]
in tactic "saved global invocation gets a fresh looper budget"
  saved g [([],p),([],mk_conj (q,r))] end

val _ = List.app (fn build => List.app (fn control =>
  check "non-global option decoding retains ReqD failure"
    (case Exn.capture (fn () => runtac
       (build S.empty_ss [S.ReqD control])
       ([],em ``invocation_option_p:bool``)) () of
         Exn.Exn (HOL_ERR e) =>
           Feedback.top_function_of e = "REQUIRE_DECREASE_TAC"
       | _ => false))
  [markerLib.NoAsms,Once (markerLib.IgnAsm [QUOTE "invocation_unused"])])
  [S.GEN_SIMP_TAC unsafe,S.GEN_SIMP_TAC_CHILD_FIRST policy unsafe]

(* Pretactics precede directive resolution/binding, including failures.
   Keep label lookup at its earlier option-decoding stage. *)
val _ = let
  val missing = "invocation_missing_frag"
  val args = [markerSyntax.Abbr [QUOTE "invocation_missing_abbr"],
              markerLib.FRAG missing]
  val g = ([],em ``invocation_staging_p:bool``)
  val configured = S.add_looper ("force configured path",fn _ => NO_TAC)
    S.empty_ss
  fun error tac = case Exn.capture (fn () => runtac tac g) () of
      Exn.Exn (HOL_ERR e) => SOME e
    | _ => NONE
  val _ = List.app (fn build => let
    val saved = build configured args
    fun run () = check "Abbr failure precedes FRAG on every saved invocation"
      (case error saved of
           SOME e => String.isSubstring "No assumption of the form"
                       (Feedback.message_of e)
         | NONE => false)
    val _ = run ()
    val _ = run ()
    val _ = check "FRAG still resolves when pretactics succeed"
      (case error (build configured [markerLib.FRAG missing]) of
           SOME e => Feedback.top_function_of e = "process_tags" andalso
                     String.isSubstring missing (Feedback.message_of e)
         | NONE => false)
  in check "label lookup still precedes Abbr and FRAG"
    (case error (build configured
       (markerSyntax.L "invocation_missing_label" :: args)) of
         SOME e => String.isSubstring "No assumption with label"
                     (Feedback.message_of e)
       | NONE => false)
  end) [S.GEN_SIMP_TAC unsafe,S.GEN_SIMP_TAC_CHILD_FIRST policy unsafe,
         S.ASM_SIMP_TAC]
  val bound = ref 0
  exception PrematureBinding
  fun bind _ _ = (bound := !bound + 1; raise PrematureBinding)
  val _ = check "failed pretactic never invokes the binding callback"
    (case error (markerLib.process_taclist_then_bind {arg=args} bind) of
         SOME e => String.isSubstring "No assumption of the form"
                     (Feedback.message_of e) andalso !bound = 0
       | NONE => false)
  val _ = check "successful pretactic invokes binding exactly once"
    (case Exn.capture (fn () => runtac
       (markerLib.process_taclist_then_bind {arg=[]} bind) g) () of
         Exn.Exn PrematureBinding => !bound = 1
       | _ => false)
in () end

(* Multiple bound hypotheses on a real rule are not content directives.
   Preserve the selected allowance and every other hypothesis verbatim. *)
val _ = List.app (fn nested => let
  val (_,limit_before) = BoundedRewrites.DEST_BOUNDED nested
  val (_,prepared) = S.prepare_rewrite_arguments S.empty_ss [nested]
  val _ = check "nested genuine rewrite survives preparation verbatim"
    (length prepared = 1 andalso same (hd prepared) nested)
  val (plain,after) = BoundedRewrites.DEST_BOUNDED (hd prepared)
  val _ = check "nested genuine rewrite retains the initially selected bound"
    (limit_before = after)
  val installed = S.++ (S.empty_ss,S.rewrites prepared)
  val cv = S.SIMP_CONV installed []
  val _ = List.app (fn _ => result "nested allowance spends selected control"
    cv fT plain) (List.tabulate (limit_before,I))
in result "nested allowance stays exhausted on saved conversion"
  cv fT (REFL fT) end)
  [Once (Ntimes rule 2),Ntimes (Once rule) 2,
   Ntimes (Ntimes rule 3) 2,Once (Ntimes rule 0)]

(* A bounded supplied fact is an untagged fact for final solvers, even if
   a maker drops it from the rewrite net. *)
val _ = let
  val fact = SPEC ``invocation_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val seen = ref false
  val calls = ref 0
  val drop = S.SSFRAG {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],
    congs=[],filter=SOME (fn _ => (calls := !calls + 1; []))}
  fun solve {context_thms,...} tm = let
    val th = valOf (List.find (fn th => same th fact) context_thms)
    val _ = seen := true
  in if aconv tm (concl th) then th else NO_CONV tm end
  val base = S.add_unsafe_solver {name="untagged supplied",solve=solve}
    (S.++ (S.empty_ss,drop))
  val _ = tactic "bounded supplied solver facts are untagged"
    (S.GEN_SIMP_TAC unsafe base [Once fact]) ([],concl fact) []
in check "supplied rule compiled once, solver saw plain theorem"
  (!seen andalso !calls = 1) end

val _ = let
  fun quantified binder i =
    let val p = mk_var ("reconcile_" ^ Int.toString i, bool --> bool)
    in mk_forall (binder, mk_comb (p,binder)) end
  val x = mk_var ("x", bool)
  val y = mk_var ("y", bool)
  val asms = List.tabulate (128,quantified x) @ [quantified y 127]
  val fact = SPEC (mk_var ("reconcile_goal", bool)) boolTheory.EXCLUDED_MIDDLE
  val required = List.tabulate (64,fn i => quantified y (i + 64))
  val good = List.foldl (fn (h,th) => ADD_ASSUM h th) fact required
  val bad = ADD_ASSUM (mk_var ("reconcile_missing", bool)) good
  val calls = ref []
  fun solver name th =
    {name=name, solve=fn _ => fn _ => (calls := name :: !calls; th)}
  val ss = S.set_safe_solvers [solver "missing" bad,solver "matched" good]
    S.empty_ss
  val _ = tactic "solver reconciles alpha-equivalent assumptions"
    (S.GEN_SIMP_TAC {safe=true} ss [markerLib.NoAsms]) (asms,concl fact) []
in check "missing hypothesis falls through to the next solver"
  (!calls = ["matched","missing"]) end

(* Nested wrappers qualify directives, not rewrites of marker propositions.
   Requirements on content directives are stripped before interpretation. *)
val _ = let
  val saved = Context.snapshot ()
  fun run () = let
    val frag = S.register_frag (S.name_ss "invocation nested"
      (S.looper_ss ("nested conjunction",fn _ => CONJ_TAC)))
    val target = em ``invocation_p:bool``
    val g = ([],mk_conj (target,target))
    val args = [S.Req0 (Once (Ntimes (S.SF frag) 2))]
    val _ = tactic "nested requirements/bound around SF execute looper"
      (S.GEN_SIMP_TAC unsafe S.empty_ss args) g
      [([],target),([],target)]
    val _ = check "nested ReqD retains its requirement failure"
      (case Exn.capture (fn () => runtac
         (S.GEN_SIMP_TAC unsafe S.empty_ss
           [S.Req0 (S.ReqD (Once (S.SF frag)))]) g) () of
           Exn.Exn (HOL_ERR e) =>
             Feedback.top_function_of e = "REQUIRE_DECREASE_TAC"
         | _ => false)
    val _ = tactic "bounded SF via extension alias executes looper"
      (S.SIMP_TAC S.empty_ss [Once (S.SF frag)]) g
      [([],target),([],target)]
    val p = ``invocation_policy_p:bool``
    val goal = ([p],em p)
    val _ = List.app (fn control =>
      tactic "wrapped NoAsms/IgnAsm retains unbound global policy"
        (S.GEN_GLOBAL_SIMP_TAC unsafe cfg ext_pure_ss [control])
        goal [goal])
      [Once markerLib.NoAsms,S.Req0 markerLib.NoAsms,
       Once (markerLib.IgnAsm [QUOTE "invocation_policy_p"])]
    val label = markerLib.MK_LABEL ("invocation label",rule)
    val labelled = ([concl label],em fT)
    val _ = tactic "bounded label reference is resolved before binding"
      (S.GEN_SIMP_TAC unsafe S.empty_ss
        [Once (markerSyntax.L "invocation label")]) labelled
      [([concl label],em T)]
    val abbreviation = markerSyntax.mk_abbrev ("invocation_alias",T)
    val g = ([abbreviation],em ``invocation_alias:bool``)
    val _ = tactic "bounded abbreviation pretactic executes once"
      (S.GEN_SIMP_TAC unsafe S.empty_ss
        [Once (markerSyntax.Abbr [QUOTE "invocation_alias"])]) g [([],em T)]
  in () end
in Portable.finally (fn () => Context.restore saved) run () end

val _ = let
  val split = splitLib.type_split_of ``:bool``
  val directive = Once (Ntimes (S.Split split) 2)
  val input = ``(if invocation_b then invocation_p else invocation_q) \/ T``
  val output = ``(invocation_b ==> invocation_p \/ T) /\
                (~invocation_b ==> invocation_q \/ T)``
  val _ = tactic "bounded Split is executed as an extension directive"
    (S.GEN_SIMP_TAC unsafe S.empty_ss [directive]) ([],input) [([],output)]
  val markers = [S.Split split,S.ExclX "case:unregistered-case"]
  val seen = ref []
  val registrations = ThmSetData.all_set_types ()
  val attribute = ThmAttribute.is_attribute "split"
  val target = em ``invocation_generic_p:bool``
  val _ = tactic "generic marker tactic forwards extension markers inertly"
    (markerLib.process_taclist_then {arg=markers}
      (fn ths => (seen := ths; ALL_TAC))) ([],target) [([],target)]
  val _ = check "generic tactic passes recognised extension markers on"
    (List.all markerLib.is_directive markers andalso
     ListPair.allEq (fn (a,b) => same a b) (!seen,markers))
in check "extension/generic tactic execution creates no split registrations"
  (registrations = ThmSetData.all_set_types () andalso
   attribute = ThmAttribute.is_attribute "split") end

(* Both the bundle and independent ambient controls must stay spent after
   a local marker removes another fragment. A looper receives exactly the
   adjusted installed object, not an earlier reset copy. *)
val _ = List.app (fn count => let
  val makers = ref 0
  val collect = ref 0
  exception Context
  val reducer = E.lift (Traverse.REDUCER
    {name=NONE,initial=Context,
     addcontext=fn (c,_) => (collect := !collect + 1; c),
     apply=fn _ => NO_CONV})
  val maker = S.SSFRAG {name=NONE,convs=[],rewrs=[],ac=[],congs=[],
    dprocs=[reducer],filter=SOME (fn rw => (makers := !makers + 1; [rw]))}
  val dummy = S.name_ss "invocation remove" S.empty_ssfrag
  val ambient = SPEC T (GEN_ALL ambient_def)
  val input_a = lhs (concl ambient)
  val base = S.++ (S.++ (S.++ (S.empty_ss,maker),dummy),
    S.rewrites [Once ambient])
  val bundle = S.prepare_rewrite_bundle base [Ntimes rule count]
  val source = hd (#2 (hd (S.rewrite_bundle_rules bundle)))
  val installed = S.install_rewrite_bundle bundle [(source,rule)] base
  val cv = S.SIMP_CONV installed []
  val _ = result "spend ambient before local replay" cv input_a ambient
  val _ = result "partially spend installed bundle" cv fT rule
  val loop_seen = ref false
  fun probe ss g = let
    val cv = S.SIMP_CONV ss []
    val a = QCONV cv input_a
    val b = QCONV cv fT
    val _ = loop_seen := (same a (REFL input_a) andalso same b (REFL fT))
  in NO_TAC g end
  val installed = S.add_looper ("probe installed controls",probe) installed
  val marker = concl (S.ExclSF "invocation remove")
  val g = ([marker],mk_conj (mk_disj (input_a,T),mk_disj (fT,T)))
  val expected = if count = 1 then g
    else ([marker],mk_conj (mk_disj (input_a,T),mk_disj (T,T)))
  val maker_start = !makers
  val before_collect = !collect
  val tac = S.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND policy unsafe cfg
    installed bundle []
  val recompiles = ref 0
  fun watch (2,Trace.LZ_TEXT text) =
        if String.isPrefix "New rewrite: " (text ()) andalso
           String.isSubstring "invocation_f" (text ())
        then recompiles := !recompiles + 1 else ()
    | watch _ = ()
  val listener = "bound local replay"
  val _ = Listener.add_listener Trace.trace_hook (listener,watch)
  val _ = Portable.finally
    (fn () => ignore (Listener.remove_listener Trace.trace_hook listener))
    (fn () => tactic "bound local replay preserves ambient/bundle controls"
      tac g [expected]) ()
  val _ = check "installed bundle and attached view never recompile locally"
    (!recompiles = 0)
  val _ = check "local looper sees the shared exhausted controls" (!loop_seen)
  (* One ambient rule is remade per local removal; bundle shapes never
     enter the maker. The former second repair replay doubled these calls. *)
  val _ = print ("REPLAY_SCHEDULE count=" ^ Int.toString count ^
    " makers=" ^ Int.toString (!makers - maker_start) ^
    " collectors=" ^ Int.toString (!collect - before_collect) ^ "\n")
  val _ = check "local replay maker/collector schedule is single, not repair"
    (!makers - maker_start = count andalso
     !collect - before_collect = 3 * count)
  val _ = result "saved ambient conversion remains exhausted" cv input_a
    (REFL input_a)
  val _ = result "saved bundle conversion shares local consumption" cv fT
    (REFL fT)
in () end) [1,2]

val _ = print ("EXTENSION_TACTICS_OK checks=" ^
  Int.toString (!checks) ^ " validations=" ^ Int.toString (!validations) ^
  "\n")
val _ = Context.restore saved_context
val _ = OS.Process.exit OS.Process.success

end (* struct *)
