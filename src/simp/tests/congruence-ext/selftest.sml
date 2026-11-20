(* Focused congExtLib contracts. The extended primitives retain the original
   congproc, travrules and preorder types; ordinary semantics stay separate. *)
structure selftest =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure S = simpExtLib
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val _ = new_theory "congruenceExtContracts"

val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected)
fun terms xs ys = ListPair.allEq (fn (x,y) => aconv x y) (xs,ys)
fun total cv = QCONV (TRY_CONV cv)
fun fails name predicate f =
  check name (case Exn.capture f () of Exn.Exn e => predicate e
                                    | Exn.Res _ => false)
fun holerr (HOL_ERR _) = true | holerr _ = false
fun unchanged UNCHANGED = true | unchanged _ = false
fun eqrefl {Rinst,arg} = REFL arg
fun reject tm = NO_CONV tm
fun run (proc : Opening.congproc) solver depther tm =
  proc equality {solver=solver,depther=depther,freevars=[]} tm
val a = ``ce_a:bool``
val b = ``ce_b:bool``
val c = ``ce_c:bool``
val p = ``ce_p:bool``
val q = ``ce_q:bool``
val f = ``ce_f:bool -> bool``
val g = ``ce_g:bool -> bool``
val ab = ASSUME (mk_eq (a,b))
val bc = ASSUME (mk_eq (b,c))
exception Stop of unit ref

(* y is determined by the first premise and consumed only by a later one.
   The ordinary result classifier must still offer that premise to solver. *)
val chain = prove
  (``(x:bool = y) ==> (g y = z) ==> (f (g x) = f z)``,
   REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [])
val input = mk_comb (f,mk_comb (g,a))
val gbc = ASSUME (mk_eq (mk_comb (g,b),c))
val expected = TRANS (AP_TERM f (AP_TERM g ab)) (AP_TERM f gbc)
val threaded : Opening.congproc = Opening.THREADED_CONGPROC eqrefl chain
val ordinary : Opening.congproc = Opening.CONGPROC eqrefl chain
val rules : Travrules.travrules =
  Travrules.mk_threaded_travrules [Travrules.EQ_preorder] [chain]
val _ = let
  val calls = ref ([] : term list)
  val solvers = ref 0
  fun solver tm = (solvers := !solvers + 1; NO_CONV tm)
  fun depther (ths,rel) tm =
    (check "threaded premise context and relation"
       (null ths andalso same_const rel equality);
     calls := !calls @ [tm];
     if aconv tm a then ab
     else if aconv tm (mk_comb (g,b)) then gbc else NO_CONV tm)
  val saved = run threaded solver depther
  val _ = check "later premise consumes intermediate result, full proof"
    (same (saved input) expected andalso
     terms (!calls) [a,mk_comb (g,b)] andalso !solvers = 0)
  val _ = calls := []
  val _ = check "saved threaded conversion reprocesses premises"
    (same (saved input) expected andalso
     terms (!calls) [a,mk_comb (g,b)] andalso !solvers = 0)
  val _ = calls := []
  val _ = fails "ordinary classifier still rejects intermediate premise"
    holerr (fn () => run ordinary solver depther input)
  val _ = check "ordinary intermediate premise goes only to solver"
    (!solvers = 1 andalso null (!calls))
  val Travrules.TRAVRULES {relations,congprocs,weakenprocs} = rules
  val _ = check "threaded builder returns shared travrules/preorder types"
    (length relations = 1 andalso null weakenprocs andalso
     same (run (hd congprocs) solver depther input) expected)
  val original = Travrules.mk_travrules [Travrules.EQ_preorder] [chain]
  val Travrules.TRAVRULES {congprocs,...} = original
in fails "ordinary builder retains ordinary classification" holerr
     (fn () => run (hd congprocs) solver depther input) end

(* Abstraction-valued subresults leave beta redexes in the rebuilt RHS.
   The original input contains its own redex and must remain the exact LHS.
   Ordinary CONGPROC must NOT acquire the extension's beta cleanup. *)
val _ = let
  val cong = prove
    (``(!x:'a. P x = Q x) ==> ((?x:'a. P x) = (?x:'a. Q x))``,
     DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_REWRITE_TAC [])
  val tm = ``?x:'a. (x = x) /\ ((\y:'a. T) x)``
  val output = ``?x:'a. T``
  val raw_output = ``?x:'a. (\y:'a. T) x``
  fun depther (ths,rel) sub =
    (check "beta fixture has no extra context" (null ths);
     check "beta fixture descends under shared equality"
       (same_const rel equality);
     EQT_INTRO (prove (sub,REWRITE_TAC [])))
  fun proof output = prove (mk_eq (tm,output),REWRITE_TAC [])
  val ext = run (Opening.THREADED_CONGPROC eqrefl cong) reject depther
  val old = run (Opening.CONGPROC eqrefl cong) reject depther
  val th = ext tm
  val _ = check "rebuilt RHS beta cleanup preserves original redex LHS"
    (same th (proof output) andalso aconv (lhs (concl th)) tm)
  val _ = check "ordinary congruence leaves rebuilt RHS beta redex"
    (same (old tm) (proof raw_output) andalso
     not (aconv raw_output output))
in check "saved beta conversion preserves LHS on reuse"
     (same (ext tm) (proof output)) end

(* Failure scopes: HOL_ERR from a depther invokes the supplied reflexivity;
   successful reflexivity yields UNCHANGED. Foreign errors and Interrupt
   at term application are not failed congruence attempts. *)
val _ = let
  val cong = prove (``(x:bool = y) ==> (f x = f y)``,
                    DISCH_TAC THEN ASM_REWRITE_TAC [])
  val side = prove (``~s ==> (x:bool = y) ==> (f x = f y)``,
                    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [])
  val tm = mk_comb (f,a)
  val refls = ref 0
  val depths = ref 0
  val solves = ref 0
  fun refl {Rinst,arg} =
    (refls := !refls + 1;
     check "failed depther reflexivity gets original relation and argument"
       (same_const Rinst equality andalso aconv arg a); REFL arg)
  fun depth _ sub = (depths := !depths + 1; NO_CONV sub)
  fun solver sub = (solves := !solves + 1; NO_CONV sub)
  val cv = run (Opening.THREADED_CONGPROC refl cong) solver depth
  val _ = fails "failed depther and reflexivity report UNCHANGED"
    unchanged (fn () => cv tm)
  val _ = fails "saved failed depther conversion is not poisoned"
    unchanged (fn () => cv tm)
  val _ = check "reflexivity fallback counts, no solver use"
    (!refls = 2 andalso !depths = 2 andalso !solves = 0)
  val _ = fails "failed side condition rejects before descent" holerr
    (fn () => run (Opening.THREADED_CONGPROC refl side)
      solver depth tm)
  val _ = check "side failure does not invoke depther/reflexivity"
    (!solves = 1 andalso !depths = 2 andalso !refls = 2)
  val token = ref ()
  val errors =
    [("foreign",Stop token,
      fn Stop r => Portable.pointer_eq (r,token) | _ => false),
     ("Interrupt",Portable.Interrupt,
      fn Portable.Interrupt => true | _ => false)]
  fun abort (label,error,pred) = let
    val _ = fails ("depther preserves " ^ label) pred
      (fn () => run (Opening.THREADED_CONGPROC refl cong) reject
        (fn _ => fn _ => raise error) tm)
    val _ = fails ("solver preserves " ^ label) pred
      (fn () => run (Opening.THREADED_CONGPROC refl side)
        (fn _ => raise error) depth tm)
    val badrefl = Opening.THREADED_CONGPROC (fn _ => raise error) cong
  in fails ("reflexivity preserves " ^ label) pred
       (fn () => run badrefl reject depth tm) end
  val _ = List.app abort errors
  val _ = fails "failed supplied reflexivity remains a HOL_ERR" holerr
    (fn () => run (Opening.THREADED_CONGPROC
      (fn {arg,...} => NO_CONV arg) cong) reject depth tm)
in () end

(* A weakener uses the enclosing solver context. Ordinary/default traversal
   constructs factories before a root rewrite; configured traversal does
   so lazily. Reuse refreshes factories, not default private contexts. *)
val _ = let
  exception Facts of thm list
  fun exercise configured = let
    val ready = ref false
    val collections = ref 0
    val events = ref ([] : string list)
    val contexts = ref true
    fun event s = events := !events @ [s]
    val weak_rule = ASSUME (mk_imp (p,mk_eq (b,c)))
    val reducer = Traverse.REDUCER
      {name=NONE,initial=Facts [],
       addcontext=fn (Facts old,ths) =>
         (collections := !collections + 1; event "collect";
          Facts (ths @ old)) | _ => raise Fail "lost weakener context",
       apply=fn {context,...} => fn tm =>
         if aconv tm a then (event "root"; ready := true; ab)
         else if aconv tm p then
           (case context of Facts [fact] =>
              (contexts := (!contexts andalso same fact (ASSUME p));
               EQT_INTRO fact)
            | _ => raise Fail "weakener solver lost facts")
         else NO_CONV tm}
    val weakener : Opening.congproc = fn rel =>
      (event "relation"; fn {solver,freevars,...} =>
        let
          val enabled = !ready
          val _ = event "factory"
          val _ = contexts := (!contexts andalso aconv rel equality andalso
                                 terms freevars [p])
        in fn tm =>
          if enabled andalso aconv tm b then
            (event "weaken"; MP weak_rule (solver p))
          else NO_CONV tm end)
    val tr = Travrules.TRAVRULES
      {relations=[Travrules.EQ_preorder],congprocs=[],
       weakenprocs=[weakener]}
    val d : E.traverse_data =
      {limit=NONE,rewriters=[E.lift reducer],dprocs=[],
       relation=equality,travrules=tr}
    val cv = if configured then E.XTRAVERSE (d,E.default_config) [ASSUME p]
      else Traverse.TRAVERSE
        {limit=NONE,rewriters=[reducer],dprocs=[],
         relation=equality,travrules=tr} [ASSUME p]
    val _ = check "weakener collection construction stage"
      (!events = (if configured then [] else ["collect"]))
    val _ = events := []
    val first = cv a
    val proof = TRANS ab (MP weak_rule (ASSUME p))
    val _ = check "weakener first application proof and factory scheduling"
      (same first (if configured then proof else ab) andalso
       !events = (if configured then
          ["collect","relation","root","factory","weaken",
           "factory","factory"]
        else ["relation","factory","root"]))
    val _ = events := []
    (* Leave ready true: even the ordinary eager factory now sees it. *)
    val second = cv a
    val _ = check "saved weakener conversion sees fresh factory context"
      (same second proof andalso !events =
        (if configured then
           ["collect","relation","root","factory","weaken",
            "factory","factory"]
         else ["relation","factory","root","weaken","factory"]))
  in check "weakener enclosing facts and private context lifetime"
       (!contexts andalso !collections = (if configured then 2 else 1)) end
in exercise false; exercise true end

(* The user-facing library must actually select threaded primitives.
   Generic EQ descent cannot supply the implication's local assumption;
   without the new classifier it can perform only the first rewrite. *)
val _ = let
  val cong = prove
    (``(x:bool = y) ==> (p ==> (g y = z)) ==>
       ((p ==> f (g x)) = (p ==> f z))``,
     REPEAT DISCH_TAC THEN ASM_CASES_TAC ``p:bool`` THEN
     RES_TAC THEN ASM_REWRITE_TAC [])
  val conditional = ASSUME (mk_imp (p,concl gbc))
  val tm = mk_imp (p,input)
  val body_proof = TRANS (AP_TERM f (AP_TERM g ab))
    (AP_TERM f (MP conditional (ASSUME p)))
  val imp_cong = prove
    (``(p ==> (x:bool = y)) ==> ((p ==> x) = (p ==> y))``,
     REPEAT STRIP_TAC THEN ASM_CASES_TAC ``p:bool`` THEN
     RES_TAC THEN ASM_REWRITE_TAC [])
  val proof = MATCH_MP imp_cong (DISCH p body_proof)
  val cs = congExtLib.mk_congset
    [congExtLib.CSFRAG {rewrs=[],relations=[],dprocs=[],congs=[cong]}]
  val ss = S.++ (ext_pure_ss,S.rewrites [ab,conditional])
  val saved = congExtLib.CONGRUENCE_SIMP_QCONV equality cs ss []
  val base_data = S.traversedata_for_ss ss
  val contextual = E.XTRAVERSE
    ({limit=NONE,rewriters= #rewriters base_data,dprocs=[],
      relation=equality,travrules=Travrules.mk_threaded_travrules
        [Travrules.EQ_preorder] [cong]},E.default_config) []
  val _ = check "threaded builder supplies later-premise local context"
    (same (contextual tm) proof)
  val _ = check "congExtLib threads results into contextual later premises"
    (same (saved tm) proof)
  val _ = check "saved congExtLib threaded conversion repeats full proof"
    (same (saved tm) proof)
  val _ = check "congExtLib CONGRUENCE_SIMP_RULE rewrites the conclusion"
    (same (congExtLib.CONGRUENCE_SIMP_RULE cs ss [] (ASSUME tm))
          (EQ_MP proof (ASSUME tm)))
  val old_cs = congLib.mk_congset
    [congLib.CSFRAG {rewrs=[],relations=[],dprocs=[],congs=[cong]}]
  val old_ss = simpLib.++ (pureSimps.pure_ss,
                           simpLib.rewrites [ab,conditional])
  val old = congLib.CONGRUENCE_SIMP_QCONV equality old_cs old_ss []
  val old_proof = AP_TERM (mk_comb (implication,p))
    (AP_TERM f (AP_TERM g ab))
  val _ = check "ordinary congLib still lacks intermediate local context"
    (same (old tm) old_proof)
  val direct_ss = S.++ (S.empty_ss,S.rewrites [ab,gbc])
  val cv = E.XTRAVERSE
    ({limit=NONE,rewriters= #rewriters (S.traversedata_for_ss direct_ss),
      dprocs=[],relation=equality,travrules=rules},E.default_config) []
in check "threaded travrules work in configured traversal"
     (same (cv input) expected) end

(* Configured congExtLib refreshes opaque reducer contexts on each saved
   conversion application. Its solver also sees those supplied facts.
   Default congExtLib retains its construction-time reducer context. *)
val _ = let
  exception Facts of thm list
  fun exercise configured = let
    val collections = ref 0
    val applications = ref 0
    val solver_calls = ref 0
    val rule = ASSUME (mk_imp (p,mk_eq (a,b)))
    val fact = ASSUME p
    val reducer = E.CONFIG_REDUCER
      {name=SOME "congruence refresh probe",initial=Facts [],
       addcontext=fn (Facts old,ths) =>
         (collections := !collections + 1; Facts (ths @ old))
         | _ => raise Fail "lost configured context",
       apply=fn {context,solver,...} => fn tm =>
         if aconv tm a then
           (applications := !applications + 1;
            case context of Facts [th] =>
              if same th fact then
                MP rule (if configured then solver [] p else th)
              else raise Fail "changed collected theorem"
            | _ => raise Fail "context accumulated across applications")
         else NO_CONV tm}
    fun solve ({context_thms,...} : E.simp_prover_ctxt) tm =
      (solver_calls := !solver_calls + 1;
       if aconv tm p andalso
          ListPair.allEq (fn (x,y) => same x y) (context_thms,[fact])
       then fact else NO_CONV tm)
    val ss = if configured then
        S.set_unsafe_solvers [{name="context probe",solve=solve}] S.empty_ss
      else S.empty_ss
    val cs = congExtLib.mk_congset
      [congExtLib.CSFRAG
        {rewrs=[],relations=[],dprocs=[reducer],congs=[]}]
    val cv = congExtLib.CONGRUENCE_SIMP_QCONV equality cs ss [fact]
    val _ = check "congExtLib context construction stage"
      (!collections = (if configured then 0 else 1))
    val _ = check "congExtLib first result includes exact proof hypotheses"
      (same (cv a) (MP rule fact) andalso !collections = 1)
    val _ = check "congExtLib saved conversion refreshes only when configured"
      (same (cv a) (MP rule fact) andalso
       !collections = (if configured then 2 else 1))
  in check "congExtLib configured solver uses supplied context on every call"
       (!applications = 2 andalso
        !solver_calls = (if configured then 2 else 0)) end
in exercise false; exercise true end

(* Both primitives emit the same public Trace actions/listener identity on
   ordinary rules; no extension-local trace/control registration exists. *)
val _ = let
  val cong = DISCH (mk_eq (a,b)) (AP_TERM f ab)
  fun capture proc = let
    val seen = ref ([] : (int * Trace.action) list)
    val key = "congruence-ext trace"
    val _ = Listener.add_listener Trace.trace_hook
      (key,fn event => seen := event :: !seen)
    val th = Portable.finally
      (fn () => ignore (Listener.remove_listener Trace.trace_hook key))
      (fn () => run proc reject (fn _ => fn _ => ab)
        (mk_comb (f,a))) ()
  in (th,rev (!seen)) end
  val (old,old_events) = capture
    (Opening.CONGPROC eqrefl cong)
  val (ext,ext_events) = capture
    (Opening.THREADED_CONGPROC eqrefl cong)
  fun action (Trace.OPENING (t,th),Trace.OPENING (u,uh)) =
        aconv t u andalso same (GEN_ALL th) (GEN_ALL uh)
    | action (Trace.PRODUCE (t,n,th),Trace.PRODUCE (u,m,uh)) =
        aconv t u andalso n = m andalso same th uh
    | action _ = false
in
  check "shared Trace actions, levels, proof results and listener identity"
    (same old ext andalso not (null old_events) andalso
     ListPair.allEq (fn ((n,a),(m,b)) => n = m andalso action (a,b))
       (old_events,ext_events))
end

val _ = print ("Congruence extension focused checks: " ^
               Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
