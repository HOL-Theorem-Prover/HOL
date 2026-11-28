(* Private child-first derivation, not invocation simplification. *)
structure derivation =
struct

open HolKernel Parse boolLib boolSyntax testutils
val _ = simpExtLib.empty_ss
val _ = TraverseExt.default_config
structure S = simpExtLib
structure E = TraverseExt
val checks = ref 0
val failures = ref ([] : string list)
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK ()
   else (failures := name :: !failures; print "FAILED\n"))
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun result name cv input expected =
  case Exn.capture cv input of
      Exn.Res actual =>
        (if same actual expected then () else
           (print ("Actual: " ^ thm_to_string actual ^ "\n");
            print ("Expected: " ^ thm_to_string expected ^ "\n"));
         check name (same actual expected))
    | Exn.Exn e =>
        (print (General.exnMessage e ^ "\n"); check name false)
fun throws name predicate f =
  check name (case Exn.capture f () of
                  Exn.Exn e => predicate e | _ => false)
fun projection ss = E.XTRAVERSE (S.xtraversedata_for_ss ss) []
fun total cv = QCONV (TRY_CONV cv)
fun source ss = hd (S.rewrite_source_handles ss)
fun seed maker = S.++ (S.empty_ss,S.SSFRAG
  {name=NONE,convs=[],rewrs=[],ac=[],filter=SOME maker,
   congs=[],dprocs=[]})
val policy = E.charge_only (fn () => ())
val rule = ASSUME ``(derivation_f:bool -> bool) x = y``
val other = ASSUME ``(derivation_g:bool -> bool) x = z``
val alias = ASSUME ``(derivation_alias:bool -> bool) x = y``
val input = lhs (concl rule)
val output = rhs (concl rule)
val head = ``derivation_pair:bool -> bool -> bool``
fun pairterm a b = list_mk_comb (head,[a,b])
fun pairproof a b = MK_COMB (AP_TERM head a,b)
val pair_input = pairterm input input
val pair_expected = pairproof rule rule
exception Stop of unit ref
val token = ref ()
fun exact (Stop r) = Portable.pointer_eq (r,token) | exact _ = false
val holpayload = Feedback.mk_hol_error
  "derivation" "callback" locn.Loc_Unknown "derivation payload"
val holerror = HOL_ERR holpayload
fun exact_hol (HOL_ERR e) =
      Portable.pointer_eq (e,holpayload) andalso
      Feedback.top_structure_of e = "derivation" andalso
      Feedback.top_function_of e = "callback" andalso
      Feedback.message_of e = "derivation payload"
  | exact_hol _ = false
val errors = [("foreign",Stop token,exact),
              ("HOL_ERR",holerror,exact_hol),
              ("Interrupt",Portable.Interrupt,
               fn Portable.Interrupt => true | _ => false)]
type prepared = {normalize : thm list -> conv,
                 arguments : thm list -> conv,
                 may_reduce_arguments : term -> bool}
val entries = [("normalize",fn (p : prepared) => #normalize p),
               ("arguments",fn (p : prepared) => #arguments p)]

(* Capture the real installed native counter through the public maker API.
   It witnesses that failure/reentry occurs AFTER a bounded rewrite, not
   merely while entering a scope which has yet to do any work. *)
fun fixture kind spent = let
  val counters = ref ([] : int ref list)
  fun maker (rw as (_,control)) =
    (case control of BOUNDED r => counters := r :: !counters | _ => ();
     Cond_rewr.mk_cond_rewrs rw)
  val base = seed maker
  val conjuncts = kind = "conjunct" orelse kind = "bundle/conjunct/alias"
  val theorem = if conjuncts then CONJ rule other else rule
  val ss =
    if kind = "bundle" orelse kind = "bundle/conjunct/alias" then
      S.install_rewrite_bundle
        (S.prepare_rewrite_bundle base [Ntimes theorem 2]) [] base
    else S.++ (base,S.rewrites [Ntimes theorem 2])
  val ss =
    if kind = "alias" orelse kind = "bundle/conjunct/alias" then
      S.++ (ss,S.rewrite_views [(source ss,alias)])
    else ss
  val a = if conjuncts then CONJUNCT1 theorem else rule
  val b = if kind = "alias" orelse kind = "bundle/conjunct/alias" then
            alias
          else if conjuncts then CONJUNCT2 theorem else rule
  val caller = total (projection ss)
  val _ = List.app (fn _ => result (kind ^ ": caller consumption")
    caller input a) (List.tabulate (spent,I))
in (ss,caller,hd (!counters),a,b) end
fun remaining label spent caller proof =
  (List.app (fn _ => result (label ^ ": caller remainder")
     caller input proof) (List.tabulate (2-spent,I));
   result (label ^ ": caller exhausted") caller input (REFL input))

(* Each saved conversion receives declared quotas afresh, while aliases
   and sibling conjuncts still share ONE quota inside that private scope. *)
val _ = List.app (fn kind => List.app (fn spent => let
  val (ss,caller,counter,a,b) = fixture kind spent
  val prepared = S.prepare_child_first policy ss
  val tm = pairterm (lhs (concl a)) (lhs (concl b))
  val expected = pairproof a b
  val triple = pairterm tm (lhs (concl a))
  val two_only = MK_COMB (AP_TERM head expected,REFL (lhs (concl a)))
  val _ = List.app (fn (entry,select) => let
    val saved = select prepared []
    val label = kind ^ "/" ^ entry
    val _ = List.app (fn _ =>
      result (label ^ ": saved reuse has private quota") saved tm expected)
      [1,2]
    val _ = result (label ^ ": private group has exactly two uses")
      saved triple two_only
  in check (label ^ ": actual caller counter restored")
       (!counter = 2-spent) end) entries
in remaining kind spent caller a end) [1,2])
  ["native","bundle","alias","conjunct","bundle/conjunct/alias"]

(* Unlike normalize, arguments must leave a reducible root intact. *)
val _ = let
  val root = ASSUME (mk_eq (pairterm output output,``derivation_done:bool``))
  val (ss,caller,_,_,_) = fixture "native" 2
  val ss = S.++ (ss,S.rewrites [root])
  val prepared = S.prepare_child_first policy ss
  val _ = result "normalize rewrites root after its children"
    (#normalize prepared []) pair_input (TRANS pair_expected root)
  val _ = result "arguments preserves root after its children"
    (#arguments prepared []) pair_input pair_expected
in result "root distinction does not refill caller"
     caller input (REFL input) end

(* Same prepared object, including its protected-callback state, reenters
   itself. The inner failure is caught; the outer still has its second use.
   Repeat the saved outer conversion to detect stale failure state. *)
val _ = List.app (fn spent => List.app (fn (error_name,inner_error) =>
  List.app (fn (entry,select) => let
    val (ss,caller,counter,_,_) = fixture "native" spent
    val depth = ref 0
    val entered = ref false
    val consumed = ref false
    val saved = ref (REFL : conv)
    fun visit tm =
      if aconv tm output then
        if !depth = 1 then
          (consumed := (!consumed orelse !counter = 1);
           case inner_error of NONE => () | SOME (error,_) => raise error)
        else if not (!entered) then let
          val _ = entered := true
          val _ = check "outer consumed before same-object reentry"
            (!counter = 1)
          val _ = depth := 1
          val _ =
            case inner_error of
                SOME (_,predicate) =>
                  throws (error_name ^ ": caught nested failure identity")
                    predicate (fn () => (!saved) pair_input)
              | NONE => result "same-object nested success" (!saved)
                          pair_input pair_expected
          val _ = depth := 0
        in check "nested scope restores partially consumed outer counter"
             (!counter = 1) end
        else ()
      else ()
    val prepared = S.prepare_child_first_observed visit policy ss
    val _ = saved := select prepared []
    val _ = List.app (fn _ =>
      (entered := false; consumed := false;
       result (entry ^ ": outer succeeds after nested call")
         (!saved) pair_input pair_expected;
       check "nested call actually consumed bounded allowance" (!consumed);
       check "reentrant saved conversion restores caller counter"
         (!counter = 2-spent))) [1,2]
  in remaining "reentry" spent caller rule end) entries)
    (("success",NONE) :: map (fn (name,error,predicate) =>
      (name,SOME (error,predicate))) errors)) [1,2]

(* All three callbacks fail only after the first child has consumed a
   bounded rewrite. keep_abstraction is deliberately inside a later
   application, where ordinary conversion failure combinators could swallow
   HOL_ERR or replace Interrupt/foreign exceptions with a wrapper error. *)
val hold = ``(derivation_hold:(bool -> bool) -> bool)
               (\u:bool. derivation_h u)``
val failure_input = pairterm input hold
val _ = List.app (fn spent => List.app (fn (entry,select) =>
  List.app (fn route => List.app (fn (error_name,error,predicate) => let
    val (ss,caller,counter,_,_) = fixture "native" spent
    val consumed = ref false
    val enabled = ref true
    val armed = ref false
    fun stop () =
      (consumed := !counter = 1; raise error)
    fun visit tm =
      if aconv tm output then armed := true
      else if route = "observer" andalso !enabled andalso
              !armed andalso aconv tm hold then stop ()
      else ()
    fun charge () =
      if route = "charge" andalso !enabled andalso !armed then stop ()
      else ()
    fun keep tm =
      if route = "keep_abstraction" andalso !enabled andalso
         aconv tm hold andalso !counter = 1 then stop ()
      else false
    val prepared = S.prepare_child_first_observed visit
      {charge=charge,keep_abstraction=keep} ss
    val saved = select prepared []
    val label = entry ^ "/" ^ route ^ "/" ^ error_name
    val _ = throws (label ^ ": exact exception after consumption") predicate
      (fn () => saved failure_input)
    val _ = check (label ^ ": failure was after bounded consumption")
      (!consumed)
    val _ = check (label ^ ": restores actual caller counter")
      (!counter = 2-spent)
    val _ = enabled := false
    val _ = result (label ^ ": saved object recovers after exception")
      saved pair_input pair_expected
  in remaining label spent caller rule end) errors)
    ["observer","charge","keep_abstraction"]) entries) [1,2]

(* Descent can CREATE an eta candidate. Its policy check then happens in
   the configured native ETA entry, before the traversal's next head pass.
   The preparation-level guard must preserve that abort across tryfind. *)
val _ = List.app (fn (entry,select) =>
  List.app (fn (error_name,error,predicate) => let
    val (ss,caller,counter,_,_) = fixture "native" 2
    val eta_rule = ASSUME
      ``(derivation_eta_input:bool -> bool) = (\u:bool. derivation_h u)``
    val late = ``derivation_hold (derivation_eta_input:bool -> bool):bool``
    val eta = S.SSFRAG
      {name=NONE,rewrs=[],ac=[],congs=[],dprocs=[],filter=NONE,
       convs=[{name="ETA_CONV (eta reduction)",trace=0,
               key=SOME ([],hold),conv=K (K (RAND_CONV ETA_CONV))},
              {name="create eta argument",trace=0,
               key=SOME ([],lhs (concl eta_rule)),
               conv=K (K (REWR_CONV eta_rule))}]}
    val ss = S.++ (ss,eta)
    val consumed = ref false
    val enabled = ref true
    val calls = ref 0
    fun keep tm =
      if !enabled andalso aconv tm hold then
        (calls := !calls + 1; consumed := !counter = 1; raise error)
      else false
    val prepared = S.prepare_child_first
      {charge=fn () => (),keep_abstraction=keep} ss
    val saved = select prepared []
    val label = entry ^ "/native ETA/" ^ error_name
    val _ = throws (label ^ ": exact abort after descent") predicate
      (fn () => saved (pairterm input late))
    val _ = check (label ^ ": bounded rewrite precedes policy abort")
      (!consumed andalso !calls = 1)
    val _ = check (label ^ ": caller counter restored") (!counter = 0)
    val _ = enabled := false
    val _ = result (label ^ ": saved conversion recovers")
      saved pair_input pair_expected
  in result (label ^ ": caller still exhausted")
       caller input (REFL input) end) errors) entries

(* Direct child-first conversion shares its policy guard with native ETA,
   including a candidate CREATED by descent. Unlike derivation this spends
   actual caller quotas: an abort must not secretly refill them. *)
val _ = List.app (fn spent =>
  List.app (fn (error_name,error,predicate) => let
    val (ss,caller,counter,_,_) = fixture "native" spent
    val eta_rule = ASSUME
      ``(derivation_direct_eta:bool -> bool) = (\u:bool. derivation_h u)``
    val late = ``derivation_hold (derivation_direct_eta:bool -> bool):bool``
    val eta = S.SSFRAG
      {name=NONE,rewrs=[],ac=[],congs=[],dprocs=[],filter=NONE,
       convs=[{name="ETA_CONV (eta reduction)",trace=0,
               key=SOME ([],hold),conv=K (K (RAND_CONV ETA_CONV))},
              {name="create eta argument",trace=0,
               key=SOME ([],lhs (concl eta_rule)),
               conv=K (K (REWR_CONV eta_rule))}]}
    val ss = S.++ (ss,eta)
    val enabled = ref true
    val calls = ref 0
    fun keep tm =
      if aconv tm hold then
        (calls := !calls + 1; if !enabled then raise error else false)
      else false
    val saved = S.SIMP_CONV_CHILD_FIRST
      {charge=fn () => (),keep_abstraction=keep} ss []
    val label = "direct/native ETA/" ^ error_name
    val _ = check (label ^ ": saving is inert") (!calls = 0)
    val _ = throws (label ^ ": exact abort after descent") predicate
      (fn () => saved (pairterm input late))
    val _ = check (label ^ ": one policy call, caller use stays spent")
      (!calls = 1 andalso !counter = 1-spent)
    val _ = enabled := false
    val expected = TRANS (AP_TERM (rator late) eta_rule)
                         (RAND_CONV ETA_CONV hold)
    val _ = result (label ^ ": saved direct conversion recovers")
      saved late expected
    val _ = check (label ^ ": recovery does not refill caller")
      (!counter = 1-spent)
  in remaining label (spent+1) caller rule end) errors) [0,1]

(* A remembered abort is insufficient: tryfind must not invoke ANY later
   conversion before rethrowing. Exercise the late native ETA check with
   failing and successful fallbacks, all routes, and saved reuse. Ordinary
   conversion errors must still reject candidates rather than abort search. *)
val _ = List.app (fn route =>
  List.app (fn (error_name,error,predicate) => let
    val eta_rule = ASSUME
      ``(derivation_dispatch_eta:bool -> bool) = (\u:bool. derivation_h u)``
    val late = ``derivation_hold (derivation_dispatch_eta:bool -> bool):bool``
    val enabled = ref true
    val reject = ref false
    val aborted = ref false
    val calls = ref 0
    val post_abort_calls = ref 0
    val fallbacks = ref ([] : string list)
    fun fallback name cv tm =
      (if !aborted then post_abort_calls := !post_abort_calls + 1 else ();
       if aconv tm hold then fallbacks := !fallbacks @ [name] else ();
       cv tm)
    fun eta tm = if !reject then raise error else RAND_CONV ETA_CONV tm
    val frag = S.SSFRAG
      {name=NONE,rewrs=[],ac=[],congs=[],dprocs=[],filter=NONE,
       convs=[{name="ETA_CONV (eta reduction)",trace=0,
               key=SOME ([],hold),conv=K (K eta)},
              {name="failed fallback",trace=0,key=SOME ([],hold),
               conv=K (K (fallback "failed" NO_CONV))},
              {name="successful fallback",trace=0,key=SOME ([],hold),
               conv=K (K (fallback "success" (RAND_CONV ETA_CONV)))},
              {name="create dispatch eta argument",trace=0,
               key=SOME ([],lhs (concl eta_rule)),
               conv=K (K (REWR_CONV eta_rule))}]}
    val ss = S.++ (S.empty_ss,frag)
    fun keep tm =
      if aconv tm hold then
        (calls := !calls + 1;
         if !enabled then (aborted := true; raise error) else false)
      else false
    val policy = {charge=fn () => (),keep_abstraction=keep}
    val prepared = S.prepare_child_first policy ss
    val observed = S.prepare_child_first_observed (fn _ => ()) policy ss
    val cv = case route of
        "direct" => S.SIMP_CONV_CHILD_FIRST policy ss []
      | "normalize" => #normalize prepared []
      | "observed" => #normalize observed []
      | _ => #arguments prepared []
    val outer = ``derivation_outer:bool -> bool``
    val tm = if route = "arguments" then mk_comb (outer,late) else late
    val expected = TRANS (AP_TERM (rator late) eta_rule)
                         (RAND_CONV ETA_CONV hold)
    val expected = if route = "arguments" then AP_TERM outer expected
                   else expected
    val label = route ^ "/dispatch/" ^ error_name
    val _ = check (label ^ ": construction is inert")
      (!calls = 0 andalso null (!fallbacks))
    val _ = List.app (fn _ =>
      (calls := 0; aborted := false; post_abort_calls := 0; fallbacks := [];
       throws (label ^ ": exact policy abort") predicate (fn () => cv tm);
       check (label ^ ": one late policy abort") (!aborted andalso !calls = 1);
       check (label ^ ": no post-abort candidate callback")
         (!post_abort_calls = 0 andalso null (!fallbacks)))) [1,2]
    val _ = enabled := false
    val _ = aborted := false
    val _ = result (label ^ ": saved conversion recovers") cv tm expected
    val _ = check (label ^ ": recovery needs no fallback") (null (!fallbacks))
    val _ = reject := true
    val _ = fallbacks := []
    val _ = case error of
        Portable.Interrupt =>
          (throws (label ^ ": ordinary Interrupt still propagates")
             predicate (fn () => cv tm);
           check (label ^ ": Interrupt invokes no fallback")
             (null (!fallbacks)))
      | _ =>
          (result (label ^ ": ordinary errors still try later candidates")
             cv tm expected;
           check (label ^ ": both ordinary fallback callbacks execute")
             (!fallbacks = ["failed","success"]))
  in () end) errors) ["direct","normalize","observed","arguments"]

(* The native ETA search may be nested inside another candidate or solver
   pipeline. Rethrowing at the inner boundary alone is insufficient: outer
   search and solver continuation must consult the SAME abort state. *)
val _ = List.app (fn route => List.app (fn nesting =>
  List.app (fn (error_name,error,predicate) => let
    val eta_rule = ASSUME
      ``(derivation_nested_eta:bool -> bool) = (\u:bool. derivation_h u)``
    val late = ``derivation_hold (derivation_nested_eta:bool -> bool):bool``
    val trigger = ``derivation_nested_trigger:bool``
    val aborted = ref false
    val enabled = ref true
    val calls = ref 0
    val post_calls = ref ([] : string list)
    fun callback name =
      if !aborted then post_calls := name :: !post_calls else ()
    fun invoke recurse tm =
      if aconv tm trigger then (ignore (recurse late); NO_CONV tm)
      else NO_CONV tm
    val recurse_conv =
      {name="nested solver conversion",trace=0,key=SOME ([],trigger),
       conv=fn solver => fn stack => invoke (solver stack)}
    val fallback =
      {name="outer fallback",trace=0,key=SOME ([],trigger),
       conv=K (K (fn tm => (callback "outer candidate"; NO_CONV tm)))}
    val eta = S.SSFRAG
      {name=NONE,ac=[],congs=[],dprocs=[],filter=NONE,
       rewrs=if nesting = "condition" then
               [(NONE,DISCH late (ASSUME (mk_eq (trigger,``T``))))]
             else [],
       convs=(if nesting = "conversion" then [recurse_conv] else []) @
             [fallback,
              {name="ETA_CONV (eta reduction)",trace=0,
               key=SOME ([],hold),conv=K (K (RAND_CONV ETA_CONV))},
              {name="create nested eta argument",trace=0,
               key=SOME ([],lhs (concl eta_rule)),
               conv=K (K (REWR_CONV eta_rule))}]}
    exception Context
    fun reducer name apply = E.CONFIG_REDUCER
      {name=SOME name,initial=Context,addcontext= #1,
       apply=fn {conv,...} => fn tm =>
         (callback name; apply (conv []) tm)}
    val ss = S.++ (S.empty_ss,eta)
    val ss =
      if nesting = "reducer" then
        S.++ (S.++ (ss,S.dproc_ss (reducer "nested reducer" invoke)),
          S.dproc_ss (reducer "later reducer" (fn _ => NO_CONV)))
      else ss
    val ss = S.set_unsafe_solvers
      [{name="later solver",solve=fn _ => fn _ =>
          (callback "solver continuation"; raise holerror)}] ss
    fun keep tm =
      if !enabled andalso aconv tm hold then
        (calls := !calls + 1; aborted := true; raise error)
      else false
    val policy = {charge=fn () => (),keep_abstraction=keep}
    val prepared = S.prepare_child_first policy ss
    val observed = S.prepare_child_first_observed
      (fn _ => callback "observer") policy ss
    val cv = case route of
        "direct" => S.SIMP_CONV_CHILD_FIRST policy ss []
      | "normalize" => #normalize prepared []
      | "observed" => #normalize observed []
      | _ => #arguments prepared []
    val tm = if route = "arguments" then
               mk_comb (``derivation_outer:bool -> bool``,trigger)
             else trigger
    val label = route ^ "/nested " ^ nesting ^ "/" ^ error_name
    val _ = throws (label ^ ": exact late policy abort") predicate
      (fn () => cv tm)
    val _ = check (label ^ ": policy reached once") (!calls = 1)
    val _ = check (label ^ ": no enclosing callback after abort")
      (null (!post_calls))
    val _ = enabled := false
    val _ = aborted := false
  in result (label ^ ": saved conversion recovers")
       (total cv) ``T`` (REFL ``T``)
  end) errors) ["conversion","condition","reducer"])
  ["direct","normalize","observed","arguments"]

(* A nonopaque indexed pretest calls keep_abstraction without traversal.
   Its abort state must be private too, but it must NEVER reset quotas,
   charge work or observe terms. Exercise both recovery orders. *)
val _ = List.app (fn observed => List.app (fn spent =>
  List.app (fn (error_name,error,predicate) => let
    val (ss,caller,counter,_,_) = fixture "native" spent
    val calls = ref 0
    val charges = ref 0
    val visits = ref 0
    val enabled = ref true
    fun keep _ =
      (calls := !calls + 1;
       check "pretest sees actual caller allowance" (!counter = 2-spent);
       if !enabled then raise error else false)
    val policy = {charge=fn () => charges := !charges + 1,
                  keep_abstraction=keep}
    val prepared =
      if observed then S.prepare_child_first_observed
        (fn _ => visits := !visits + 1) policy ss
      else S.prepare_child_first policy ss
    val pretest = #may_reduce_arguments prepared
    val label = "pretest/" ^ Bool.toString observed ^ "/" ^ error_name
    val _ = check (label ^ ": preparing is inert")
      (!calls = 0 andalso !charges = 0 andalso !visits = 0)
    val _ = throws (label ^ ": exact policy abort") predicate
      (fn () => pretest hold)
    val _ = enabled := false
    val _ = check (label ^ ": pretest recovers immediately")
      (case Exn.capture pretest hold of Exn.Res b => b | _ => false)
    val _ = check (label ^ ": callback retries, no traversal or quota work")
      (!calls = 2 andalso !charges = 0 andalso !visits = 0 andalso
       !counter = 2-spent)
    val _ = enabled := true
    val _ = throws (label ^ ": reused pretest can abort again") predicate
      (fn () => pretest hold)
    val _ = enabled := false
    val _ = result (label ^ ": normalization after pretest abort")
      (#normalize prepared []) ``T`` (REFL ``T``)
    val _ = check (label ^ ": no latent failure after normalization")
      (case Exn.capture pretest hold of Exn.Res b => b | _ => false)
    val _ = check (label ^ ": all four pretests called policy") (!calls = 4)
  in remaining label spent caller rule end) errors) [1,2]) [false,true]

(* A pretest nested inside a derivation callback gets its own abort scope,
   but keeps the partially consumed enclosing quota, not declared quotas.
   Catching its exception must not poison the successful outer derivation. *)
val _ = List.app (fn (entry,select) =>
  List.app (fn (error_name,error,predicate) => let
    val (ss,caller,counter,_,_) = fixture "native" 2
    val pretest = ref (fn (_ : term) => false)
    val nested = ref false
    fun visit tm =
      if aconv tm output andalso not (!nested) then
        (nested := true;
         throws ("nested pretest/" ^ error_name ^ ": original error")
           predicate (fn () => (!pretest) hold);
         check "nested pretest preserves partially spent outer quota"
           (!counter = 1))
      else ()
    fun keep tm = if aconv tm hold then raise error else false
    val prepared = S.prepare_child_first_observed visit
      {charge=fn () => (),keep_abstraction=keep} ss
    val _ = pretest := #may_reduce_arguments prepared
    val saved = select prepared []
    val _ = result (entry ^ ": outer recovers from caught pretest error")
      saved pair_input pair_expected
    val _ = check "nested pretest ran inside derivation" (!nested)
    val _ = check "outer caller stays exhausted after nested pretest"
      (!counter = 0)
  in result "nested pretest did not refill caller" caller input (REFL input)
  end) errors) entries

(* Observing failed conditions and unchanged inputs adds dependencies, not
   work charges or rewrite consumption. Compare full proofs, not RHS only. *)
val _ = List.app (fn (entry,select) => let
  val condition = ``derivation_unsolved:bool``
  val calls = ref 0
  val seen = ref ([] : term list)
  val counters = ref ([] : int ref list)
  fun maker (rw as (_,BOUNDED r)) =
        (counters := r :: !counters; Cond_rewr.mk_cond_rewrs rw)
    | maker rw = Cond_rewr.mk_cond_rewrs rw
  val ss = S.++ (seed maker,S.rewrites [Once (DISCH condition rule)])
  val counter = hd (!counters)
  val charged = E.charge_only (fn () => calls := !calls + 1)
  val plain = select (S.prepare_child_first charged ss) []
  val observed = select (S.prepare_child_first_observed
    (fn tm => seen := tm :: !seen) charged ss) []
  val tm = pairterm input ``derivation_unchanged:bool``
  val _ = result (entry ^ ": failed condition remains unchanged")
    plain tm (REFL tm)
  val plain_calls = !calls
  val _ = calls := 0
  val _ = result (entry ^ ": observation preserves complete proof")
    observed tm (REFL tm)
  val _ = check (entry ^ ": observation adds no charges")
    (!calls = plain_calls andalso plain_calls > 0)
  fun saw tm = List.exists (aconv tm) (!seen)
  val _ = check (entry ^ ": failed premise remains a dependency")
    (saw condition)
  val _ = check (entry ^ ": unchanged child remains a dependency")
    (saw ``derivation_unchanged:bool``)
in check (entry ^ ": failed condition did not charge bounded quota")
     (!counter = 1) end) entries

(* A rejected conditional candidate cannot spend the allowance shared by
   its sibling. Inspect that fact INSIDE one private scope, not merely the
   restored public counter after the scope. *)
val _ = List.app (fn (entry,select) => let
  val premise = ``derivation_rejected:bool``
  val conjunction = CONJ (DISCH premise rule) other
  val ss = S.++ (seed Cond_rewr.mk_cond_rewrs,
                  S.rewrites [Once conjunction])
  val sibling = CONJUNCT2 conjunction
  val caller = total (projection ss)
  val prepared = S.prepare_child_first policy ss
  val tm = pairterm input (lhs (concl other))
  val expected = pairproof (REFL input) sibling
  val saved = select prepared []
  val _ = result (entry ^ ": rejected candidate leaves private sibling use")
    saved tm expected
  val _ = result (entry ^ ": private sibling did not spend caller use")
    caller (lhs (concl other)) sibling
  val _ = result (entry ^ ": private sibling works after caller exhaustion")
    saved tm expected
in result (entry ^ ": sibling scope restored caller exhaustion")
     caller (lhs (concl other)) (REFL (lhs (concl other))) end) entries

(* Ordinary lifted callbacks are opaque but run within the same private
   scope. Reducer, solver, and collector failures are triggered from a
   later child AFTER the native rule; no asynchronous interrupt machinery.
   HOL_ERR is ordinary candidate rejection here, not an abort callback. *)
val _ = List.app (fn (entry,select) => List.app (fn route =>
  List.app (fn (error_name,error,predicate) => let
    exception Context
    val (ss,caller,counter,_,_) = fixture "native" 2
    val consumed = ref false
    val enabled = ref false
    val marker =
      if route = "collector" then
        ``if derivation_context then derivation_callback
          else derivation_callback':bool``
      else ``derivation_callback:bool``
    val fact = ASSUME ``derivation_context:bool``
    fun stop () = (consumed := !counter = 1; raise error)
    val reducer = E.lift (Traverse.REDUCER
      {name=SOME "derivation opaque",initial=Context,
       addcontext=fn (ctxt,ths) =>
         if route = "collector" andalso !enabled andalso
            List.exists (fn th => same th fact) ths then stop () else ctxt,
       apply=fn {conv,solver,...} => fn tm =>
         if !enabled andalso aconv tm marker then
           if route = "solver" then
             solver [] ``derivation_callback_condition:bool``
           else stop ()
         else NO_CONV tm})
    val ss = S.++ (S.++ (ss,S.dproc_ss reducer),S.SSFRAG
      {name=NONE,convs=[],rewrs=[],ac=[],filter=NONE,dprocs=[],
       congs=if route = "collector" then [boolTheory.COND_CONG] else []})
      |> S.set_unsafe_solvers
           [{name="derivation throwing solver",solve=fn _ => fn _ =>
               if !enabled then stop () else raise holerror}]
    val prepared = S.prepare_child_first policy ss
    val saved = select prepared []
    val tm = pairterm input marker
    val expected = pairproof rule (REFL marker)
    val label = entry ^ "/lifted " ^ route ^ "/" ^ error_name
    val _ = enabled := true
    val _ =
      if error_name = "HOL_ERR" then
        result (label ^ ": ordinary rejection remains a valid proof")
          saved tm expected
      else throws (label ^ ": exact exception") predicate
             (fn () => saved tm)
    val _ = check (label ^ ": callback ran after bounded consumption")
      (!consumed)
    val _ = check (label ^ ": exhausted caller restored") (!counter = 0)
    val _ = enabled := false
    val _ = result (label ^ ": saved conversion reusable")
      saved pair_input pair_expected
  in result (label ^ ": caller remains exhausted")
       caller input (REFL input) end) errors)
    ["reducer","solver","collector"]) entries

(* Preparation and saving conversions neither collect supplied premises
   nor recompile installed rules. Normalize refreshes context once;
   arguments refreshes each child on each pass (two arguments, two passes).
   Neither reruns the installed maker or refills the public allowance. *)
val _ = let
  exception Context of int
  val maker_calls = ref 0
  val collects = ref 0
  val applies = ref 0
  val visits = ref 0
  val charges = ref 0
  val deriving = ref true
  fun maker rw =
    (maker_calls := !maker_calls + 1; Cond_rewr.mk_cond_rewrs rw)
  val reducer = E.lift (Traverse.REDUCER
    {name=SOME "derivation lifetime",initial=Context 0,
     addcontext=fn (Context n,ths) =>
       (check "derivation collector receives one fresh supplied context"
          (n = 0 andalso length ths = 1 andalso same (hd ths) TRUTH);
        collects := !collects + 1; Context 1)
       | _ => raise Fail "lost derivation context",
     apply=fn {context,...} => fn tm =>
       (check "derivation apply retains its collected context"
          (case context of Context n => n = (if !deriving then 1 else 0)
                         | _ => false);
        applies := !applies + 1; NO_CONV tm)})
  val ss = S.++ (S.++ (seed maker,S.rewrites [Once rule]),
                 S.dproc_ss reducer)
  val made = !maker_calls
  val policy = E.charge_only (fn () => charges := !charges + 1)
  val prepared = S.prepare_child_first_observed
    (fn _ => visits := !visits + 1) policy ss
  val saved = map (fn (entry,select) =>
    (entry,select prepared [TRUTH])) entries
  val _ = check "prepare/save/pretest is inert for opaque ordinary reducer"
    (#may_reduce_arguments prepared pair_input andalso
     !maker_calls = made andalso !collects = 0 andalso !applies = 0 andalso
     !visits = 0 andalso !charges = 0)
  val tm = pairterm input output
  val expected = pairproof rule (REFL output)
  val _ = List.app (fn (entry,cv) => List.app (fn _ => let
    val refreshes = if entry = "arguments" then 4 else 1
    val before_makers = !maker_calls
    val before_collects = !collects
    val _ = result "saved private conversion with supplied context"
      cv tm expected
  in check (entry ^ ": exact supplied-context refresh/compilation count")
       (!maker_calls = before_makers + refreshes andalso
        !collects = before_collects + refreshes) end) [1,2]) saved
  val _ = deriving := false
  val _ = result "prepared reuse did not spend caller's installed rule"
    (total (projection ss)) input rule
in result "preparation did not increase caller's declared allowance"
     (total (projection ss)) input (REFL input) end

val _ = print ("DERIVATION_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = if null (!failures) then OS.Process.exit OS.Process.success
        else die (Int.toString (length (!failures)) ^ " derivation failures")

end (* struct *)
