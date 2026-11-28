(* Intersections not covered by the native traversal/strategy pins:
   single-step roots, retained generic contexts through opaque callbacks,
   failed saved applications, and eta policy with selected congruence descent.
   All expected results are kernel proofs, including complete hypotheses. *)
structure lifetimes =
struct

(* Explicit import: Holdep does not follow the local structure alias. *)
open TraverseExt HolKernel Parse boolLib boolSyntax testutils
structure E = TraverseExt

val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected)
fun total cv = QCONV (TRY_CONV cv)
fun result name cv tm expected = check name (same (total cv tm) expected)
fun contract ok = if ok then () else raise Fail "lifetime callback contract"
fun terms xs ys = ListPair.allEq (fn (x,y) => aconv x y) (xs,ys)
fun facts xs ys = ListPair.allEq (fn (x,y) => same x y) (xs,ys)
fun rules congs = Travrules.TRAVRULES
  {relations=[Travrules.EQ_preorder],congprocs=congs,weakenprocs=[]}
fun data rewriters dprocs congs : E.traverse_data =
  {limit=NONE,rewriters=rewriters,dprocs=dprocs,
   relation=equality,travrules=rules congs}

(* A root entry performs exactly one successful candidate, never a descent
   or a fixpoint. Even its congruence factories must remain uncalled. *)
val _ = let
  exception Payload of unit ref * thm list
  val token = ref ()
  val supplied = ASSUME ``lifetime_root_fact:bool``
  val a = ``(lifetime_root_f:bool -> bool) lifetime_root_x``
  val x = rand a
  val y = ``lifetime_root_child:bool``
  val xy = ASSUME (mk_eq (x,y))
  val b = ``lifetime_root_b:bool``
  val c = ``lifetime_root_c:bool``
  val ab = ASSUME (mk_eq (a,b))
  val bc = ASSUME (mk_eq (b,c))
  val ac = TRANS ab bc
  val log = ref ([] : string list)
  fun record s = log := !log @ [s]
  val collectors = ref 0
  val high = ref true
  val low = ref true
  fun reducer name enabled proof = E.lift (Traverse.REDUCER
    {name=SOME name,initial=Payload (token,[]),
     addcontext=fn (Payload (r,ths),more) =>
       (contract (Portable.pointer_eq (r,token) andalso null ths andalso
                  facts more [supplied]);
        collectors := !collectors + 1; Payload (r,more))
       | _ => raise Fail "lost opaque root payload",
     apply=fn {context,stack,relation=(rel,refl),...} => fn tm =>
       (contract (null stack andalso aconv rel equality andalso
                  same (refl tm) (REFL tm) andalso
                  (case context of Payload (r,ths) =>
                     Portable.pointer_eq (r,token) andalso
                     facts ths [supplied] | _ => false));
        record (name ^ (if aconv tm a then ":root" else ":other"));
        if !enabled andalso aconv tm a then proof
        else if aconv tm b then bc
        else if aconv tm x then xy else NO_CONV tm)})
  val h = reducer "high" high ab
  val l = reducer "low" low ac
  val factory : Opening.congproc = fn _ => fn _ =>
    (record "factory"; NO_CONV)
  val xd = (data [h] [l] [factory],E.default_config)
  val cv = E.ROOT_REWRITE xd [supplied]
  val split = E.ROOT_REWRITE_WITH_CONTEXT xd
    {reducer_context=[supplied],solver_context=[TRUTH]}
  val _ = check "root construction/lifting is callback-free"
    (null (!log) andalso !collectors = 0)
  fun run label conversion expected events = let
    val collected = !collectors
    val _ = log := []
    val _ = result label conversion a expected
  in check (label ^ ": exact callbacks, fresh private payloads")
       (!log = events andalso !collectors = collected + 2) end
  val _ = run "root high priority stops before low/fixpoint/descent" cv ab
    ["high:root"]
  val _ = run "saved root still stops after one successful rewrite" cv ab
    ["high:root"]
  val _ = high := false
  val _ = run "root failed high candidate falls through to low" cv ac
    ["high:root","low:root"]
  val _ = run "solver-only facts never reach opaque root collectors"
    split ac ["high:root","low:root"]
  val _ = low := false
  val _ = run "failed root never descends into reducible children"
    cv (REFL a) ["high:root","low:root"]
  val _ = log := []
  val collected = !collectors
  val _ = result "positive control: the ignored child really rewrites"
    cv x xy
in check "child control is a single high candidate with fresh contexts"
     (!log = ["high:other"] andalso !collectors = collected + 2) end

(* Distinct reducer-only and solver-only facts. Each saved application gets
   a new private collector result, while a solver's saved recurse closure
   retains its OWN context even after nested calls and later failures. The
   ordinary callback forwards explicit stacks through both conv and solver. *)
val _ = let
  exception Payload of unit ref * int * thm list
  exception Stop of unit ref
  val token = ref ()
  val stop = ref ()
  val generations = ref 0
  val calls = ref ([] : string list)
  val captured = ref ([] : (int * E.simp_prover_ctxt) list)
  val seen = ref ([] : (int * term) list)
  val fail = ref false
  val nested = ref true
  val inside = ref false
  val inner = ref (NO_CONV : conv)
  val root = ``lifetime_solver_root:bool``
  val output = ``lifetime_solver_output:bool``
  val x = ``lifetime_solver_x:bool``
  val y = ``lifetime_solver_y:bool``
  val p = ``lifetime_solver_p:bool``
  val conv_stack = [``lifetime_conv_stack:bool``]
  val solve_stack = [``lifetime_solve_stack:bool``]
  val outer_r = ASSUME ``lifetime_outer_reducer:bool``
  val inner_r = ASSUME ``lifetime_inner_reducer:bool``
  val outer_p = ADD_ASSUM ``lifetime_outer_solver:bool`` (ASSUME p)
  val inner_p = ADD_ASSUM ``lifetime_inner_solver:bool`` (ASSUME p)
  val xy = ASSUME (mk_eq (x,y))
  val conditional = ASSUME (mk_imp (p,mk_eq (root,output)))
  val outer_expected = MP conditional outer_p
  val inner_expected = MP conditional inner_p
  fun record s = calls := !calls @ [s]
  fun current thms =
    if facts thms [outer_r,outer_p] then ("outer",outer_p)
    else if facts thms [inner_r,inner_p] then ("inner",inner_p)
    else raise Fail "generic context mixed or reordered"
  val reducer = Traverse.REDUCER
    {name=SOME "opaque lifetime forwarding",initial=Payload (token,0,[]),
     addcontext=fn (Payload (r,n,ths),more) =>
       (contract (Portable.pointer_eq (r,token) andalso n = 0 andalso
                  null ths andalso
                  (facts more [outer_r] orelse facts more [inner_r]));
        generations := !generations + 1;
        record ("collect:" ^ Int.toString (!generations));
        Payload (r,!generations,more))
       | _ => raise Fail "lost opaque solver payload",
     apply=fn {context,stack,conv,solver,relation=(rel,refl)} => fn tm =>
       let
         val (n,ths) = case context of Payload (r,n,ths) =>
           (contract (Portable.pointer_eq (r,token)); (n,ths))
           | _ => raise Fail "lost opaque apply payload"
         val _ = contract (aconv rel equality andalso
                           same (refl tm) (REFL tm))
         val _ = seen := !seen @ [(n,tm)]
       in
         if aconv tm root then
           (contract (null stack andalso
                      (facts ths [outer_r] orelse facts ths [inner_r]));
            contract (same (conv conv_stack x) xy);
            MP conditional (solver solve_stack p))
         else if aconv tm x then
           (contract (terms stack conv_stack orelse
                      terms stack solve_stack); xy)
         else NO_CONV tm
       end}
  val lifted = E.lift reducer
  val _ = ignore (E.reducer_data lifted)
  val _ = ignore (E.reducer_config_data lifted)
  fun subgoaler {context_thms,stack,...} tm =
    let val (name,_) = current context_thms in
      contract (terms stack solve_stack andalso aconv tm p);
      record (name ^ ":subgoal"); REFL tm
    end
  fun rejecting (ctxt as {context_thms,stack,recurse}) tm = let
    val (name,_) = current context_thms
    val _ = contract (terms stack solve_stack andalso aconv tm p)
    val _ = record (name ^ ":reject")
    val _ = captured := !captured @ [(!generations,ctxt)]
    val _ = contract (same (recurse x) xy)
  in NO_CONV tm end
  fun proving {context_thms,stack,recurse} tm = let
    val (name,proof) = current context_thms
    val _ = contract (terms stack solve_stack andalso aconv tm p)
    val _ = record (name ^ ":prove")
    val _ = if !fail then raise Stop stop else ()
    val _ = if !nested andalso not (!inside) then
      Portable.finally (fn () => inside := false)
        (fn () => (inside := true;
                   contract (same ((!inner) root) inner_expected))) ()
      else ()
    (* The outer context/stack survives reentrant use of the SAME data. *)
    val _ = contract (same (recurse x) xy)
  in proof end
  val config : E.traverse_config =
    {subgoaler=SOME subgoaler,
     solvers=[{name="reject",solve=rejecting},{name="prove",solve=proving}],
     cond_depth=NONE,term_ord=NONE}
  val xd = (data [lifted] [] [],config)
  fun build r p = E.ROOT_REWRITE_WITH_CONTEXT xd
    {reducer_context=[r],solver_context=[p]}
  val outer = build outer_r outer_p
  val _ = inner := build inner_r inner_p
  val _ = check "opaque adapters and saved generic roots are inert"
    (!generations = 0 andalso null (!calls) andalso null (!seen))
  val pipeline = ["outer:subgoal","outer:reject","outer:prove"]
  val inner_pipeline = ["inner:subgoal","inner:reject","inner:prove"]
  fun invocation first =
    ["collect:" ^ Int.toString first] @ pipeline @
    ["collect:" ^ Int.toString (first + 1)] @ inner_pipeline
  val _ = result "nested generic solver root: complete outer proof"
    outer root outer_expected
  val _ = result "reused generic solver root: complete outer proof"
    outer root outer_expected
  val _ = check "nested/reused solver callback order and collector counts"
    (!generations = 4 andalso !calls = invocation 1 @ invocation 3)
  fun apply_trace first =
    map (fn tm => (first,tm)) [root,x,y,x,y] @
    map (fn tm => (first + 1,tm)) [root,x,y,x,y,x,y] @
    map (fn tm => (first,tm)) [x,y]
  fun same_trace actual expected = ListPair.allEq
    (fn ((n,tm),(m,other)) => n = m andalso aconv tm other)
    (actual,expected)
  val _ = check "opaque conv/solver/recurse apply counts are exact"
    (same_trace (!seen) (apply_trace 1 @ apply_trace 3))
  val _ = check "saved solver contexts contain no nested/reused additions"
    (map #1 (!captured) = [1,2,3,4] andalso
     ListPair.allEq
       (fn ((_,{context_thms,...}),expected) => facts context_thms expected)
       (!captured,[[outer_r,outer_p],[inner_r,inner_p],
                   [outer_r,outer_p],[inner_r,inner_p]]))
  val first = #2 (hd (!captured))
  val _ = seen := []
  val _ = result "retained recurse after later applications keeps proof"
    (#recurse first) x xy
  val _ = check "retained recurse uses original opaque context, no collector"
    (!generations = 4 andalso map #1 (!seen) = [1,1])
  val _ = nested := false
  val _ = fail := true
  val _ = calls := []
  val _ = seen := []
  val failed = Exn.capture (fn () => outer root) ()
  val _ = check "failed saved root propagates exact solver exception"
    (case failed of Exn.Exn (Stop r) => Portable.pointer_eq (r,stop)
                 | _ => false)
  val _ = check "failed saved root has exactly one fresh context/pipeline"
    (!generations = 5 andalso !calls = ["collect:5"] @ pipeline andalso
     same_trace (!seen) (map (fn tm => (5,tm)) [root,x,y,x,y]))
  val _ = fail := false
  val _ = calls := []
  val _ = seen := []
  val _ = result "saved root after failure refreshes and proves again"
    outer root outer_expected
  val _ = check "post-failure reuse neither keeps nor doubles collectors"
    (!generations = 6 andalso !calls = ["collect:6"] @ pipeline andalso
     same_trace (!seen) (map (fn tm => (6,tm)) [root,x,y,x,y,x,y]))
  val _ = seen := []
  val _ = result "old recurse survives a later foreign solver exception"
    (#recurse first) x xy
in check "old recurse still has generation one after failure/retry"
     (!generations = 6 andalso map #1 (!seen) = [1,1]) end

(* Eta head preservation precedes descent even when a congruence deliberately
   ignores that function argument. A successful unchanged selected congruence
   must also block fallback descent. Toggle a policy captured by a saved
   conversion: its predicate is consulted at use, not construction. *)
val _ = let
  exception Empty
  val h = ``lifetime_head:(bool -> bool) -> bool -> bool``
  val f = ``lifetime_fun:bool -> bool``
  val abstraction = ``\x:bool. lifetime_fun x:bool``
  val a = ``lifetime_selected_a:bool``
  val b = ``lifetime_selected_b:bool``
  val ab = ASSUME (mk_eq (a,b))
  val input = list_mk_comb (h,[abstraction,a])
  val kept = AP_TERM (mk_comb (h,abstraction)) ab
  val eta = AP_THM (AP_TERM h (ETA_CONV abstraction)) a
  val contracted = TRANS eta (AP_TERM (mk_comb (h,f)) ab)
  val keep = ref true
  val selected = ref 0
  val fallback = ref 0
  val rewrites = ref 0
  val body_visits = ref 0
  fun is_head tm = aconv (fst (strip_comb tm)) h
  val policy : E.child_first_policy =
    {charge=fn () => (),keep_abstraction=fn tm => !keep andalso is_head tm}
  val reducer = E.lift (Traverse.REDUCER
    {name=SOME "selected child",initial=Empty,
     addcontext=fn (c,_) => c,
     apply=fn _ => fn tm =>
       if aconv tm a then (rewrites := !rewrites + 1; ab)
       else (if aconv tm abstraction orelse aconv tm f orelse
                    (is_comb tm andalso aconv (rator tm) f)
             then body_visits := !body_visits + 1 else ();
             NO_CONV tm)})
  val select : Opening.congproc = fn _ => fn {depther,...} => fn tm =>
    case strip_comb tm of
        (head,[func,arg]) =>
          if aconv head h then let
            val _ = selected := !selected + 1
            val th = total (depther ([],equality)) arg
          in
            if aconv (lhs (concl th)) (rhs (concl th)) then
              raise UNCHANGED
            else AP_TERM (mk_comb (h,func)) th
          end else NO_CONV tm
      | _ => NO_CONV tm
  val other : Opening.congproc = fn _ => fn _ => fn tm =>
    (if is_head tm then fallback := !fallback + 1 else (); NO_CONV tm)
  val cv = E.TRAVERSE_WITH_CONTEXT (E.ChildFirst policy)
    (data [reducer] [] [select,other],E.default_config)
    {reducer_context=[],solver_context=[]}
  val _ = check "saved head policy has no construction-time traversal"
    (!selected = 0 andalso !rewrites = 0 andalso !body_visits = 0)
  val _ = result "kept eta head survives congruence-selected descent"
    cv input kept
  val _ = keep := false
  val _ = result "saved policy now eta-contracts before selected descent"
    cv input contracted
  val _ = keep := true
  val _ = result "saved policy can preserve the head again" cv input kept
  val _ = result "unchanged selected congruence blocks fallback descent"
    cv (rhs (concl kept)) (REFL (rhs (concl kept)))
in check "exact selected descent counts; ignored function never visited"
     (!selected = 4 andalso !rewrites = 3 andalso !fallback = 0 andalso
      !body_visits = 0) end

(* A policy abort is not a failed eta candidate. In particular HOL_ERR
   must survive eta fallback and TRY_CONV, without stale state on reuse. *)
val _ = let
  exception Stop of unit ref
  val token = ref ()
  val holpayload = Feedback.mk_hol_error
    "lifetime" "head" locn.Loc_Unknown "head-policy payload"
  val holerror = HOL_ERR holpayload
  fun is_hol (HOL_ERR e) =
        Portable.pointer_eq (e,holpayload) andalso
        Feedback.top_structure_of e = "lifetime" andalso
        Feedback.top_function_of e = "head" andalso
        Feedback.message_of e = "head-policy payload"
    | is_hol _ = false
  val errors =
    [("HOL_ERR",holerror,is_hol),
     ("foreign",Stop token,
      fn Stop r => Portable.pointer_eq (r,token) | _ => false),
     ("Interrupt",Portable.Interrupt,
      fn Portable.Interrupt => true | _ => false)]
  val tm = ``(lifetime_abort:(bool -> bool) -> bool) (\x:bool. f x)``
  val expected = RAND_CONV ETA_CONV tm
  val xd = (data [] [] [],E.default_config)
  fun entry label build (error_name,error,predicate) = let
    val enabled = ref true
    val calls = ref 0
    val policy : E.child_first_policy =
      {charge=fn () => (),keep_abstraction=fn _ =>
         (calls := !calls + 1; if !enabled then raise error else false)}
    val children = ref 0
    fun child tm = (children := !children + 1; REFL tm)
    val saved = build policy child
    val actual = Exn.capture saved tm
    val _ = check (label ^ "/" ^ error_name ^ ": exact policy abort")
      (case actual of Exn.Exn e => predicate e | _ => false)
    val _ = check (label ^ "/" ^ error_name ^ ": no callback after abort")
      (!calls = 1)
    val _ = if label = "arguments" then
        check (label ^ "/" ^ error_name ^ ": no child callback after abort")
          (!children = 0)
      else ()
    val _ = enabled := false
  in result (label ^ "/" ^ error_name ^ ": saved entry recovers")
       saved tm expected end
in
  List.app (fn (label,build) => List.app (entry label build) errors)
    [("child",fn p => fn _ =>
        E.TRAVERSE_WITH_CONTEXT (E.ChildFirst p) xd
          {reducer_context=[],solver_context=[]}),
     ("observed",fn p => fn _ =>
        E.CHILD_FIRST_WITH_OBSERVER (fn _ => ()) p xd
          {reducer_context=[],solver_context=[]}),
     ("arguments",fn p => E.NORMALIZE_ARGUMENTS p)]
end

(* A selected congruence can encounter a policy abort inside depther after
   ALL congruence factories have been built. Guard the returned conversions,
   not just their factories: HOL_ERR rejection must never call a fallback
   after that abort. Ordinary rejection and UNCHANGED keep their schedules. *)
val _ = let
  exception Foreign of unit ref
  val token = ref ()
  val payload = Feedback.mk_hol_error
    "lifetime" "selected_child" locn.Loc_Unknown "selected child abort"
  val errors =
    [("HOL_ERR",HOL_ERR payload,
      fn HOL_ERR e => Portable.pointer_eq (e,payload) | _ => false),
     ("foreign",Foreign token,
      fn Foreign r => Portable.pointer_eq (r,token) | _ => false),
     ("Interrupt",Portable.Interrupt,
      fn Portable.Interrupt => true | _ => false)]
  val hold = ``(lifetime_hold:(bool -> bool) -> bool)
                  (\u:bool. lifetime_h u)``
  val outer = ``lifetime_outer:bool -> bool``
  val input = mk_comb (outer,hold)
  val expected = AP_TERM outer (RAND_CONV ETA_CONV hold)
  val context = {reducer_context=[],solver_context=[]}
  fun build route policy observer xd =
    case route of
        "generic" => E.TRAVERSE_WITH_CONTEXT (E.ChildFirst policy) xd context
      | "observed" =>
          E.CHILD_FIRST_WITH_OBSERVER observer policy xd context
      | _ => E.CHILD_FIRST_WITH_ABORT (fn () => ()) NONE policy xd context
  fun run route successful (error_name,error,exact) = let
    val enabled = ref true
    val aborted = ref false
    val policy_calls = ref 0
    val post_calls = ref ([] : string list)
    val factories = ref ([] : string list)
    val fallbacks = ref ([] : string list)
    fun callback name =
      if !aborted then post_calls := !post_calls @ [name] else ()
    fun keep tm =
      (callback "policy";
       if !enabled andalso aconv tm hold then
         (policy_calls := !policy_calls + 1; aborted := true; raise error)
       else false)
    val policy = {charge=fn () => callback "charge",keep_abstraction=keep}
    fun observe _ = callback "observer"
    fun factory name =
      (callback (name ^ " factory"); factories := !factories @ [name])
    val select : Opening.congproc = fn _ => fn {depther,...} =>
      (factory "select"; fn tm =>
        (callback "select";
         if is_comb tm andalso aconv (rator tm) outer then
           AP_TERM outer (QCONV (depther ([],equality)) (rand tm))
         else NO_CONV tm))
    fun fallback name success : Opening.congproc = fn _ => fn _ =>
      (factory name; fn tm =>
        (callback name;
         if aconv tm input then
           (fallbacks := !fallbacks @ [name];
            if success then expected else NO_CONV tm)
         else NO_CONV tm))
    val xd = (data [] [] [select,fallback "reject" false,
                          fallback "last" successful],E.default_config)
    val saved = build route policy observe xd
    val label = route ^ "/selected child/" ^ error_name ^
                (if successful then "/success" else "/failure")
    val _ = check (label ^ ": construction is inert")
      (null (!factories) andalso !policy_calls = 0)
    fun abort () = let
      val actual = Exn.capture saved input
      val _ = check (label ^ ": exact policy abort")
        (case actual of Exn.Exn e => exact e | _ => false)
      val _ = check (label ^ ": selected child abort witnessed once")
        (!policy_calls = 1)
      val _ = check (label ^ ": no congruence or callback after abort")
        (null (!post_calls) andalso null (!fallbacks))
    in check (label ^ ": factories retain eager list schedule per descent")
         (!factories = ["select","reject","last"]) end
    val _ = abort ()
    val _ = aborted := false
    val _ = policy_calls := 0
    val _ = factories := []
    val _ = abort ()
    val _ = enabled := false
    val _ = aborted := false
    val _ = result (label ^ ": saved conversion recovers with proof")
      saved input expected
  in check (label ^ ": successful selected descent never tries fallback")
       (null (!post_calls) andalso null (!fallbacks)) end
  (* No policy abort: a rejected selected conversion MUST invoke fallback.
     UNCHANGED stops fallback, whereas foreign errors/Interrupt propagate. *)
  fun ordinary route (name,error,exact) = let
    val calls = ref ([] : string list)
    val mode = ref "error"
    val select : Opening.congproc = fn _ => fn _ => fn tm =>
      if aconv tm input then
        (calls := !calls @ ["select"];
         if !mode = "error" then raise error
         else if !mode = "unchanged" then raise UNCHANGED else expected)
      else NO_CONV tm
    fun fallback name success : Opening.congproc = fn _ => fn _ => fn tm =>
      if aconv tm input then
        (calls := !calls @ [name]; if success then expected else NO_CONV tm)
      else NO_CONV tm
    val saved = build route
      {charge=fn () => (),keep_abstraction=fn _ => false} (fn _ => ())
      (data [] [] [select,fallback "reject" false,fallback "prove" true],
       E.default_config)
    val actual = Exn.capture saved input
    val holerror = case error of HOL_ERR _ => true | _ => false
    val label = route ^ "/ordinary congruence/" ^ name
    val _ = check (label ^ ": exact rejection or exception")
      (case actual of Exn.Res th => holerror andalso same th expected
                    | Exn.Exn e => not holerror andalso exact e)
    val _ = check (label ^ ": exact fallback callback order")
      (!calls = if holerror then ["select","reject","prove"]
                else ["select"])
    val _ = calls := []
    val _ = mode := "unchanged"
    val _ = result (label ^ ": unchanged blocks fallback")
      saved input (REFL input)
    val _ = check (label ^ ": unchanged callback count") (!calls = ["select"])
    val _ = calls := []
    val _ = mode := "success"
    val _ = result (label ^ ": saved congruence succeeds again")
      saved input expected
  in check (label ^ ": successful callback count") (!calls = ["select"]) end
in
  List.app (fn route =>
    (List.app (fn success => List.app (run route success) errors) [false,true];
     List.app (ordinary route) errors)) ["generic","observed","abort-hook"]
end

val _ = print ("TraverseExt lifetime checks: " ^ Int.toString (!checks) ^
               "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
