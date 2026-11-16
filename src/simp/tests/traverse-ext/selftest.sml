(* Assertions on the separate engine, not legacy adapters. *)
structure selftest =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure T = TraverseExt

val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected)
fun terms xs ys = ListPair.allEq (fn (x,y) => aconv x y) (xs,ys)
fun total cv = QCONV (TRY_CONV cv)
fun result cv tm expected = same (total cv tm) expected
fun fails name predicate f =
  check name (case Exn.capture f () of
                  Exn.Exn e => predicate e
                | Exn.Res _ => false)
val empty_context = {reducer_context=[],solver_context=[]}
val quiet = T.charge_only (fn () => ())
val no_rules = Travrules.TRAVRULES
  {relations=[Travrules.EQ_preorder],congprocs=[],weakenprocs=[]}
fun data rules rewriters dprocs limit : T.traverse_data =
  {rewriters=rewriters,dprocs=dprocs,limit=limit,
   travrules=rules,relation=equality}
fun config subgoaler solvers depth ord : T.traverse_config =
  {subgoaler=subgoaler,solvers=solvers,cond_depth=depth,term_ord=ord}
exception Private of unit ref * thm list
exception Stop of unit ref
val a = ``ext_a:bool``
val b = ``ext_b:bool``
val c = ``ext_c:bool``
val p = ``ext_p:bool``
val ab = ASSUME (mk_eq (a,b))
val bc = ASSUME (mk_eq (b,c))

(* Lifting and both record views are inert; explicit addctxt is not. The
   original exception payload, callback closures and all continuations must
   survive both views. No dest_reducer exists on the extension boundary. *)
val _ = let
  val token = ref ()
  val collections = ref 0
  val applications = ref 0
  val supplied = [ASSUME p,TRUTH]
  val observed = ref ([] : thm list)
  val solver_calls = ref 0
  val conv_calls = ref 0
  fun collector (Private (r,old),ths) =
        (check "lift: collector payload identity"
           (Portable.pointer_eq (r,token));
         collections := !collections + 1; observed := ths;
         Private (r,old @ ths))
    | collector _ = raise Fail "lost private collector context"
  val ordinary = Traverse.REDUCER
    {name=SOME "opaque ordinary",initial=Private (token,[]),
     addcontext=collector,
     apply=fn {solver,conv,context,stack,relation=(rel,refl)} => fn tm =>
       let
         val _ = applications := !applications + 1
         val _ = case context of Private (r,ths) =>
           check "lift: apply payload and collected facts"
             (Portable.pointer_eq (r,token) andalso
              terms (map concl ths) (map concl supplied))
           | _ => raise Fail "lost private apply context"
         val _ = check "lift: stack/relation/refl forwarded"
           (terms stack [a,b] andalso aconv rel equality andalso
            same (refl tm) (REFL tm))
         val _ = check "lift: solver continuation forwarded"
           (same (solver [b,a] p) (ASSUME p))
         val _ = check "lift: conv continuation forwarded"
           (same (conv [c,b] a) ab)
       in REFL tm end}
  val lifted = T.lift ordinary
  val rd = T.reducer_data lifted
  val rc = T.reducer_config_data lifted
  val _ = check "lift and record extraction run no callbacks"
    (!collections = 0 andalso !applications = 0 andalso
     #name rd = SOME "opaque ordinary" andalso #name rc = #name rd)
  val added = T.addctxt supplied lifted
  val _ = if T.reducer_kind lifted = T.LiftedReducer andalso
             T.reducer_kind added = T.LiftedReducer then ()
          else raise Fail "lift or addctxt changed the lifted kind"
  val _ = check "explicit addctxt invokes original collector exactly once"
    (!collections = 1 andalso !applications = 0 andalso
     ListPair.allEq (fn (x,y) => same x y) (!observed,supplied))
  fun solver stack tm =
    (solver_calls := !solver_calls + 1;
     if terms stack [b,a] andalso aconv tm p then ASSUME p
     else raise Fail "solver arguments changed")
  fun conv stack tm =
    (conv_calls := !conv_calls + 1;
     if terms stack [c,b] andalso aconv tm a then ab
     else raise Fail "conv arguments changed")
  val rd = T.reducer_data added
  val rc = T.reducer_config_data added
  val _ = check "integer record view forwards ordinary apply"
    (same (#apply rd
      {solver=solver,conv=conv,context= #initial rd,stack=[a,b],
       relation=(equality,REFL),cond_depth=19,term_ord=fn _ => LESS} a)
      (REFL a))
  val _ = check "option record view forwards ordinary apply"
    (same (#apply rc
      {solver=solver,conv=conv,context= #initial rc,stack=[a,b],
       relation=(equality,REFL),cond_depth=NONE,term_ord=fn _ => GREATER} a)
      (REFL a))
  val _ = check "adapter callback counts"
    (!collections = 1 andalso !applications = 2 andalso
     !solver_calls = 2 andalso !conv_calls = 2)
in () end

(* The lifted callbacks also receive the real engine continuations. *)
val _ = let
  val token = ref ()
  val root = ``ext_forward_root:bool``
  val output = ``ext_forward_output:bool``
  val pT = ASSUME (mk_eq (p,T))
  val rule = ASSUME (mk_imp (p,mk_eq (root,output)))
  val visits = ref ([] : (term * term list) list)
  val ordinary = Traverse.REDUCER
    {name=NONE,initial=Private (token,[]),
     addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,conv,context,stack,relation=(rel,refl)} => fn tm =>
       (case context of Private (r,[]) =>
          if Portable.pointer_eq (r,token) then ()
          else raise Fail "engine changed lifted payload"
        | _ => raise Fail "engine changed lifted context";
        if aconv rel equality andalso same (refl tm) (REFL tm) then ()
        else raise Fail "engine changed lifted relation";
        visits := !visits @ [(tm,stack)];
        if aconv tm root then
          (if same (conv [c,b] a) ab then ()
           else raise Fail "engine conv continuation";
           MP rule (solver [a,b] p))
        else if aconv tm a then ab
        else if aconv tm p then pT else NO_CONV tm)}
  val cv = T.ROOT_REWRITE
    (data no_rules [T.lift ordinary] [] NONE,T.default_config) []
  val _ = check "lifted engine solver/conv preserve proof and context"
    (same (cv root) (MP rule (EQT_ELIM pT)))
  val _ = check "lifted engine recursive continuations forward exact stacks"
    (ListPair.allEq (fn ((tm,s),(expected,es)) =>
       aconv tm expected andalso terms s es)
       (!visits,[(root,[]),(a,[c,b]),(b,[c,b]),(p,[a,b]),(T,[a,b])]))
in () end

(* Native adapter views retain option-vs-integer depth and payloads. *)
val _ = let
  val token = ref ()
  val calls = ref 0
  val depths = ref ([] : int option list)
  fun collect (Private (r,old),ths) =
        (calls := !calls + 1;
         if Portable.pointer_eq (r,token) then Private (r,old @ ths)
         else raise Fail "native collector token changed")
    | collect _ = raise Fail "native collector context changed"
  fun apply {context,cond_depth,term_ord,...} tm =
    (case context of Private (r,ths) =>
       if Portable.pointer_eq (r,token) andalso terms (map concl ths) [p]
       then () else raise Fail "native adapter payload changed"
     | _ => raise Fail "native adapter context changed";
     if term_ord (a,b) = LESS then () else raise Fail "adapter order changed";
     depths := !depths @ [cond_depth]; REFL tm)
  val native = T.CONFIG_REDUCER
    {name=SOME "native",initial=Private (token,[]),addcontext=collect,
     apply=apply}
  val view = T.reducer_data native
  val back = T.reducer_config_data (T.CONTEXT_REDUCER view)
  val _ = check "native record adapters do not collect or apply"
    (!calls = 0 andalso null (!depths) andalso #name back = SOME "native")
  fun invoke r depth = let
    val r = T.addctxt [ASSUME p] r
    val rd = T.reducer_config_data r
  in
    #apply rd {solver=fn _ => ASSUME,conv=fn _ => REFL,
      context= #initial rd,stack=[],cond_depth=depth,
      term_ord=fn _ => LESS,relation=(equality,REFL)} a
  end
  val _ = check "CONFIG addctxt preserves payload and NONE"
    (same (invoke native NONE) (REFL a) andalso !depths = [NONE])
  val contextual = T.CONTEXT_REDUCER view
  val _ = Lib.with_flag (Cond_rewr.stack_limit,23) (fn () =>
    check "CONTEXT adapter samples live depth at application"
      (same (invoke contextual NONE) (REFL a) andalso
       !depths = [NONE,SOME 23])) ()
  val _ = check "integer view of CONFIG passes SOME, not live NONE"
    (same (invoke contextual (SOME 5)) (REFL a) andalso
     !depths = [NONE,SOME 23,SOME 5] andalso !calls = 3)
  (* Silent: reducer_kind reports provenance for all three builders and
     addctxt preserves it; it is not a behavioural predicate. *)
  val _ = let
    val ctx = Private (ref (),[])
    fun keep (c,_) = c
    fun unused _ = raise Fail "unused"
    val ord = T.lift (Traverse.REDUCER
      {name=NONE,initial=ctx,addcontext=keep,apply=unused})
    val cfg = T.CONFIG_REDUCER
      {name=NONE,initial=ctx,addcontext=keep,apply=unused}
    val cxt = T.CONTEXT_REDUCER (T.reducer_data cfg)
    fun kind k r = T.reducer_kind r = k andalso
                   T.reducer_kind (T.addctxt [] r) = k
  in
    if kind T.LiftedReducer ord andalso kind T.ConfigReducer cfg andalso
       kind T.ContextReducer cxt andalso
       T.reducer_kind (T.CONFIG_REDUCER (T.reducer_config_data ord)) =
         T.ConfigReducer
    then () else raise Fail "reducer_kind changed"
  end
in () end

(* Atomic terms isolate initial collection from congruence additions. *)
val _ = let
  exception Generation of int
  fun lifetime kind (label,build,expected) = let
    val additions = ref 0
    val seen = ref ([] : int list)
    fun add (Generation n,ths) =
          (if terms (map concl ths) [p] then ()
           else raise Fail "initial fact sequence changed";
           additions := !additions + 1; Generation (n+1))
      | add _ = raise Fail "generation context changed"
    fun apply context tm =
      (case context of Generation n => seen := !seen @ [n]
       | _ => raise Fail "generation payload changed";
       NO_CONV tm)
    val reducer =
      case kind of
          "lifted" => T.lift (Traverse.REDUCER
            {name=NONE,initial=Generation 0,addcontext=add,
             apply=fn {context,...} => apply context})
        | "context" => T.CONTEXT_REDUCER
            {name=NONE,initial=Generation 0,addcontext=add,
             apply=fn {context,...} => apply context}
        | _ => T.CONFIG_REDUCER
            {name=NONE,initial=Generation 0,addcontext=add,
             apply=fn {context,...} => apply context}
    val cv = build (data no_rules [reducer] [] NONE) [ASSUME p]
    val n0 = !additions
    val th1 = total cv a
    val n1 = !additions
    val th2 = total cv a
    val n2 = !additions
  in
    check ("context lifetime: " ^ kind ^ "/" ^ label)
      ([n0,n1,n2] = expected andalso !seen = [1,1] andalso
       same th1 (REFL a) andalso same th2 (REFL a))
  end
  val builders =
    [("TRAVERSE",T.TRAVERSE,[1,1,1]),
     ("XTRAVERSE",fn d => T.XTRAVERSE (d,T.default_config),[0,1,2]),
     ("explicit parent",fn d => fn ths =>
        T.TRAVERSE_WITH_CONTEXT T.ParentFirst (d,T.default_config)
          {reducer_context=ths,solver_context=[]},[0,1,2]),
     ("root",fn d => T.ROOT_REWRITE (d,T.default_config),[0,1,2]),
     ("observer",fn d => fn ths =>
        T.CHILD_FIRST_WITH_OBSERVER (fn _ => ()) quiet (d,T.default_config)
          {reducer_context=ths,solver_context=[]},[0,1,2])]
  val _ = List.app (fn k => List.app (lifetime k) builders)
                  ["lifted","context","config"]
  val calls = ref ([] : string list)
  fun reducer tag = T.lift (Traverse.REDUCER
    {name=SOME tag,initial=Fail tag,
     addcontext=fn (ctxt,ths) =>
       (if terms (map concl ths) [p,a] then ()
        else raise Fail "collector fact order";
        calls := !calls @ [tag]; ctxt),apply=fn _ => NO_CONV})
  val d = data no_rules (map reducer ["R1","R2"])
                       (map reducer ["D1","D2"]) NONE
  val cv = T.TRAVERSE d [ASSUME p,ASSUME a]
  val _ = check "collector order: rewriters then dprocs"
    (!calls = ["R1","R2","D1","D2"])
  val _ = total cv a
  val _ = T.TRAVERSE d []
  val _ = check "empty initial context skips collectors; saved cv reuses"
    (!calls = ["R1","R2","D1","D2"])
in () end

(* NONE must reach the native candidate, not be sampled at reducer entry:
   both conversions below are in one reducer's FIRST_CONV invocation. *)
val _ = let
  val rule = ASSUME (mk_imp (p,mk_eq (a,b)))
  val run = Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG ("ext depth",rule) false
  val seen = ref ([] : int option list)
  val mutates = ref 0
  fun reducer mutate = T.CONFIG_REDUCER
    {name=NONE,initial=Fail "depth",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,cond_depth,term_ord,...} =>
       FIRST_CONV
         [fn tm => (if aconv tm a then
                      (seen := !seen @ [cond_depth];
                       if mutate then
                         (mutates := !mutates + 1;
                          Cond_rewr.stack_limit := 4)
                       else ())
                    else (); NO_CONV tm),
          run {solver=solver,stack=stack,cond_depth=cond_depth,
               term_ord=term_ord}]}
  val cfg = config (SOME (fn _ => REFL))
    [{name="depth fact",solve=fn _ => fn tm =>
        if aconv tm p then ASSUME p else NO_CONV tm}]
  fun cv mutate depth = T.XTRAVERSE
    (data no_rules [reducer mutate] [] NONE,cfg depth NONE) []
  val expected = MP rule (ASSUME p)
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0) (fn () =>
    (check "NONE reads shared depth after a preceding candidate mutates it"
       (result (cv true NONE) a expected andalso !seen = [NONE] andalso
        !mutates = 1 andalso !Cond_rewr.stack_limit = 4);
     seen := [];
     check "SOME zero is not replaced by mutated live depth"
       (result (cv true (SOME 0)) a (REFL a) andalso !seen = [SOME 0]);
     check "SOME one remains explicit"
       (result (cv true (SOME 1)) a expected))) ()
  val live = cv false NONE
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0)
    (fn () => check "saved NONE conversion reads depth zero"
      (result live a (REFL a))) ()
  val _ = Lib.with_flag (Cond_rewr.stack_limit,1)
    (fn () => check "saved NONE conversion reads changed depth one"
      (result live a expected)) ()
  val depth_seen = ref ([] : int list)
  val mutate = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "mutator",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => fn tm => (Cond_rewr.stack_limit := 13; NO_CONV tm)})
  val contextual = T.CONTEXT_REDUCER
    {name=NONE,initial=Fail "sample",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {cond_depth,...} => fn tm =>
       (depth_seen := !depth_seen @ [cond_depth]; NO_CONV tm)}
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0) (fn () =>
    (ignore (total (T.XTRAVERSE
       (data no_rules [mutate,contextual] [] NONE,T.default_config) []) a);
     check "CONTEXT samples NONE immediately before its callback"
       (!depth_seen = [13]))) ()
  val _ = depth_seen := []
  val _ = ignore (total (T.XTRAVERSE
    (data no_rules [contextual] [] NONE,cfg (SOME 7) NONE) []) a)
  val _ = check "CONTEXT receives configured integer" (!depth_seen = [7])
  val native = Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG
    ("ext permutation",SPEC_ALL boolTheory.EQ_SYM_EQ) false
  val comparisons = ref 0
  val perm = T.CONFIG_REDUCER
    {name=NONE,initial=Fail "perm",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,cond_depth,term_ord,...} =>
       native {solver=solver,stack=stack,cond_depth=cond_depth,
               term_ord=term_ord}}
  val input = ``(ext_order_a:'a) = ext_order_b``
  val output = ``(ext_order_b:'a) = ext_order_a``
  fun ordered ord = T.XTRAVERSE
    (data no_rules [perm] [] (SOME 1),
     config NONE [] (SOME 9)
       (SOME (fn pair => (comparisons := !comparisons + 1; ord pair)))) []
  val _ = convtest ("custom GREATER permits native permutation",
                    total (ordered (fn _ => GREATER)),input,output)
  val _ = checks := !checks + 1
  val _ = check "custom LESS rejects native permutation"
    (result (ordered (fn _ => LESS)) input (REFL input) andalso
     !comparisons = 2)
in () end

(* Generic solver facts must not leak into reducer collectors. Recursive
   facts prepend; initial solver-only facts append. Both pipeline stages
   receive the same context order and the caller's side-condition stack. *)
val _ = let
  val initial = map ASSUME [p,a]
  val solver_only = map ASSUME [b,c]
  val nested = [ASSUME ``ext_nested:bool``]
  val condition = ``ext_condition:bool``
  fun order_test subgoal = let
    val seen = ref ([] : term list list)
    val stacks = ref ([] : term list list)
    val collections = ref ([] : term list list)
    fun record ({context_thms,stack,...} : T.simp_prover_ctxt) =
      (seen := !seen @ [map concl context_thms];
       stacks := !stacks @ [stack])
    fun sg (ctxt : T.simp_prover_ctxt) tm =
      (record ctxt; EQT_INTRO (ASSUME tm))
    fun solve (ctxt : T.simp_prover_ctxt) tm =
      (record ctxt; ASSUME tm)
    val reducer = T.lift (Traverse.REDUCER
      {name=NONE,initial=Fail "order",
       addcontext=fn (ctxt,ths) =>
         (collections := !collections @ [map concl ths]; ctxt),
       apply=fn {solver,...} => fn tm =>
         (if aconv tm a orelse aconv tm b then
            ignore (solver [c,p] condition) else (); NO_CONV tm)})
    val descend : Opening.congproc = fn _ => fn {depther,...} => fn tm =>
      if aconv tm a then
        (ignore (total (depther (nested,equality)) b); raise UNCHANGED)
      else NO_CONV tm
    val rules = Travrules.TRAVRULES
      {relations=[Travrules.EQ_preorder],congprocs=[descend],weakenprocs=[]}
    val cfg = config (if subgoal then SOME sg else NONE)
      (if subgoal then [] else [{name="order",solve=solve}]) NONE NONE
    val _ = total (T.TRAVERSE_WITH_CONTEXT T.ParentFirst
      (data rules [reducer] [] NONE,cfg)
      {reducer_context=initial,solver_context=solver_only}) a
  in
    check ("generic " ^ (if subgoal then "subgoaler" else "solver") ^
           " context and stack order")
      (ListPair.allEq (fn (xs,ys) => terms xs ys)
         (!seen,map (map concl)
           [initial @ solver_only,nested @ initial @ solver_only]) andalso
       List.all (fn s => terms s [c,p]) (!stacks));
    check "solver-only facts are never passed to reducer collectors"
      (ListPair.allEq (fn (xs,ys) => terms xs ys)
        (!collections,map (map concl) [initial,nested]))
  end
  val _ = order_test true
  val _ = order_test false
  (* No generic provider: solver-only hypotheses still prevent capture. *)
  val x = ``ext_capture_x:bool``
  val capture = ASSUME ``ext_capture_c = (ext_capture_x:bool)``
  val rewrite = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "capture",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => REWR_CONV capture})
  val input = ``\ext_capture_x:bool. ext_capture_c:bool``
  val output = ``\ext_capture_y:bool. ext_capture_x:bool``
  val cv = T.TRAVERSE_WITH_CONTEXT T.ParentFirst
    (data Travrules.EQ_tr [rewrite] [] NONE,T.default_config)
    {reducer_context=[],solver_context=[ASSUME x]}
  val _ = convtest ("solver-only facts protect binders without a provider",
                    cv,input,output)
  val _ = checks := !checks + 1
  val cv = T.TRAVERSE_WITH_CONTEXT T.ParentFirst
    (data Travrules.EQ_tr [rewrite] [] NONE,T.default_config)
    {reducer_context=[ASSUME x],solver_context=[]}
  val _ = convtest ("reducer facts also protect binders without a provider",
                    cv,input,output)
  val _ = checks := !checks + 1
in () end

(* Root selection applies only outside; side conditions recurse normally. *)
val _ = let
  fun ordinary th = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "rule",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => REWR_CONV th})
  val chain = (data Travrules.EQ_tr (map ordinary [ab,bc]) [] NONE,
               T.default_config)
  val _ = check "ROOT_REWRITE takes one root step, not a root fixpoint"
    (same (T.ROOT_REWRITE chain [] a) ab)
  val _ = check "XTRAVERSE iterates at root"
    (same (T.XTRAVERSE chain [] a) (TRANS ab bc))
  val input = ``(ext_wrap:bool -> bool) ext_a``
  val _ = check "ROOT_REWRITE does not visit proper children"
    (result (T.ROOT_REWRITE chain []) input (REFL input))
  val f = ``ext_f:bool -> bool``
  val condition = mk_comb (f,a)
  val fbT = ASSUME (mk_eq (mk_comb (f,b),T))
  val root = ``ext_root:bool``
  val output = ``ext_output:bool``
  val conditional = ASSUME (mk_imp (condition,mk_eq (root,output)))
  val run = Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG
    ("root side condition",conditional) false
  val conditional_reducer = T.CONFIG_REDUCER
    {name=NONE,initial=Fail "root",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,cond_depth,term_ord,...} =>
       run {solver=solver,stack=stack,cond_depth=cond_depth,
            term_ord=term_ord}}
  val xd = (data Travrules.EQ_tr
    [conditional_reducer,ordinary ab,ordinary fbT] [] NONE,
    config NONE [] (SOME 4) NONE)
  val expected = MP conditional
    (EQT_ELIM (TRANS (AP_TERM f ab) fbT))
  val _ = check "root side condition uses full child traversal"
    (same (T.ROOT_REWRITE xd [] root) expected)
  val _ = check "explicit root context entry has the same recursive proof"
    (same (T.ROOT_REWRITE_WITH_CONTEXT xd empty_context root) expected)
  val visited = ref ([] : term list)
  val probe = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "visit",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => fn tm => (visited := !visited @ [tm]; NO_CONV tm)})
  val xd = (data Travrules.EQ_tr [probe] [] NONE,T.default_config)
  val child = ``(ext_inner:bool -> bool) ext_a``
  val parent = mk_comb (``ext_outer:bool -> bool``,child)
  fun precedes x y [] = false
    | precedes x y (h::rest) =
        if aconv h x then List.exists (aconv y) rest
        else precedes x y rest
  val _ = total (T.XTRAVERSE xd []) parent
  val _ = check "parent-first offers parent before children"
    (precedes parent child (!visited))
  val _ = visited := []
  val _ = total (T.TRAVERSE_WITH_CONTEXT (T.ChildFirst quiet)
    xd empty_context) parent
  val _ = check "child-first offers children before parent"
    (precedes child parent (!visited))
  val conjunction = mk_conj (a,T)
  val input = mk_neg conjunction
  val parent_output = mk_imp (a,F)
  val child_output = mk_eq (a,F)
  val parent_rule = ASSUME (mk_eq (input,parent_output))
  val child_rule = ASSUME (mk_eq (conjunction,a))
  val after_child = ASSUME (mk_eq (mk_neg a,child_output))
  val overlap = (data Travrules.EQ_tr
    (map ordinary [parent_rule,child_rule,after_child]) [] NONE,
    T.default_config)
  val _ = check "parent-first overlap proof selects parent rule"
    (same (T.XTRAVERSE overlap [] input) parent_rule)
  val expected = TRANS (AP_TERM negation child_rule) after_child
  val _ = check "child-first overlap proof selects normalized child"
    (same (T.TRAVERSE_WITH_CONTEXT (T.ChildFirst quiet)
      overlap empty_context input) expected)
in () end

(* Eta preservation is policy-selected, excludes logical binder predicates,
   and does not offer the root itself to the child conversion. *)
val _ = let
  val charges = ref 0
  val children = ref ([] : term list)
  val policy = T.charge_only (fn () => charges := !charges + 1)
  fun child tm = (children := !children @ [tm]; NO_CONV tm)
  val input = ``(ext_h:('a -> 'b) -> 'c) (\x:'a. ext_fun x)``
  val output = ``(ext_h:('a -> 'b) -> 'c) ext_fun``
  val _ = convtest ("NORMALIZE_ARGUMENTS contracts eta before descent",
                    T.NORMALIZE_ARGUMENTS policy child,input,output)
  val _ = checks := !checks + 1
  val _ = check "eta normalization charges both changing and stable passes"
    (!charges = 2 andalso
     not (List.exists (aconv input) (!children)))
  val keep = {charge=fn () => (),keep_abstraction=fn _ => true}
  val _ = check "keep_abstraction policy is exposed unchanged"
    (T.keep_abstraction keep input andalso
     not (T.keep_abstraction quiet input))
  val _ = check "selected eta argument retains abstraction"
    (same (T.NORMALIZE_ARGUMENTS keep child input) (REFL input))
  val _ = List.app (fn tm =>
    check "logical binder predicate is not eta contracted"
      (same (T.NORMALIZE_ARGUMENTS quiet child tm) (REFL tm)))
    [``!x:'a. ext_pred x``,``?x:'a. ext_pred x``,``@x:'a. ext_pred x``]
  val abs = mk_abs (``ext_bound:bool``,a)
  val _ = check "normalizing an abstraction rewrites its body only"
    (same (T.NORMALIZE_ARGUMENTS quiet (REWR_CONV ab) abs)
          (ABS ``ext_bound:bool`` ab))
  val probe = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "eta",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => NO_CONV})
  val xd = (data no_rules [probe] [] NONE,T.default_config)
  val _ = convtest ("child-first engine preserves eta head without congs",
    total (T.TRAVERSE_WITH_CONTEXT (T.ChildFirst quiet) xd empty_context),
    input,output)
  val _ = checks := !checks + 1
in () end

(* Failed recursive proofs restore traversal allowances. These are the
   first five ordinary traversal-limit assertions, with explicitly lifted
   inputs. *)
val _ = let
  val side = ``ext_limit_side:bool``
  val unsolved = ``ext_limit_unsolved:bool``
  val side_rule = ASSUME (mk_eq (side,unsolved))
  val events = ref ([] : string list)
  fun event s = events := !events @ [s]
  val reducer = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "limit",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,...} => fn tm =>
       if aconv tm a then
         (event "root";
          ((ignore (solver [] side); raise Fail "unsolved succeeded")
           handle HOL_ERR _ => event "rejected"); ab)
       else if aconv tm b then (event "second"; bc)
       else if aconv tm side then (event "side"; side_rule)
       else NO_CONV tm})
  fun raw n = total (T.XTRAVERSE
    (data no_rules [reducer] [] (SOME n),T.default_config) [])
  val _ = check "zero traversal limit makes no reducer attempt"
    (same (raw 0 a) (REFL a) andalso null (!events))
  val _ = check "failed solver restores one-use allowance"
    (same (raw 1 a) ab)
  val _ = check "failed one-use attempt exact callbacks"
    (!events = ["root","side","rejected"])
  val _ = events := []
  val _ = check "failed recursive proof restores two-use allowance"
    (same (raw 2 a) (TRANS ab bc))
  val _ = check "failed two-use attempt exact callbacks"
    (!events = ["root","side","rejected","second"])
  val solved = ASSUME b
  val conditional = ASSUME (mk_imp (a,p))
  val seen = ref ([] : string list)
  val root = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "pipeline",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,...} => fn tm =>
       if aconv tm p then EQT_INTRO (MP conditional (solver [] a))
       else NO_CONV tm})
  fun sg _ tm = if aconv tm a then ab else REFL tm
  fun fail _ tm = (seen := !seen @ ["first"]; NO_CONV tm)
  fun solve _ tm =
    (seen := !seen @ ["second"];
     if aconv tm b then solved else NO_CONV tm)
  val cfg = config (SOME sg)
    [{name="fails",solve=fail},{name="solves",solve=solve}] NONE NONE
  val cv = T.ROOT_REWRITE (data no_rules [root] [] NONE,cfg) []
  val _ = check "solver pipeline transports rewritten condition proof"
    (same (cv p) (EQT_INTRO (MP conditional (EQ_MP (SYM ab) solved)))
     andalso
     !seen = ["first","second"])
in () end

(* Construction and factory exception scopes are part of the boundary.
   Compare default traversal's exact observations to the unchanged engine;
   extended/root entries must keep their deliberately lazy schedule. *)
val _ = let
  fun run low abort extended = let
    val events = ref ([] : string list)
    fun event s = events := !events @ [s]
    val token = ref ()
    fun label tm = if aconv tm a then "a" else if aconv tm b then "b"
                   else "c"
    val ordinary = Traverse.REDUCER
      {name=NONE,initial=Fail "schedule",
       addcontext=fn (ctxt,_) => (event "collect"; ctxt),
       apply=fn _ => fn tm =>
         (event ("R:" ^ label tm);
          if abort then raise Stop token else
          if aconv tm a then ab else
          if low andalso aconv tm b then bc else NO_CONV tm)}
    fun factory tag : Opening.congproc = fn _ =>
      (event ("relation-" ^ tag); fn _ =>
        (event ("factory-" ^ tag); fn tm =>
          (event (tag ^ ":" ^ label tm); NO_CONV tm)))
    val rules = Travrules.TRAVRULES
      {relations=[Travrules.EQ_preorder],congprocs=[factory "C"],
       weakenprocs=[factory "W"]}
    val cv = if extended then T.TRAVERSE
      (data rules (if low then [] else [T.lift ordinary])
                  (if low then [T.lift ordinary] else []) NONE) [TRUTH]
      else Traverse.TRAVERSE
        {rewriters=if low then [] else [ordinary],
         dprocs=if low then [ordinary] else [],limit=NONE,
         travrules=rules,relation=equality} [TRUTH]
    val _ = check "default collects once before any factory"
      (!events = ["collect"])
    val _ = events := []
    fun apply () = if abort then
      fails "root reducer preserves foreign payload"
        (fn Stop r => Portable.pointer_eq (r,token) | _ => false)
        (fn () => cv a)
      else check "factory schedule proof"
        (same (cv a) (if low then TRANS ab bc else ab))
    val _ = apply ()
    val first = !events
    val _ = apply ()
    val _ = check "factories refresh but collectors do not on reuse"
      (!events = first @ first)
  in first end
  val _ = List.app (fn (low,abort) =>
    check "lifted default factory/reducer schedule equals ordinary"
      (run low abort true = run low abort false))
    [(false,false),(true,false),(false,true)]
  val events = ref ([] : string list)
  fun event s = events := !events @ [s]
  val probe = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "lazy",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => fn tm =>
       (event (if aconv tm a then "R:a" else "R:b");
        if aconv tm a then ab else NO_CONV tm)})
  fun factory tag : Opening.congproc = fn _ =>
    (event ("relation-" ^ tag); fn _ =>
      (event ("factory-" ^ tag); fn tm =>
        (event tag; NO_CONV tm)))
  val rules = Travrules.TRAVRULES
    {relations=[Travrules.EQ_preorder],congprocs=[factory "C"],
     weakenprocs=[factory "W"]}
  val xd = (data rules [probe] [] NONE,T.default_config)
  val _ = check "root avoids unused congruence/weakener factories"
    (same (T.ROOT_REWRITE xd [] a) ab andalso
     !events = ["relation-C","relation-W","R:a"])
  val _ = events := []
  val _ = check "extended factories run lazily after root attempts"
    (same (T.XTRAVERSE xd [] a) ab andalso
     !events = ["relation-C","relation-W","R:a","R:b",
                "factory-C","C","factory-W","W"])
  val ready = ref false
  val builds = ref 0
  val gated : Opening.congproc = fn _ => fn _ =>
    (builds := !builds + 1;
     if !ready then REWR_CONV bc else NO_CONV)
  val changes = T.lift (Traverse.REDUCER
    {name=NONE,initial=Fail "gated",addcontext=fn (ctxt,_) => ctxt,
     apply=fn _ => fn tm =>
       if aconv tm a then (ready := true; ab) else NO_CONV tm})
  val gated_rules = Travrules.TRAVRULES
    {relations=[Travrules.EQ_preorder],congprocs=[gated],weakenprocs=[]}
  val gd = data gated_rules [changes] [] NONE
  val saved = T.TRAVERSE gd []
  val _ = check "default factory rejection precedes root mutation"
    (same (saved a) ab andalso !builds = 1 andalso !ready)
  val _ = ready := false
  val extended_th = T.XTRAVERSE (gd,T.default_config) [] a
  val _ = check "extended lazy factory sees root mutation"
    (same extended_th (TRANS ab bc) andalso !builds = 2)
  val token = ref ()
  fun bad error : Opening.congproc = fn _ => fn _ => raise error
  fun cv error = T.TRAVERSE
    (data (Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[bad error],
        weakenprocs=[]}) [probe] [] NONE) []
  val _ = check "foreign factory exception retains rejection scope"
    (same (cv (Stop token) a) ab)
  val _ = fails "factory Interrupt retains shared constructor"
    (fn Portable.Interrupt => true | _ => false)
    (fn () => cv Portable.Interrupt a)
  val collections = ref 0
  val ordinary = Traverse.REDUCER
    {name=NONE,initial=Private (token,[]),
     addcontext=fn _ => (collections := !collections + 1; raise Stop token),
     apply=fn _ => NO_CONV}
  val d = data no_rules [T.lift ordinary] [] NONE
  val exact = fn Stop r => Portable.pointer_eq (r,token) | _ => false
  val _ = fails "default initial collector throws at construction"
    exact (fn () => T.TRAVERSE d [TRUTH])
  val saved = T.XTRAVERSE (d,T.default_config) [TRUTH]
  val _ = check "refreshing construction does not run throwing collector"
    (!collections = 1)
  val _ = fails "refreshing collector throws at first application"
    exact (fn () => saved a)
  val _ = fails "refreshing collector throws again at second application"
    exact (fn () => saved a)
  val _ = check "throwing collector is not cached" (!collections = 3)
  val traced = ref ([] : term list)
  fun listener (_,Trace.REDUCE (_,tm)) = traced := tm :: !traced
    | listener _ = ()
  val _ = Listener.add_listener Trace.trace_hook ("TraverseExt test",listener)
  val _ = Portable.finally
    (fn () => ignore
      (Listener.remove_listener Trace.trace_hook "TraverseExt test"))
    (HOLFlags.trace ("simplifier.trace",4)
      (fn () => ignore (total (T.XTRAVERSE
        (data no_rules [] [] NONE,T.default_config) []) a))) ()
  val _ = check "extension uses the original shared Trace listener"
    (terms (!traced) [a])
in () end

(* Observer failure must survive even conditional wrappers and HOL_ERR
   fallback dispatch. Observation itself must not introduce charge calls. *)
val _ = let
  val rule = ASSUME (mk_imp (p,mk_eq (a,b)))
  val runner = Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG
    ("observed failed condition",rule) false
  val applications = ref 0
  val solves = ref 0
  val reducer = T.CONFIG_REDUCER
    {name=NONE,initial=Fail "observer",addcontext=fn (ctxt,_) => ctxt,
     apply=fn {solver,stack,cond_depth,term_ord,...} => fn tm =>
       (applications := !applications + 1;
        runner {solver=solver,stack=stack,cond_depth=cond_depth,
                term_ord=term_ord} tm)}
  val cfg = config (SOME (fn _ => REFL))
    [{name="fails",solve=fn _ => fn tm =>
      (solves := !solves + 1; NO_CONV tm)}] (SOME 4) NONE
  val xd = (data no_rules [reducer] [] NONE,cfg)
  val charges = ref 0
  val visits = ref ([] : term list)
  fun charge () = charges := !charges + 1
  fun observe tm = visits := !visits @ [tm]
  val cv = T.CHILD_FIRST_WITH_OBSERVER observe (T.charge_only charge)
    xd empty_context
  val _ = check "failed side condition is observed, without extra charges"
    (result cv a (REFL a) andalso terms (!visits) [a,a,p,a] andalso
     !charges = 3 andalso !applications = 1 andalso !solves = 1)
  val _ = charges := 0
  val _ = applications := 0
  val _ = solves := 0
  val without = T.TRAVERSE_WITH_CONTEXT
    (T.ChildFirst (T.charge_only charge)) xd empty_context
  val _ = check "observer does not alter reducer/solver/charge counts"
    (result without a (REFL a) andalso !charges = 3 andalso
     !applications = 1 andalso !solves = 1)
  val token = ref ()
  val foreign = Stop token
  val holpayload = Feedback.mk_hol_error
    "TraverseExtTest" "observer" locn.Loc_Unknown "original payload"
  val holerr = HOL_ERR holpayload
  val exceptions =
    [("HOL_ERR",holerr,fn HOL_ERR payload =>
       Portable.pointer_eq (payload,holpayload) | _ => false),
     ("foreign",foreign,fn Stop r => Portable.pointer_eq (r,token)
                         | _ => false),
     ("Interrupt",Portable.Interrupt,
                  fn Portable.Interrupt => true | _ => false)]
  fun abort (label,error,predicate) = let
    val visits = ref ([] : term list)
    val n = ref 0
    val _ = applications := 0
    val _ = solves := 0
    fun visit tm =
      (visits := !visits @ [tm]; if aconv tm p then raise error else ())
    val observed = T.CHILD_FIRST_WITH_OBSERVER visit
      (T.charge_only (fn () => n := !n + 1)) xd empty_context
    val _ = fails ("observer preserves " ^ label ^ " identity through runner")
      predicate (fn () => observed a)
    val _ = check ("observer abort counts: " ^ label)
      (terms (!visits) [a,a,p] andalso !n = 2 andalso
       !applications = 1 andalso !solves = 0)
    val _ = applications := 0
    val _ = visits := []
    val _ = n := 0
    fun stop () = (n := !n + 1; if !n = 2 then raise error else ())
    val charged = T.CHILD_FIRST_WITH_OBSERVER
      (fn tm => visits := !visits @ [tm]) (T.charge_only stop)
      xd empty_context
    val _ = fails ("charge preserves " ^ label ^ " identity")
      predicate (fn () => charged a)
    val _ = check ("charge abort precedes reducer attempt: " ^ label)
      (terms (!visits) [a,a] andalso !n = 2 andalso !applications = 0)
  in () end
  val _ = List.app abort exceptions
in () end

val _ = print ("TraverseExt focused checks: " ^
  Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
