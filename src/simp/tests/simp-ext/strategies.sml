(* Maintained configured-strategy regressions.
   Provenance: src/selftest.sml strategy surface, solver/looper pipeline,
   child-first traversal, and mutual/counting global simplification groups.
   Additive: the 642 native checks remain in place. Bound replay and nested
   directive wrappers have separate coverage; no ordinary-set promotion. *)
structure strategies =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure S = simpExtLib
val ext_bool_ss = simpExtLib.lift_simpset boolSimps.bool_ss
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val saved_context = Context.snapshot ()
val _ = new_theory "simpExtStrategies"

val checks = ref 0
val validations = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same a b = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun ordered_goal ((as1,w1),(as2,w2)) =
  list_eq aconv as1 as2 andalso aconv w1 w2
fun printgoal (asl,w) = "[" ^
  String.concatWith ", " (map term_to_string asl) ^ "] |- " ^
  term_to_string w
val global_th = EXISTS
  (``?f:bool -> bool. !x. f x = x``,``\x:bool. x``)
  (GEN ``x:bool`` (BETA_CONV ``(\x:bool. x) x``))
fun closed_goal (asl,w) = let
  val th = Tactical.prove_goal
    ((asl,w),ASM_REWRITE_TAC [boolTheory.EXCLUDED_MIDDLE,global_th] THEN
       FIRST_ASSUM
         (CONTR_TAC o REWRITE_RULE [boolTheory.EXCLUDED_MIDDLE,global_th]))
in List.foldl (fn (a,th) => ADD_ASSUM a th) th asl end
fun tactic_with prove name tac goal expected = let
  val (actual,validate) = runtac (VALID tac) goal
  val equal_goals = ListPair.allEq ordered_goal (actual,expected)
  val _ = if equal_goals then () else
    (print ("Actual goals: " ^
       String.concatWith "; " (map printgoal actual) ^ "\n");
     print ("Expected goals: " ^
       String.concatWith "; " (map printgoal expected) ^ "\n"))
  val _ = check (name ^ ": ordered goals") equal_goals
  (* These are real kernel proofs, not mk_thm/oracle stand-ins. Force the
     entire residual context into the proofs to exercise hypothesis repair. *)
  val th = validate (map prove actual)
  val _ = validations := !validations + 1
in check (name ^ ": validation and full hypotheses")
     (same th (prove goal)) end
fun tactic name tac goal expected =
  tactic_with closed_goal name tac goal expected
fun conversion name cv input expected =
  check name (same (QCONV (TRY_CONV cv) input) expected)
fun fails name pred f =
  check name (case Exn.capture f () of Exn.Exn e => pred e
                                    | Exn.Res _ => false)
fun reject () = raise mk_HOL_ERR "strategies" "probe" "not applicable"
fun em p = SPEC p boolTheory.EXCLUDED_MIDDLE
fun noasms mode ss = S.GEN_SIMP_TAC mode ss [markerLib.NoAsms]
val safe = {safe=true}
val unsafe = {safe=false}
val target_th = em ``strategy_goal_p:bool``
val target = concl target_th
val goal = ([],target)
val cfg = {droptrues=true,elimvars=false,strip=false,oldestfirst=true}
fun xcfg concl rebuild premises =
  {base=cfg,concl_in_fixpoint=concl,imp_rebuild=rebuild,
   imp_premises=premises}
fun global mode concl rebuild premises ss =
  S.GEN_GLOBAL_SIMP_TAC mode (xcfg concl rebuild premises) ss []

(* Final selection is independent of the unsafe condition-solver list. *)
val _ = let
  val calls = ref ([] : string list)
  fun exact name th : E.ssolver =
    {name=name,solve=fn _ => fn tm =>
       (calls := !calls @ [name];
        if aconv tm (concl th) then th else reject ())}
  val ss = S.empty_ss
    |> S.add_safe_solver (exact "safe final" target_th)
    |> S.add_unsafe_solver (exact "unsafe final" target_th)
  val _ = tactic "safe selects safe final only" (noasms safe ss) goal []
  val _ = check "safe final callback list" (!calls = ["safe final"])
  val _ = calls := []
  val _ = tactic "unsafe selects unsafe final only"
    (noasms unsafe ss) goal []
  val _ = check "unsafe final callback list" (!calls = ["unsafe final"])
  val _ = calls := []
  val only_safe = S.set_unsafe_solvers [] ss
  val _ = tactic "unsafe never falls back to safe final"
    (noasms unsafe only_safe) goal [goal]
  val only_unsafe = S.set_safe_solvers [] ss
  val _ = tactic "safe never falls back to unsafe final"
    (noasms safe only_unsafe) goal [goal]
  val _ = check "unselected solver lists remain untouched" (null (!calls))
  val p = ``strategy_context_p:bool``
  val imp = mk_imp (p,target)
  fun context {context_thms,...} tm = let
    fun find t = case List.find (aconv t o concl) context_thms of
      SOME th => th | NONE => reject ()
  in if aconv tm target then MP (find imp) (find p) else reject () end
  val contextual = S.add_safe_solver
    {name="context MP",solve=context} S.empty_ss
  val _ = tactic "final solver receives full assumption context"
    (S.GEN_SIMP_TAC safe contextual []) ([p,imp],target) []
  val supplied_p = REFL ``strategy_supplied_x:bool``
  val supplied_imp = DISCH (concl supplied_p) target_th
  val supplied_ss = S.add_unsafe_solver
    {name="supplied MP",solve=fn {context_thms,...} => fn tm =>
       if aconv tm target andalso
          List.exists (fn th => same th supplied_p) context_thms andalso
          List.exists (fn th => same th supplied_imp) context_thms
       then MP supplied_imp supplied_p else reject ()} S.empty_ss
  val _ = tactic "global final solver receives supplied kernel theorems"
    (S.GEN_GLOBAL_SIMP_TAC unsafe (xcfg false false false) supplied_ss
       [supplied_p,supplied_imp]) goal []
  val context_solver = S.mk_tactic_solver
    ("tactic context",FIRST_ASSUM ACCEPT_TAC)
  val result = #solve context_solver
    {stack=[],context_thms=[target_th],recurse=REFL} target
in check "mk_tactic_solver discharges temporary context assumptions"
     (same result target_th) end

(* Safe tactics still use UNSAFE condition solvers, including after an
   explicit subgoaler transforms a condition to a residual proposition. *)
val _ = let
  val condition_th = em ``strategy_side_p:bool``
  val condition = concl condition_th
  val residual_th = em ``strategy_side_q:bool``
  val residual = concl residual_th
  val input = mk_cond (condition,``strategy_x:bool``,``strategy_y:bool``)
  val output = ``strategy_x:bool``
  val rule = DISCH condition
    (REWRITE_CONV [ASSUME condition] input)
  val expected = MP rule condition_th
  val calls = ref ([] : string list)
  fun unsafe_solve _ tm =
    (calls := !calls @ ["condition"];
     if aconv tm condition then condition_th else reject ())
  fun safe_solve _ tm =
    (calls := !calls @ ["final"];
     if aconv tm (mk_eq (output,output)) then REFL output else reject ())
  val ss = S.++ (S.empty_ss,S.rewrites [rule])
    |> S.set_unsafe_solvers [{name="condition",solve=unsafe_solve}]
    |> S.set_safe_solvers [{name="final",solve=safe_solve}]
  val _ = conversion "unsafe condition proves full closed conversion"
    (S.SIMP_CONV ss []) input expected
  val _ = check "safe solvers are not conversion condition solvers"
    (!calls = ["condition"])
  val _ = calls := []
  val eqgoal = ([],mk_eq (input,output))
  val _ = tactic "safe tactic uses unsafe conditions and safe final"
    (noasms safe ss) eqgoal []
  val _ = check "condition precedes safe final"
    (!calls = ["condition","final"])
  val _ = calls := []
  val safe_only = ss |> S.set_unsafe_solvers []
  val _ = conversion "safe-only list cannot discharge rewrite conditions"
    (S.SIMP_CONV safe_only []) input (REFL input)
  val _ = check "safe-only list was not consulted" (null (!calls))
  val eq = TRANS (EQT_INTRO condition_th) (SYM (EQT_INTRO residual_th))
  val subgoals = ref 0
  val stacks = ref ([] : term list list)
  val ss = ss
    |> S.set_subgoaler (fn {stack,...} => fn tm =>
         (subgoals := !subgoals + 1; stacks := stack :: !stacks;
          if aconv tm condition then eq else REFL tm))
    |> S.set_unsafe_solvers
         [{name="residual",solve=fn _ => fn tm =>
             if aconv tm residual then residual_th else reject ()}]
  val _ = conversion "configured subgoaler plus residual solver proof"
    (S.SIMP_CONV ss []) input
    (MP rule (EQ_MP (SYM eq) residual_th))
  val _ = check "subgoaler sees the conditional stack"
    (!subgoals = 1 andalso
     list_eq (list_eq aconv) (!stacks) [[condition]])
  val _ = tactic "safe global traversal uses unsafe condition solver"
    (global safe false false false ss) eqgoal []
  val replaced = S.set_subgoaler (fn _ => REFL) ss
  val _ = conversion "subgoaler setter replaces the previous callback"
    (S.SIMP_CONV replaced []) input (REFL input)
  val _ = conversion "subgoaler replacement leaves old set reusable"
    (S.SIMP_CONV ss []) input expected
in () end

(* List setters replace, preserve order, deduplicate names at first use;
   additive solver registration does not replace an existing callback. *)
val _ = List.app (fn mode => let
  val label = if #safe mode then "safe" else "unsafe"
  val set = if #safe mode then S.set_safe_solvers else S.set_unsafe_solvers
  val add = if #safe mode then S.add_safe_solver else S.add_unsafe_solver
  val seen = ref ([] : string list)
  fun solver name tag succeed : E.ssolver =
    {name=name,solve=fn _ => fn tm =>
       (seen := !seen @ [tag];
        if succeed andalso aconv tm target then target_th else reject ())}
  val old = solver "old" "old" true
  val first = solver "first" "first" false
  val last = solver "last" "last" true
  val duplicate = solver "last" "duplicate" true
  val original = set [old] S.empty_ss
  val ss = set [first,last,duplicate] original |> add duplicate
  fun run suffix ss expected tags =
    (seen := [];
     tactic (label ^ " setter " ^ suffix) (noasms mode ss) goal expected;
     check (label ^ " setter " ^ suffix ^ ": callback order")
       (!seen = tags))
  val _ = run "replacement/dedup" ss [] ["first","last"]
  val _ = run "saved original is immutable" original [] ["old"]
  val _ = run "reordering" (set [last,first] ss) [] ["last"]
  val _ = run "removal" (S.remove_solver "last" ss) [goal] ["first"]
  val _ = run "empty list" (set [] ss) [goal] []
  val both = original |> S.set_safe_solvers [old]
                      |> S.set_unsafe_solvers [old]
  val _ = run "remove clears both lists" (S.remove_solver "old" both)
    [goal] []
in () end) [safe,unsafe]

(* Live NONE versus explicit depth on saved conversions AND saved tactics.
   Open fixtures compare every hypothesis in the recursive kernel proof. *)
val _ = let
  val input = ``(strategy_depth_f:bool -> bool) strategy_depth_x``
  val output = ``strategy_depth_y:bool``
  val p = ``strategy_depth_p = strategy_depth_p'``
  val q = ``strategy_depth_q = strategy_depth_q'``
  val r0 = ASSUME (mk_imp (p,mk_eq (input,output)))
  val r1 = ASSUME (mk_imp (q,mk_eq (p,T)))
  val r2 = ASSUME (mk_eq (q,T))
  val expected = MP r0 (EQT_ELIM (MP r1 (EQT_ELIM r2)))
  val ss = S.++ (ext_pure_ss,S.rewrites [r0,r1,r2])
  val live = E.XTRAVERSE (S.xtraversedata_for_ss ss) []
  val explicit = E.XTRAVERSE
    (S.xtraversedata_for_ss (S.set_cond_depth 40 ss)) []
  val zero = E.XTRAVERSE
    (S.xtraversedata_for_ss (S.set_cond_depth 0 ss)) []
  val tac = noasms unsafe ss
  val fixed = noasms unsafe (S.set_cond_depth 40 ss)
  val zero_tac = noasms unsafe (S.set_cond_depth 0 ss)
  val g = (hyp expected,concl expected)
  val simplified = [(hyp expected,mk_eq (output,output))]
  fun depth_proof (asl,w) = let
    val th = if aconv w (concl expected) then expected else REFL output
  in List.foldl (fn (a,th) => ADD_ASSUM a th) th asl end
  val pin = tactic_with depth_proof
  val saved = !Cond_rewr.stack_limit
  fun run n = let
    val _ = Cond_rewr.stack_limit := n
    val prefix = "saved depth " ^ Int.toString n
    val _ = conversion (prefix ^ ": live proof") live input
      (if n = 0 then REFL input else expected)
    val _ = conversion (prefix ^ ": fixed 40 proof") explicit input expected
    val _ = conversion (prefix ^ ": fixed zero proof") zero input (REFL input)
    val _ = pin (prefix ^ ": live tactic") tac g
      (if n = 0 then [g] else simplified)
    val _ = pin (prefix ^ ": explicit tactic") fixed g simplified
    val _ = pin (prefix ^ ": zero tactic") zero_tac g [g]
  in check (prefix ^ ": overrides never mutate shared depth")
       (!Cond_rewr.stack_limit = n) end
in Portable.finally (fn () => Cond_rewr.stack_limit := saved)
     (fn () => List.app run [0,40,0]) () end

(* Permutative order is explicit per set, shared defaults are unaffected;
   both parent/child traversal and saved tactics consume the setting. *)
val _ = let
  fun reverse pair = case Cond_rewr.ac_term_ord pair of
      LESS => GREATER | GREATER => LESS | EQUAL => EQUAL
  val input = ``strategy_order_x:'a = strategy_order_y``
  val output = ``strategy_order_y:'a = strategy_order_x``
  val expected = REWR_CONV boolTheory.EQ_SYM_EQ input
  val base = S.++ (ext_pure_ss,S.rewrites [boolTheory.EQ_SYM_EQ])
  val ss = S.set_term_ord reverse base
  val cv = S.SIMP_CONV ss []
  val policy = E.charge_only (fn () => ())
  val _ = conversion "default order rejects the reverse permutation"
    (S.SIMP_CONV base []) input (REFL input)
  val _ = conversion "explicit term order gives complete permutation proof"
    cv input expected
  val _ = conversion "child-first forwards explicit term order"
    (S.SIMP_CONV_CHILD_FIRST policy ss []) input expected
  val tac = noasms unsafe ss
  val g = ([input],input)
  val _ = List.app (fn _ => tactic "saved explicit order tactic"
    tac g [([input],output)]) [1,2]
  val _ = conversion "configured order did not mutate default order"
    (S.SIMP_CONV base []) input (REFL input)
in () end

(* Looper replacement retains its slot; set replaces the whole list.
   Limits count successful rounds, are shared across sibling goals, and
   are fresh on every application of a saved tactic. *)
val _ = let
  val p = ``strategy_loop_p:bool``
  val q = ``strategy_loop_q:bool``
  val r = ``strategy_loop_r:bool``
  val asl = [p,q,r]
  val g = (asl,mk_conj (p,mk_conj (q,r)))
  val seen = ref ([] : string list)
  fun failing tag _ _ = (seen := !seen @ [tag]; reject ())
  fun splitting tag _ g = (seen := !seen @ [tag]; CONJ_TAC g)
  val ss = S.empty_ss
    |> S.add_looper ("first",failing "old")
    |> S.add_looper ("second",splitting "second")
    |> S.add_looper ("first",failing "replacement")
    |> S.limit 1
  val _ = tactic "looper replacement keeps first position"
    (noasms unsafe ss) g [(asl,p),(asl,mk_conj (q,r))]
  val _ = check "replaced callback and registration order"
    (!seen = ["replacement","second"])
  val _ = seen := []
  val single = S.set_looper ("only",splitting "only") ss
  val _ = tactic "set_looper removes all previous loopers"
    (noasms unsafe single) g [(asl,p),(asl,mk_conj (q,r))]
  val _ = check "only replacement looper executed" (!seen = ["only"])
  val _ = seen := []
  val _ = tactic "del_looper removes singleton"
    (noasms unsafe (S.del_looper "only" single)) g [g]
  val _ = check "deleted looper was not called" (null (!seen))
  val loop = S.set_looper ("split",splitting "split") S.empty_ss
  val limited = noasms unsafe (S.limit 1 loop)
  val _ = List.app (fn _ => tactic "saved one-round budget resets"
    limited g [(asl,p),(asl,mk_conj (q,r))]) [1,2]
  val restart_solver_calls = ref 0
  val restart_looper_calls = ref 0
  val restart = S.empty_ss
    |> S.add_unsafe_solver
         {name="restart first leaf",solve=fn _ => fn tm =>
            (restart_solver_calls := !restart_solver_calls + 1;
             if aconv tm p then ASSUME p else reject ())}
    |> S.add_looper ("restart conjunction",fn _ => fn g =>
         (restart_looper_calls := !restart_looper_calls + 1; CONJ_TAC g))
  val _ = tactic "looper restarts traversal and solvers on every subgoal"
    (noasms unsafe restart) ([p],mk_conj (p,target)) [([p],target)]
  val _ = check "restart final-solver and looper counts"
    (!restart_solver_calls = 3 andalso !restart_looper_calls = 2)
  val _ = seen := []
  val _ = tactic "zero budget makes no looper attempt"
    (noasms unsafe (S.limit 0 loop)) g [g]
  val _ = check "zero looper callback count" (null (!seen))
  val _ = tactic "two rounds reach both conjunctions"
    (noasms unsafe (S.limit 2 loop)) g [(asl,p),(asl,q),(asl,r)]
  val _ = tactic "unlimit restores full recursion"
    (noasms unsafe (S.unlimit (S.limit 0 loop))) g
    [(asl,p),(asl,q),(asl,r)]
  val skipped = S.empty_ss
    |> S.add_looper ("unchanged",fn _ => fn _ => raise UNCHANGED)
    |> S.add_looper ("split",fn _ => CONJ_TAC)
    |> S.limit 1
in tactic "looper UNCHANGED permits the next candidate"
     (noasms unsafe skipped) g [(asl,p),(asl,mk_conj (q,r))] end

(* Foreign exceptions preserve payload identity, unlike normal HOL_ERR
   candidate rejection. Invalid final proofs must not be accepted. *)
val _ = let
  exception Stop of unit ref
  val token = ref ()
  fun exact (Stop r) = Portable.pointer_eq (r,token) | exact _ = false
  val stopped = S.set_looper
    ("foreign exception",fn _ => fn _ => raise Stop token) S.empty_ss
  val _ = fails "looper propagates foreign exception payload" exact
    (fn () => runtac (VALID (noasms unsafe stopped)) goal)
  val ss = S.set_unsafe_solvers
    [{name="foreign solver",solve=fn _ => fn _ => raise Stop token}]
    S.empty_ss
  val _ = fails "final solver propagates foreign exception payload" exact
    (fn () => runtac (VALID (noasms unsafe ss)) goal)
  val _ = fails "child-first tactic propagates charge exception payload" exact
    (fn () => runtac (VALID (S.GEN_SIMP_TAC_CHILD_FIRST
       (E.charge_only (fn () => raise Stop token)) unsafe
       ext_pure_ss [])) goal)
  val _ = fails "child-first global propagates charge exception payload" exact
    (fn () => runtac (VALID (S.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST
       (E.charge_only (fn () => raise Stop token)) unsafe
       (xcfg true false false) ext_pure_ss [])) goal)
  fun solver th : E.ssolver = {name="invalid",solve=fn _ => fn _ => th}
  val bad_hyp = ADD_ASSUM ``strategy_unavailable:bool`` target_th
  val _ = List.app (fn (name,th) => let
    val bad = S.set_unsafe_solvers [solver th] S.empty_ss
    val _ = tactic (name ^ " is rejected") (noasms unsafe bad) goal [goal]
    val good : E.ssolver =
      {name="valid fallback",solve=fn _ => fn _ => target_th}
  in tactic (name ^ " permits valid fallback")
       (noasms unsafe (S.add_unsafe_solver good bad)) goal [] end)
    [("wrong final conclusion",TRUTH),("unavailable final hypothesis",bad_hyp)]
  val condition = concl (em ``strategy_invalid_side:bool``)
  val input = mk_cond
    (condition,``strategy_bad_x:bool``,``strategy_bad_y:bool``)
  val rule = DISCH condition (REWRITE_CONV [ASSUME condition] input)
  val bad = S.++ (S.empty_ss,S.rewrites [rule])
    |> S.set_unsafe_solvers [solver TRUTH]
in conversion "wrong condition proof cannot justify a rewrite"
     (S.SIMP_CONV bad []) input (REFL input) end

(* Child-first term order is observable at overlapping parents, not merely
   a callback count. Both tactic families preserve ordered full contexts. *)
val _ = let
  fun proof tm = Tactical.prove (tm,REWRITE_TAC [])
  val rules =
    [proof ``~(p /\ T) = (p ==> F)``,
     proof ``(p /\ T) = p``, proof ``(~p) = (p = F)``]
  val input = ``~(strategy_overlap_q /\ T)``
  val parent = ``strategy_overlap_q ==> F``
  val child = ``strategy_overlap_q = F``
  val ss = S.++ (ext_pure_ss,S.rewrites rules)
  val charges = ref 0
  val policy = E.charge_only (fn () => charges := !charges + 1)
  val _ = conversion "parent-first overlap kernel proof"
    (S.SIMP_CONV ss []) input (proof (mk_eq (input,parent)))
  val _ = conversion "child-first overlap kernel proof"
    (S.SIMP_CONV_CHILD_FIRST policy ss []) input
    (proof (mk_eq (input,child)))
  val g = ([``~strategy_overlap_q``],input)
  val child_tac = S.GEN_SIMP_TAC_CHILD_FIRST policy unsafe ss
    [markerLib.NoAsms]
  val _ = List.app (fn _ => tactic "saved child-first overlap tactic"
    child_tac g [([``~strategy_overlap_q``],child)]) [1,2]
  (* No assumptions: equality of the two equivalent formulas is closed. *)
  val g = ([],mk_eq (input,child))
  val global_child = S.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST policy unsafe
    (xcfg true false false) ss []
  val _ = List.app (fn _ => tactic "saved child-first global overlap"
    global_child g [([],mk_eq (child,child))]) [1,2]
in check "child-first strategy actually charged work" (!charges > 0) end

(* Global mutual context, premise extraction, root rebuilding and counted
   pass schedule. Conversions below return only kernel-certified equalities. *)
val _ = let
  val target = concl global_th
  val mutual = ([``P (strategy_a:'a):bool``,``strategy_a:'a = strategy_b``],
                target)
  val mutual_expected =
    [([``P (strategy_b:'a):bool``,``strategy_a:'a = strategy_b``],target)]
  val _ = tactic "global later assumptions simplify earlier ones"
    (global unsafe false false false ext_bool_ss)
    mutual mutual_expected
  val premise = ([],mk_imp (``P (strategy_a:'a):bool``,
    mk_imp (``strategy_a:'a = strategy_b``,target)))
  val _ = tactic "imp_premises false keeps leading implications"
    (TRY (global unsafe false false false ext_bool_ss))
    premise [premise]
  val _ = tactic "imp_premises true supplies the mutual fixpoint"
    (global unsafe false false true ext_bool_ss) premise
    [([``strategy_a:'a = strategy_b``,``P (strategy_b:'a):bool``],target)]
  val a = ``strategy_schedule_a:bool``
  val b0 = ``strategy_schedule_b /\ T``
  val b1 = ``strategy_schedule_b:bool``
  val c = ``strategy_schedule_c:bool``
  val counts = Array.array (4,0)
  fun inc i = Array.update (counts,i,Array.sub (counts,i) + 1)
  fun schedule _ _ tm =
    if aconv tm a then (inc 0; NO_CONV tm)
    else if aconv tm b0 then (inc 1; REWRITE_CONV [] tm)
    else if aconv tm b1 then (inc 2; NO_CONV tm)
    else if aconv tm c then (inc 3; NO_CONV tm)
    else NO_CONV tm
  val ss = S.++ (S.empty_ss,S.conv_ss
    {name="counting schedule",key=NONE,trace=0,conv=schedule})
  val g = ([a,b0,c],target)
  val _ = tactic "counted global passes preserve assumption order"
    (global unsafe false false false ss) g [([a,b1,c],target)]
  val _ = check "counting skips provably fixed tail"
    (List.tabulate (4,fn i => Array.sub (counts,i)) = [1,1,1,2])
  val conclusion_calls = ref 0
  val ss = S.++ (ss,S.conv_ss
    {name="conclusion pass probe",key=NONE,trace=0,
     conv=fn _ => fn _ => fn tm =>
       (if aconv tm target then conclusion_calls := !conclusion_calls + 1
        else (); NO_CONV tm)})
  val _ = tactic "conclusion participates in every counted pass"
    (global unsafe true false false ss) g [([a,b1,c],target)]
  val _ = check "two counted conclusion passes" (!conclusion_calls = 2)
  val nested = ref false
  val expansions = ref 0
  fun noop _ _ tm =
    if aconv tm a then
      if !nested then (nested := false; NO_CONV tm)
      else (nested := true; expansions := !expansions + 1;
            SYM (REWRITE_CONV [] (mk_conj (a,T))))
    else NO_CONV tm
  val noop_ss = S.++ (S.empty_ss,S.conv_ss
    {name="structural net noop",key=NONE,trace=0,conv=noop})
  val noop_cfg =
    {base={droptrues=true,elimvars=false,strip=true,oldestfirst=true},
     concl_in_fixpoint=false,imp_rebuild=false,imp_premises=false}
  val _ = tactic "structural net-noop global pass terminates"
    (S.GEN_GLOBAL_SIMP_TAC unsafe noop_cfg noop_ss [])
    ([a],target) [([a],target)]
  val _ = check "net-noop needs no second assumption pass"
    (!expansions = 1)
  val mode_ss = S.set_unsafe_solvers
    [{name="global unsafe final",solve=fn _ => fn tm =>
        if aconv tm target then global_th else reject ()}] S.empty_ss
  val _ = tactic "safe global excludes unsafe final proof"
    (global safe true false false mode_ss) ([],target) [([],target)]
  val _ = tactic "unsafe global accepts unsafe final proof"
    (global unsafe true false false mode_ss) ([],target) []
  val asm0 = ``strategy_gate_asm /\ T``
  val asm1 = ``strategy_gate_asm:bool``
  val concl0 = mk_conj (target,T)
  val unlocked = ref false
  fun gate _ _ tm =
    if aconv tm concl0 then (unlocked := true; REWRITE_CONV [] tm)
    else if !unlocked andalso aconv tm asm0 then REWRITE_CONV [] tm
    else NO_CONV tm
  val gate_ss = S.++ (S.empty_ss,S.conv_ss
    {name="conclusion gate",key=NONE,trace=0,conv=gate})
  val _ = tactic "default global conclusion stays outside fixpoint"
    (global unsafe false false false gate_ss) ([asm0],concl0)
    [([asm0],target)]
  val _ = unlocked := false
  val saved = global unsafe true false false gate_ss
  val _ = List.app (fn _ =>
    (unlocked := false;
     tactic "saved conclusion fixpoint restarts assumptions"
       saved ([asm0],concl0) [([asm1],target)])) [1,2]
  val p = concl (em ``strategy_root_p:bool``)
  val root = mk_imp (p,target)
  val root_calls = ref 0
  fun rebuild _ _ tm =
    if aconv tm root then
      (root_calls := !root_calls + 1;
       REWR_CONV (GSYM boolTheory.CONTRAPOS_THM) tm)
    else NO_CONV tm
  val root_ss = S.++ (S.empty_ss,S.conv_ss
    {name="root implication rebuild",key=SOME ([],root),trace=0,
     conv=rebuild})
  val _ = tactic "imp_rebuild false leaves root wrapper alone"
    (global unsafe false false false root_ss) ([p],target) [([p],target)]
  val _ = check "disabled rebuild callback count" (!root_calls = 0)
  val saved = global unsafe false true false root_ss
  val _ = List.app (fn _ => tactic "saved root rebuild contrapositive"
    saved ([p],target) [([mk_neg target],mk_neg p)]) [1,2]
  val _ = check "root rebuilt once per saved tactic application"
    (!root_calls = 2)
  val side = ``(strategy_root_P:bool -> bool) (T /\ T)``
  val rule = ASSUME (mk_imp (side,mk_eq (root,``strategy_root_result:bool``)))
  val fact = ASSUME ``(strategy_root_P:bool -> bool) T``
  val side_ss = S.++ (ext_pure_ss,
    S.rewrites [boolTheory.AND_CLAUSES,rule])
  val side_proof = EQ_MP
    (SYM (AP_TERM ``strategy_root_P:bool -> bool``
       (REWRITE_CONV [] ``T /\ T``))) fact
  val _ = conversion "ROOT_REWRITE traverses conditional premises fully"
    (E.ROOT_REWRITE (S.xtraversedata_for_ss side_ss) [fact]) root
    (MP rule side_proof)
in () end

val _ = print ("simpExtLib strategy checks: " ^ Int.toString (!checks) ^
  "; executed validations: " ^ Int.toString (!validations) ^ "\n")
val _ = Context.restore saved_context
val _ = OS.Process.exit OS.Process.success

end (* struct *)
