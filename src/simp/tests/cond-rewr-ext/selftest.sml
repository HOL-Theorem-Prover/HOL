(* Ordinary construction is the direct comparison, never an
   extension projection. All successful proofs compare hypotheses too. *)
open HolKernel Parse boolLib boolSyntax testutils

val checks = ref 0
fun check name ok =
  (checks := !checks + 1; tprint name;
   if ok then OK () else die name)
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected)
fun terms xs ys = ListPair.allEq (fn (x,y) => aconv x y) (xs,ys)
fun proofs xs ys = ListPair.allEq (fn (x,y) => same x y) (xs,ys)
fun fails name predicate f =
  check name (case Exn.capture f () of
                  Exn.Exn e =>
                    predicate e orelse
                    (print (Feedback.exn_to_string e ^ "\n"); false)
                | Exn.Res _ => false)
fun hol e = case e of HOL_ERR _ => true | _ => false
fun stage s = check_HOL_ERRexn
  (fn (origin,func,_) => origin = "Cond_rewr" andalso func = s)
val application = stage "COND_REWR_CONV (application)"
val construction = stage "COND_REWR_CONV (construction) "
(* Prepared bounds are checked outside the conditional engine. Compare the
   complete diagnostic with liteLib's baseline, not an application wrapper. *)
val bound_error =
  case Exn.capture liteLib.failwith "exceeded rewrite bound" of
      Exn.Exn (HOL_ERR err) => err
    | _ => raise Fail "liteLib.failwith did not raise HOL_ERR"
val _ = check "baseline bound error has exact failwith provenance"
  (Feedback.message_of bound_error = "exceeded rewrite bound" andalso
   Feedback.origins_of bound_error =
     [{origin_structure="??",origin_function="failwith",
       source_location=locn.Loc_Unknown}])
fun exhausted_bound (HOL_ERR err) =
      Feedback.message_of err = Feedback.message_of bound_error andalso
      Feedback.origins_of err = Feedback.origins_of bound_error
  | exhausted_bound _ = false
exception Callback of unit ref
val a = ``cond_ext_a:bool``
val p = ``cond_ext_p:bool``
val q = ``cond_ext_q:bool``
val h = ``cond_ext_h:bool``
val input = mk_conj (a,T)
val plain = CONJUNCT1 (CONJUNCT2 (SPEC a boolTheory.AND_CLAUSES))
val rule = DISCH p (ADD_ASSUM p (ADD_ASSUM h plain))
val two = DISCH p (DISCH q
  (ADD_ASSUM p (ADD_ASSUM q (ADD_ASSUM h plain))))
val expected = MP rule (ASSUME p)
val two_expected = MP (MP two (ASSUME p)) (ASSUME q)
fun solver _ tm = ASSUME tm
fun cfg solve stack depth ord : Cond_rewrExt.config =
  {solver=solve,stack=stack,cond_depth=depth,term_ord=ord}
fun default solve stack depth =
  cfg solve stack depth Cond_rewr.ac_term_ord
val paired : Cond_rewrExt.runners =
  Cond_rewrExt.COND_REWR_CONVS ("conditional",rule) false
val ordinary = Cond_rewr.COND_REWR_CONV ("conditional",rule) false
val legacy = #legacy paired solver []
val live = #configured paired (default solver [] NONE)
val fixed = #configured paired (default solver [] (SOME 1))
val zero = #configured paired (default solver [] (SOME 0))

(* Closures are saved before the live reference changes. NONE is not a
   construction-time snapshot; SOME and the integer adapter are fixed. *)
val _ = Lib.with_flag (Cond_rewr.stack_limit,0) (fn () =>
  (fails "ordinary saved conversion sees live zero" application
     (fn () => ordinary solver [] input);
   fails "paired legacy sees shared live zero" application
     (fn () => legacy input);
   fails "configured NONE sees shared live zero" application
     (fn () => live input);
   check "configured SOME one ignores live zero" (same (fixed input) expected);
   Cond_rewr.stack_limit := 1;
   check "ordinary sees later depth change"
     (same (ordinary solver [] input) expected);
   check "paired legacy sees later depth change"
     (same (legacy input) expected);
   check "saved NONE sees later depth change" (same (live input) expected);
   fails "saved SOME zero ignores later live change" application
     (fn () => zero input))) ()
val _ = Lib.with_flag (Cond_rewr.stack_limit,0) (fn () =>
  (check "WITH_CONFIG adapter preserves explicit depth"
     (same (Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG
        ("conditional",rule) false (default solver [] (SOME 1)) input)
        expected);
   check "WITH_CONTEXT adapter forwards integer depth"
     (same (Cond_rewrExt.COND_REWR_CONV_WITH_CONTEXT
        ("conditional",rule) false
        {solver=solver,stack=[],cond_depth=1,
         term_ord=Cond_rewr.ac_term_ord} input) expected))) ()

(* Conditions prepend, in theorem order, to the caller's exact stack.
   Calls with a nonempty stack must not count as top-level rewrites. *)
val _ = let
  val seen = ref ([] : (term list * term) list)
  fun solve stack tm = (seen := !seen @ [(stack,tm)]; ASSUME tm)
  val pair = Cond_rewrExt.COND_REWR_CONVS ("two",two) false
  val cv = #configured pair (default solve [h] (SOME 3))
  val (th,fired) = Cond_rewr.with_tracking cv input
  val _ = check "multiple conditions preserve proof and hypotheses"
    (same th two_expected andalso null fired)
  val _ = check "solver receives all conditions then original stack"
    (ListPair.allEq (fn ((s,t),(es,et)) => terms s es andalso aconv t et)
      (!seen,[([p,q,h],p),([p,q,h],q)]))
  val _ = seen := []
  val _ = fails "depth counts existing stack plus every condition"
    application (fn () => #configured pair
      (default solve [h] (SOME 2)) input)
  val _ = fails "condition already on stack cuts loop" application
    (fn () => #legacy pair solve [q] input)
  val _ = check "depth and loop rejection run no solver" (null (!seen))
in () end

val _ = let
  val seen = ref ([] : term list)
  fun solve _ tm = (seen := tm :: !seen; ASSUME q)
  val pair = Cond_rewrExt.COND_REWR_CONVS ("bad proof",two) false
  val direct = Cond_rewr.COND_REWR_CONV ("bad proof",two) false
  fun check_both name conv =
    (seen := [];
     fails (name ^ ": wrong first proof fails") application
       (fn () => conv input);
     check (name ^ ": both solvers run before discharging")
       (terms (!seen) [q,p]))
in
  check_both "ordinary" (direct solve []);
  check_both "configured" (#configured pair (default solve [] (SOME 2)))
end

(* Matching substitutes conditions before invoking the solver, while
   retaining hypotheses that did not participate in the match. *)
val _ = let
  val condition = mk_neg a
  val conditional = DISCH condition
    (ADD_ASSUM condition (ADD_ASSUM h plain))
  val tm = mk_conj (q,T)
  val instantiated = INST [a |-> q] conditional
  val want = MP instantiated (ASSUME (mk_neg q))
  val seen = ref ([] : term list)
  fun solve stack t =
    (if terms stack [mk_neg q,h] then ()
     else raise Fail "instantiated condition stack changed";
     seen := t :: !seen; ASSUME t)
  val pair = Cond_rewrExt.COND_REWR_CONVS ("instantiate",conditional) false
  val _ = check "legacy matcher instantiates condition and theorem"
    (same (#legacy pair solve [h] tm) want)
  val _ = check "configured matcher instantiates condition and theorem"
    (same (#configured pair (default solve [h] NONE) tm) want)
  val _ = check "solver sees instantiated conditions in both runners"
    (terms (!seen) [mk_neg q,mk_neg q])
in () end

(* A miss, self-loop, failed condition and malformed theorem have distinct
   stages. The boolean entry points do not own or spend a bounded control. *)
val _ = List.app (fn (name,make) =>
  (fails (name ^ ": malformed theorem fails during construction")
     construction (fn () => make ("bad",TRUTH) false);
   fails (name ^ ": leading forall fails during construction")
     construction (fn () => make ("bad",GEN a plain) false);
   fails (name ^ ": negated equality fails during construction")
     construction (fn () => make ("bad",ASSUME (mk_neg (concl plain))) false);
   fails (name ^ ": mismatch fails at application") application
     (fn () => #legacy (make ("plain",plain) false) solver [] T);
   fails (name ^ ": reflexive rewrite is rejected") application
     (fn () => #configured (make ("self",REFL input) true)
       (default solver [] NONE) input)))
  [("paired",Cond_rewrExt.COND_REWR_CONVS),
   ("ordinary",fn nmth => fn bounded =>
      {legacy=Cond_rewr.COND_REWR_CONV nmth bounded,
       configured=fn {solver,stack,cond_depth,term_ord} =>
         Cond_rewr.COND_REWR_CONV nmth bounded solver stack})]
val _ = fails "WITH_CONFIG malformed theorem fails before configuration"
  construction (fn () =>
    Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG ("bad",TRUTH) false)
val _ = fails "WITH_CONTEXT malformed theorem fails before context"
  construction (fn () =>
    Cond_rewrExt.COND_REWR_CONV_WITH_CONTEXT ("bad",TRUTH) false)
val _ = fails "prepare malformed theorem fails before projection"
  construction (fn () =>
    Cond_rewrExt.prepare ("bad",TRUTH) BoundedRewrites.UNBOUNDED)
val _ = let
  val equation = ``(\x:bool. x /\ T) = (\x. x)``
  val th = ASSUME equation
  val tm = ``\renamed:bool. renamed /\ T``
  val result = Cond_rewrExt.COND_REWR_CONV_WITH_CONFIG ("alpha",th) false
    (default solver [] NONE) tm
  val direct = Cond_rewr.COND_REWR_CONV ("alpha",th) false solver [] tm
in check "alpha-renamed input preserves conclusion and source hypotheses"
     (same result direct andalso aconv (lhs (concl result)) tm andalso
      HOLset.equal (hypset result,hypset th))
end

(* AC orientation is the original ordering unless explicitly configured.
   The public alias must classify the very same permutations. *)
val _ = let
  val perm = SPEC_ALL boolTheory.CONJ_COMM
  val pair = Cond_rewrExt.COND_REWR_CONVS ("commute",perm) false
  val xy = mk_conj (a,p)
  val yx = mk_conj (p,a)
  val down = if Cond_rewr.ac_term_ord (xy,yx) = GREATER then xy else yx
  val up = if aconv down xy then yx else xy
  val want = REWR_CONV perm down
  val _ = check "Cond_rewrExt.is_var_perm classifies permutations"
    (List.map Cond_rewrExt.is_var_perm
      [(xy,yx),(input,a),(a,a),(a,p),
       (``cond_ext_t:bool``,``cond_ext_t:bool -> bool``),
       (``(cond_ext_f:bool -> bool) cond_ext_t``,
        ``(cond_ext_f:bool -> bool) cond_ext_t``)] =
     [true,false,true,false,false,true])
  (* Cond_rewr.COND_REWR_CONV and the legacy runner of
     Cond_rewrExt.COND_REWR_CONVS must accept and refuse the same
     permutative rewrites, whichever way the term ordering points. *)
  val x = ``cond_ext_x:bool``
  val y = ``cond_ext_y:bool``
  val z = ``cond_ext_z:bool``
  fun mk l r = mk_thm ([], mk_eq (l,r))
  (* Each equation with terms to rewrite and the expected result: a
     permutation rewrites only downward in the term ordering, an equation
     whose sides are equal never. *)
  fun cx (l,r) = mk_conj (l,r)
  fun dx (l,r) = mk_disj (l,r)
  val eqns =
    [("perm",mk (cx (x,y)) (cx (y,x)),
      [(cx (x,y),NONE), (cx (y,x),SOME (cx (x,y)))]),
     ("nested perm",mk (cx (x,dx (y,z))) (cx (z,dx (x,y))),
      [(cx (x,dx (y,z)),NONE), (cx (y,dx (x,z)),NONE),
       (cx (z,dx (x,y)),SOME (cx (y,dx (z,x))))]),
     ("fewer variables",mk (cx (x,y)) (cx (x,x)),
      [(cx (x,y),SOME (cx (x,x))), (cx (y,x),SOME (cx (y,y)))]),
     ("other shape",mk (cx (x,y)) (dx (y,x)),
      [(cx (x,y),SOME (dx (y,x))), (cx (y,x),SOME (dx (x,y)))]),
     ("same shape",mk (cx (x,y)) (cx (x,y)),
      [(cx (x,y),NONE), (cx (y,x),NONE)])]
  fun outcome f = case Exn.capture f () of
                      Exn.Res th => SOME th
                    | Exn.Exn _ => NONE
  (* All three runners rewrite tm to want, or all refuse it *)
  fun rewrites th (tm,want) =
    let val ord = outcome (fn () =>
          Cond_rewr.COND_REWR_CONV ("agree",th) false solver [] tm)
        val ext = outcome (fn () =>
          #legacy (Cond_rewrExt.COND_REWR_CONVS ("agree",th) false)
            solver [] tm)
        val cfg = outcome (fn () =>
          #configured (Cond_rewrExt.COND_REWR_CONVS ("agree",th) false)
            (default solver [] NONE) tm)
        fun as_wanted res =
          case (res,want) of
              (NONE,NONE) => true
            | (SOME th',SOME r) => aconv (concl th') (mk_eq (tm,r))
            | _ => false
    in List.all as_wanted [ord,ext,cfg] end
  val _ = check "engines rewrite each permutative fixture as expected"
    (List.all (fn (_,th,cases) => List.all (rewrites th) cases) eqns)
  val _ = check "AC legacy proof agrees with direct ordinary constructor"
    (same (#legacy pair solver [] down) want andalso
     same (Cond_rewr.COND_REWR_CONV ("commute",perm) false
       solver [] down) want)
  val _ = fails "legacy refuses upward AC orientation" application
    (fn () => #legacy pair solver [] up)
  val calls = ref ([] : (term * term) list)
  fun order result ts = (calls := ts :: !calls; result)
  val _ = List.app (fn ord =>
    fails "configured non-GREATER order refuses permutation" application
      (fn () => #configured pair (cfg solver [] NONE (order ord)) down))
    [LESS,EQUAL]
  val _ = check "custom GREATER admits normally upward permutation"
    (same (#configured pair (cfg solver [] NONE (order GREATER)) up)
      (REWR_CONV perm up))
  val _ = check "custom order receives instantiated equation sides"
    (ListPair.allEq (fn ((l,r),(x,y)) => aconv l x andalso aconv r y)
      (rev (!calls),[(down,up),(down,up),(up,down)]))
  val bounded = Cond_rewrExt.COND_REWR_CONVS ("commute",perm) true
  val _ = check "bounded boolean bypasses AC rejection in both runners"
    (same (#legacy bounded solver [] up) (REWR_CONV perm up) andalso
     same (#configured bounded (cfg solver [] NONE (fn _ => LESS)) up)
       (REWR_CONV perm up))
  val remaining = ref 2
  val prepared = Cond_rewrExt.runners (Cond_rewrExt.prepare
    ("bounded commute",perm) (BoundedRewrites.BOUNDED remaining))
  val _ = check "prepared bounded AC legacy spends supplied reference"
    (same (#legacy prepared solver [] up) (REWR_CONV perm up) andalso
     !remaining = 1)
  val _ = check "prepared bounded AC configured bypasses custom rejection"
    (same (#configured prepared (cfg solver [] NONE (fn _ => LESS)) up)
       (REWR_CONV perm up) andalso !remaining = 0)
  val _ = fails "prepared bounded AC refuses after alternating exhaustion"
    exhausted_bound (fn () => #legacy prepared solver [] down)
  val comparisons_at_zero = ref 0
  val _ = fails "zero bound is checked before custom order callback"
    exhausted_bound (fn () => #configured prepared
      (cfg solver [] NONE (fn _ =>
        (comparisons_at_zero := !comparisons_at_zero + 1;
         raise Fail "order must not run"))) up)
  val _ = check "exhausted AC rule invokes no custom order"
    (!comparisons_at_zero = 0 andalso !remaining = 0)
  val unbounded = Cond_rewrExt.runners (Cond_rewrExt.prepare
    ("unbounded commute",perm) BoundedRewrites.UNBOUNDED)
  val _ = fails "prepared unbounded AC still checks orientation"
    application (fn () => #legacy unbounded solver [] up)
in () end

(* Projection must be inert and retain the supplied reference, including
   a projection first extracted after partial consumption or exhaustion. *)
val _ = let
  val remaining = ref 3
  val solves = ref 0
  fun solve stack tm = (solves := !solves + 1; solver stack tm)
  val prepared : Cond_rewrExt.prepared = Cond_rewrExt.prepare
    ("shared",rule) (BoundedRewrites.BOUNDED remaining)
  val first = Cond_rewrExt.runners prepared
  val _ = check "prepare and projection are inert"
    (!remaining = 3 andalso !solves = 0)
  val _ = check "legacy spends exactly one successful use"
    (same (#legacy first solve [] input) expected andalso !remaining = 2)
  val late = Cond_rewrExt.runners prepared
  val _ = check "late projection does not reset partially used reference"
    (!remaining = 2 andalso !solves = 1)
  val _ = check "late configured runner spends original reference"
    (same (#configured late (default solve [] NONE) input) expected andalso
     !remaining = 1)
  val _ = check "alternating back to original configured runner shares bound"
    (same (#configured first (default solve [] NONE) input) expected andalso
     !remaining = 0 andalso !solves = 3)
  val exhausted = Cond_rewrExt.runners prepared
  val _ = List.app (fn (label,cv) =>
    fails ("exhausted " ^ label ^ " refuses application") exhausted_bound
      (fn () => cv input))
    [("original legacy",#legacy first solve []),
     ("late legacy",#legacy late solve []),
     ("new configured",#configured exhausted (default solve [] NONE))]
  val _ = check "exhausted applications neither solve nor decrement"
    (!remaining = 0 andalso !solves = 3)
  val _ = remaining := 1
  val _ = check "external refill is visible to an already projected runner"
    (same (#legacy exhausted solve [] input) expected andalso !remaining = 0)
  val _ = remaining := 0
  val _ = fails "zero bound is checked before trying a mismatching term"
    exhausted_bound (fn () => #legacy exhausted solve [] T)
  val _ = check "zero-bound miss cannot spend or invoke solver"
    (!remaining = 0 andalso !solves = 4)
  val unbounded = Cond_rewrExt.runners (Cond_rewrExt.prepare
    ("unbounded",rule) BoundedRewrites.UNBOUNDED)
  val _ = List.app (fn _ =>
    check "unbounded prepared runners may alternate repeatedly"
      (same (#legacy unbounded solve [] input) expected andalso
       same (#configured unbounded (default solve [] NONE) input) expected))
    [1,2,3]
in () end

(* Failures at every application gate must leave actual control untouched.
   In particular solving is not a reservation of a use. *)
val _ = let
  val remaining = ref 2
  val pair = Cond_rewrExt.runners (Cond_rewrExt.prepare
    ("failures",rule) (BoundedRewrites.BOUNDED remaining))
  fun reject _ _ = raise mk_HOL_ERR "CondExtTest" "solver" "unsolved"
  val _ = fails "failed solver is an application HOL_ERR" application
    (fn () => #legacy pair reject [] input)
  val _ = check "failed legacy solver leaves supplied counter unchanged"
    (!remaining = 2)
  val _ = fails "failed configured solver is an application HOL_ERR"
    application (fn () => #configured pair (default reject [] NONE) input)
  val _ = fails "wrong solver proof fails without spending" application
    (fn () => #legacy pair (fn _ => fn _ => TRUTH) [] input)
  val _ = fails "prepared miss fails without spending" application
    (fn () => #legacy pair solver [] T)
  val _ = fails "prepared loop cut fails without spending" application
    (fn () => #legacy pair solver [p] input)
  val _ = fails "prepared depth cut fails without spending" application
    (fn () => #configured pair (default solver [] (SOME 0)) input)
  val _ = check "all unsuccessful gates leave original bound unchanged"
    (!remaining = 2)
  val _ = check "success after failures spends once and preserves proof"
    (same (#configured pair (default solver [] NONE) input) expected andalso
     !remaining = 1)
  val reflexive = Cond_rewrExt.runners (Cond_rewrExt.prepare
    ("self",REFL input) (BoundedRewrites.BOUNDED remaining))
  val _ = fails "prepared self-loop does not spend" application
    (fn () => #legacy reflexive solver [] input)
  val _ = check "self-loop leaves actual control unchanged" (!remaining = 1)
in () end

(* The listener/action constructors are Trace's original identities, not
   lookalikes in the extension. Compare complete ordinary event streams. *)
fun same_action (Trace.TEXT x,Trace.TEXT y) = x = y
  | same_action (Trace.REWRITING (n,t,th),Trace.REWRITING (m,u,uh)) =
      n = m andalso aconv t u andalso same th uh
  | same_action (Trace.SIDECOND_ATTEMPT t,Trace.SIDECOND_ATTEMPT u) = aconv t u
  | same_action (Trace.SIDECOND_SOLVED th,Trace.SIDECOND_SOLVED uh) =
      same th uh
  | same_action (Trace.SIDECOND_NOT_SOLVED t,Trace.SIDECOND_NOT_SOLVED u) =
      aconv t u
  | same_action (Trace.PRODUCE (t,n,th),Trace.PRODUCE (u,m,uh)) =
      n = m andalso aconv t u andalso same th uh
  | same_action (Trace.IGNORE (s,th),Trace.IGNORE (t,uh)) =
      s = t andalso same th uh
  | same_action _ = false
fun events f = let
  val seen = ref ([] : (int * Trace.action) list)
  val key = "Cond_rewrExt focused test"
  val _ = Listener.add_listener Trace.trace_hook
    (key,fn event => seen := event :: !seen)
  val result = Portable.finally
    (fn () => ignore (Listener.remove_listener Trace.trace_hook key))
    (fn () => Exn.capture f ()) ()
in (result,rev (!seen)) end
fun same_events xs ys = ListPair.allEq
  (fn ((n,a),(m,b)) => n = m andalso same_action (a,b)) (xs,ys)
val _ = let
  fun reject _ _ = raise mk_HOL_ERR "CondExtTest" "solver" "unsolved"
  val cases = [("success",solver,[],input),
               ("unsolved",reject,[],input),
               ("loop",solver,[p],input),
               ("miss",solver,[],T)]
  fun compare (label,solve,stack,tm) = let
    val (_,baseline) = events (fn () => ordinary solve stack tm)
    val (_,old) = events (fn () => #legacy paired solve stack tm)
    val (_,configured) = events (fn () => #configured paired
      (default solve stack NONE) tm)
  in check ("shared Trace exact ordinary stream: " ^ label)
       (same_events baseline old andalso same_events baseline configured)
  end
  val _ = List.app compare cases
  val (_,success) = events (fn () => live input)
  val _ = check "conditional trace order, levels, names and proofs"
    (same_events success
      [(1,Trace.REWRITING ("conditional",input,rule)),
       (2,Trace.SIDECOND_ATTEMPT p),
       (2,Trace.SIDECOND_SOLVED (ASSUME p)),
       (2,Trace.PRODUCE (input,"conditional",expected))])
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0) (fn () =>
    compare ("depth",solver,[],input)) ()
  val perm = SPEC_ALL boolTheory.CONJ_COMM
  val pair = Cond_rewrExt.COND_REWR_CONVS ("perm trace",perm) false
  val xy = mk_conj (a,p)
  val yx = mk_conj (p,a)
  val up = if Cond_rewr.ac_term_ord (xy,yx) = GREATER then yx else xy
  val (_,baseline) = events (fn () => Cond_rewr.COND_REWR_CONV
    ("perm trace",perm) false solver [] up)
  val (_,extended) = events (fn () => #configured pair
    (default solver [] NONE) up)
  val _ = check "shared Trace AC rejection stream"
    (not (null baseline) andalso same_events baseline extended)
in () end

(* Only one tracking cell: both directions, nested extents, exceptional
   restoration, non-root suppression and failures without phantom entries. *)
val _ = let
  val direct_plain = Cond_rewr.COND_REWR_CONV ("plain",plain) false solver []
  val ext_plain = #legacy
    (Cond_rewrExt.COND_REWR_CONVS ("plain",plain) false) solver []
  val ((th1,th2),fired) = Cond_rewr.with_tracking
    (fn () => (direct_plain input,live input)) ()
  val _ = check "ordinary tracking collects ordinary and configured rewrites"
    (same th1 plain andalso same th2 expected andalso
     proofs fired [plain,rule])
  val inner_seen = ref ([] : thm list)
  val (_,outer) = Cond_rewr.with_tracking (fn () =>
    (ignore (legacy input);
     inner_seen := #2 (Cond_rewr.with_tracking
       (fn () => (ignore (ext_plain input); direct_plain input)) ());
     ignore (live input))) ()
  val _ = check "nested tracking shares cell but isolates inner extent"
    (proofs outer [rule,rule] andalso proofs (!inner_seen) [plain,plain])
  val token = ref ()
  val (_,after_exception) = Cond_rewr.with_tracking (fn () =>
    (ignore (direct_plain input);
     fails "tracking rethrows original callback payload"
       (fn Callback r => Portable.pointer_eq (r,token) | _ => false)
       (fn () => Cond_rewr.with_tracking
         (fn () => (ignore (legacy input); raise Callback token)) ());
     ignore (ext_plain input))) ()
  val _ = check "exceptional inner extent restores ordinary tracking cell"
    (proofs after_exception [plain,plain])
  val (_,empty) = Cond_rewr.with_tracking (fn () =>
    (ignore (#legacy paired solver [h] input);
     fails "tracked failure remains application error" application
       (fn () => #legacy paired solver [p] input))) ()
  val _ = check "nested candidates and failures create no tracking entries"
    (null empty)
  val (_,fresh) = Cond_rewr.with_tracking (fn () => ()) ()
  val _ = check "tracking leaves no stale entries after either extent"
    (null fresh)
in () end

(* Both engines use the baseline STRUCT_WRAP contract: foreign callback
   exceptions become HOL_ERR with General.exnMessage, HOL_ERR gains an
   application origin, and Interrupt itself escapes unchanged. Exceptions
   raised outside the engine by a tracking extent are tested separately. *)
val _ = let
  val exceptions =
    [("private",Callback (ref ())),
     ("Fail",Fail "callback payload"),
     ("HOL_ERR",mk_HOL_ERR "CondExtTest" "callback" "callback diagnostic"),
     ("Interrupt",Portable.Interrupt)]
  fun same_error (HOL_ERR expected) (HOL_ERR actual) =
        Feedback.message_of actual = Feedback.message_of expected andalso
        Feedback.origins_of actual = Feedback.origins_of expected
    | same_error Portable.Interrupt Portable.Interrupt = true
    | same_error _ _ = false
  fun wrapped error =
    Feedback.wrap_exn "Cond_rewr" "COND_REWR_CONV (application)" error
    handle Portable.Interrupt => Portable.Interrupt
  fun exercise (label,error) = let
    val remaining = ref 1
    val pair = Cond_rewrExt.runners (Cond_rewrExt.prepare
      ("callback",rule) (BoundedRewrites.BOUNDED remaining))
    fun stop _ _ = raise error
    val baseline =
      case Exn.capture (fn () => ordinary stop [] input) () of
          Exn.Exn e => e
        | Exn.Res _ => raise Fail "ordinary callback did not raise"
    val _ = check (label ^ " ordinary solver obeys STRUCT_WRAP contract")
      (same_error (wrapped error) baseline)
    val _ = fails (label ^ " legacy solver matches exact ordinary exception")
      (same_error baseline) (fn () => #legacy pair stop [] input)
    val _ = fails
      (label ^ " configured solver matches exact ordinary exception")
      (same_error baseline)
      (fn () => #configured pair (default stop [] NONE) input)
    val _ = check (label ^ " solver exception does not spend") (!remaining = 1)
    val perm = Cond_rewrExt.COND_REWR_CONVS
      ("order callback",SPEC_ALL boolTheory.CONJ_COMM) false
    (* Ordinary construction has no arbitrary order callback. Its wrapper,
       not an invented ordinary callback path, supplies the expected error. *)
    val _ = fails (label ^ " term-order callback matches exact wrapper")
      (same_error (wrapped error))
      (fn () => #configured perm
        (cfg solver [] NONE (fn _ => raise error)) (mk_conj (a,p)))
  in () end
  val _ = List.app exercise exceptions
in () end

val _ = print ("Cond_rewrExt focused checks: " ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
