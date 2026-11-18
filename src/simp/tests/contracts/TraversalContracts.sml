(* Legacy APIs only: shared by normal selftest and the paired runner.
   Record every Trace action and forward every warning; do not normalize
   callback counts, warning text, or exception diagnostics. *)
structure TraversalContracts =
struct
open HolKernel Parse boolLib simpLib testutils

fun observe label value =
  print ("OBS " ^ label ^ "=" ^ String.toString value ^ "\n")
fun check label b =
  (tprint label; if b then OK () else die ("contract: " ^ label))
fun terms ts = String.concatWith ";" (map term_to_string ts)
fun theorem th = term_to_string (concl th) ^ " [" ^ terms (hyp th) ^ "]"
fun same th expected =
  aconv (concl th) (concl expected) andalso
  HOLset.equal (hypset th,hypset expected) andalso
  HOLset.equal (FVL (thm_frees th) empty_tmset,
                FVL (thm_frees expected) empty_tmset)
fun total cv = QCONV (TRY_CONV cv)

fun action a =
  case a of
      Trace.LZ_TEXT f => "LZ_TEXT:" ^ f ()
    | Trace.TEXT s => "TEXT:" ^ s
    | Trace.REDUCE (s,t) => "REDUCE:" ^ s ^ ":" ^ term_to_string t
    | Trace.REWRITING (s,t,th) =>
        "REWRITING:" ^ s ^ ":" ^ term_to_string t ^ ":" ^ theorem th
    | Trace.SIDECOND_ATTEMPT t => "ATTEMPT:" ^ term_to_string t
    | Trace.SIDECOND_SOLVED th => "SOLVED:" ^ theorem th
    | Trace.SIDECOND_NOT_SOLVED t => "NOT_SOLVED:" ^ term_to_string t
    | Trace.OPENING (t,th) =>
        "OPENING:" ^ term_to_string t ^ ":" ^ theorem th
    | Trace.PRODUCE (t,s,th) =>
        "PRODUCE:" ^ term_to_string t ^ ":" ^ s ^ ":" ^ theorem th
    | Trace.IGNORE (s,th) => "IGNORE:" ^ s ^ ":" ^ theorem th
    | Trace.MORE_CONTEXT th => "MORE_CONTEXT:" ^ theorem th

fun exception_text e =
  case e of
      Portable.Interrupt => "Interrupt"
    | HOL_ERR err =>
        "HOL_ERR:" ^ Feedback.top_structure_of err ^ ":" ^
        Feedback.top_function_of err ^ ":" ^ Feedback.message_of err ^
        ":" ^ Feedback.exn_to_string e
    | _ => General.exnName e ^ ":" ^ Feedback.exn_to_string e
fun expect_exception record label predicate f =
  let val result = (Exn.Res (f ()) handle e => Exn.Exn e)
  in
    case result of
        Exn.Res _ =>
          (record (label ^ ":returned"); check (label ^ " must raise") false)
      | Exn.Exn e =>
          (record (label ^ ":exception:" ^ exception_text e);
           observe (label ^ ".exception") (exception_text e);
           check label (predicate e))
  end

(* A single ordered stream includes stage boundaries, callbacks, traces
   and warnings, so a warning cannot move across a callback unnoticed. *)
fun scenario name test = let
  val events = ref ([] : string list)
  fun record s = events := s :: !events
  val sink = !Feedback.WARNING_outstream
  val listener = "compatibility traversal contracts"
  fun watch (n,a) = record ("trace" ^ Int.toString n ^ ":" ^ action a)
  fun finish () =
    (Feedback.WARNING_outstream := sink;
     ignore (Listener.remove_listener Trace.trace_hook listener))
  val _ = Listener.add_listener Trace.trace_hook (listener,watch)
  val _ = Feedback.WARNING_outstream :=
    (fn s => (record ("warning:" ^ s); sink s))
  val result = (Exn.Res (test record) handle e => Exn.Exn e)
  val _ = finish ()
  val _ = List.app (observe name) (rev (!events))
in Exn.release result end

exception Context of int
exception Stop of unit ref

fun lifetime record = let
  val atom = ``lifetime_atom:bool``
  val fact = ASSUME ``lifetime_fact:bool``
  fun fixture () = let
    val count = ref 0
    val reducer = Traverse.REDUCER
      {name=SOME "lifetime collector",initial=Context 0,
       addcontext=fn (Context n,ths) =>
         (count := !count + 1;
          record ("collect:" ^ Int.toString n ^ ":" ^
                  terms (map concl ths)); Context (n+1))
       | _ => raise Fail "wrong private context",
       apply=fn {context,...} => fn tm =>
         case context of
             Context n =>
               (record ("apply-context:" ^ Int.toString n ^ ":" ^
                        term_to_string tm); NO_CONV tm)
           | _ => raise Fail "lost private context"}
    val ss = pureSimps.pure_ss ++ dproc_ss reducer
  in (ss,count) end
  val builders =
    [("raw",fn ss => Traverse.TRAVERSE (traversedata_for_ss ss)),
     ("cong-qconv",congLib.CONGRUENCE_SIMP_QCONV boolSyntax.equality
                     (congLib.mk_congset [])),
     ("simp-total",SIMP_CONV),
     ("cong-total",congLib.CONGRUENCE_SIMP_CONV boolSyntax.equality
                     (congLib.mk_congset []))]
  fun run (name,build) = let
    val (ss,count) = fixture ()
    val prior_count = !count
    val _ = record (name ^ ":construct")
    val cv = build ss [fact]
    val constructed = !count - prior_count
    val _ = record (name ^ ":first")
    val th1 = total cv atom
    val first = !count - prior_count
    val _ = record (name ^ ":second")
    val th2 = total cv atom
    val second = !count - prior_count
    val expected = if String.isSuffix "total" name then [0,1,2]
                   else [1,1,1]
  in
    record (name ^ ":counts:" ^ String.concatWith ","
      (map Int.toString [constructed,first,second]));
    check (name ^ " collector lifetime")
      ([constructed,first,second] = expected andalso
       same th1 (REFL atom) andalso same th2 (REFL atom))
  end
in List.app run builders end

fun collectors record = let
  val root = ``lifetime_collect_root:bool``
  val child = ``lifetime_collect_child:bool``
  val facts = map ASSUME [``lifetime_fact1:bool``,``lifetime_fact2:bool``]
  val nested = [ASSUME ``lifetime_nested_fact:bool``]
  val calls = ref ([] : string list)
  fun reducer tag = Traverse.REDUCER
    {name=SOME tag,initial=Context 0,
     addcontext=fn (context,ths) =>
       case context of
           Context n => let
             val event = tag ^ ":" ^ Int.toString n ^ ":" ^
                         terms (map concl ths)
           in calls := event :: !calls; record event; Context (n+1) end
         | _ => raise Fail "collector context identity",
     apply=fn _ => NO_CONV}
  val descend : Opening.congproc = fn _ => fn {depther,...} => fn tm =>
    if aconv tm root then
      (ignore (total (depther (nested,boolSyntax.equality)) child);
       NO_CONV tm)
    else NO_CONV tm
  val data : Traverse.traverse_data =
    {rewriters=map reducer ["R1","R2"],dprocs=map reducer ["D1","D2"],
     limit=NONE,relation=boolSyntax.equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[descend],
        weakenprocs=[]}}
  fun expected n ths = map
    (fn tag => tag ^ ":" ^ Int.toString n ^ ":" ^ terms (map concl ths))
    ["R1","R2","D1","D2"]
  val _ = record "construct-collectors"
  val cv = total (Traverse.TRAVERSE data facts)
  val initial = expected 0 facts
  val recursive = expected 1 nested
  val _ = check "initial collector order and fact order"
    (rev (!calls) = initial)
  val _ = record "collectors-first-application"
  val th1 = cv root
  val _ = check "recursive collector order and private context"
    (rev (!calls) = initial @ recursive andalso same th1 (REFL root))
  val _ = record "collectors-second-application"
  val th2 = cv root
  val _ = check "recursive collection does not mutate reusable context"
    (rev (!calls) = initial @ recursive @ recursive andalso
     same th2 (REFL root))
  val _ = record "construct-empty-context"
  val empty = total (Traverse.TRAVERSE data [])
  val _ = empty child
in
  check "empty initial facts do not invoke collectors"
    (rev (!calls) = initial @ recursive @ recursive)
end

fun quotas record = let
  val a = ``lifetime_quota_a:bool``
  val b = ``lifetime_quota_b:bool``
  val equation = ASSUME (mk_eq (a,b))
  val ss = empty_ss ++ rewrites [Ntimes equation 2]
  val _ = record "extract-first"
  val first = total (Traverse.TRAVERSE (traversedata_for_ss ss) [])
  val th1 = first a
  val _ = record "extract-partially-spent"
  val second = total (Traverse.TRAVERSE (traversedata_for_ss ss) [])
  val th2 = second a
  val _ = record "extract-exhausted"
  val third = total (Traverse.TRAVERSE (traversedata_for_ss ss) [])
  val ths = [first a,second a,third a]
  val _ = List.app (record o theorem) (th1 :: th2 :: ths)
in
  check "legacy repeated extraction shares installed quota"
    (same th1 equation andalso same th2 equation andalso
     List.all (fn th => same th (REFL a)) ths)
end

fun factories record = let
  val a = ``lifetime_factory_a:bool``
  val b = ``lifetime_factory_b:bool``
  val c = ``lifetime_factory_c:bool``
  val ab = ASSUME (mk_eq (a,b))
  val bc = ASSUME (mk_eq (b,c))
  fun label tm = if aconv tm a then "a" else if aconv tm b then "b"
                 else if aconv tm c then "c" else "other"
  fun run low abort = let
    val callbacks = ref ([] : string list)
    fun event s = (callbacks := s :: !callbacks; record s)
    val token = ref ()
    val reducer = Traverse.REDUCER
      {name=NONE,initial=Context 0,
       addcontext=fn (ctxt,ths) => (event "collect"; ctxt),
       apply=fn _ => fn tm =>
         (event ("R:" ^ label tm);
          if abort then raise Stop token
          else if aconv tm a then ab
          else if low andalso aconv tm b then bc else NO_CONV tm)}
    fun factory tag : Opening.congproc = fn _ =>
      (event ("relation-" ^ tag);
       fn _ => (event ("factory-" ^ tag);
         fn tm => (event (tag ^ ":" ^ label tm); NO_CONV tm)))
    val data : Traverse.traverse_data =
      {rewriters=if low then [] else [reducer],
       dprocs=if low then [reducer] else [],limit=NONE,
       relation=boolSyntax.equality,
       travrules=Travrules.TRAVRULES
         {relations=[Travrules.EQ_preorder],congprocs=[factory "C"],
          weakenprocs=[factory "W"]}}
    val _ = event "construct"
    val cv = Traverse.TRAVERSE data [TRUTH]
    val _ = check "collect once; no eager congruence factories"
      (rev (!callbacks) = ["construct","collect"])
    val prefix = ["relation-C","relation-W","factory-C","factory-W"]
    val schedule = prefix @
      (if abort then ["R:a"]
       else if low then ["C:a","R:a","C:b","R:b","C:c","R:c","W:c"]
       else ["R:a","R:b","C:b","W:b"])
    fun apply () =
      if abort then expect_exception record "factory/root abort payload"
        (fn Stop r => Portable.pointer_eq (r,token) | _ => false)
        (fn () => cv a)
      else check "factory traversal theorem"
        (same (cv a) (if low then TRANS ab bc else ab))
    val _ = callbacks := []
    val _ = apply ()
    val _ = check "exact factory and reducer schedule"
      (rev (!callbacks) = schedule)
    val _ = apply ()
  in check "factories refresh on reuse; collectors do not"
       (rev (!callbacks) = schedule @ schedule)
  end
  val _ = run false false
  val _ = run true false
  val _ = run false true
  (* A rejected factory must stay rejected after the root enables it. *)
  val ready = ref false
  val builds = ref 0
  val gated : Opening.congproc = fn _ => fn _ =>
    (builds := !builds + 1; record "gated-factory";
     if !ready then REWR_CONV bc
     else raise mk_HOL_ERR "TraversalContracts" "factory" "not ready")
  val reducer = Traverse.REDUCER
    {name=NONE,initial=Context 0,addcontext=fn (c,_) => c,
     apply=fn _ => fn tm =>
       if aconv tm a then (ready := true; ab) else NO_CONV tm}
  val cv = Traverse.TRAVERSE
    {rewriters=[reducer],dprocs=[],limit=NONE,
     relation=boolSyntax.equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[gated],
        weakenprocs=[]}} []
  val _ = check "factory rejection cached before root mutation"
    (same (cv a) ab andalso !builds = 1 andalso !ready)
  val token = ref ()
  val _ = record "construct-throwing-factory"
  fun throwing error : Opening.congproc = fn _ => fn _ =>
    (record "throwing-factory"; raise error)
  fun stop error = Traverse.TRAVERSE
    {rewriters=[reducer],dprocs=[],limit=NONE,
     relation=boolSyntax.equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[throwing error],
        weakenprocs=[]}} []
  val foreign = stop (Stop token)
  val interrupt = stop Portable.Interrupt
  val _ = record "apply-throwing-factory"
  (* Traverse's mapfilter rejects foreign factory exceptions as well as
     HOL_ERR, but never Interrupt. Term-application payloads above escape. *)
  val _ = check "foreign factory exception is rejected, not propagated"
    (same (foreign a) ab)
  val _ = record "foreign-factory:returned"
in
  expect_exception record "factory Interrupt"
    (fn Portable.Interrupt => true | _ => false)
    (fn () => interrupt a)
end

fun defaults record = let
  val target = ``lifetime_depth_target:bool``
  val condition = ``lifetime_depth_condition:bool``
  val rule = ASSUME (mk_imp (condition,mk_eq (target,T)))
  val attempts = ref 0
  fun mutate _ _ tm =
    (attempts := !attempts + 1; record "candidate:depth=4";
     Cond_rewr.stack_limit := 4; NO_CONV tm)
  val ss = pureSimps.pure_ss ++ SSFRAG
    {name=NONE,congs=[],ac=[],filter=NONE,dprocs=[],
     convs=[{name="lifetime depth mutator",trace=0,
             key=SOME ([target],target),conv=mutate}],
     rewrs=[(NONE,rule)]}
  val facts = [ASSUME (mk_eq (condition,T))]
  val raw = Traverse.TRAVERSE (traversedata_for_ss ss) facts
  val saved = !Cond_rewr.stack_limit
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0)
    (fn () => check "live stack limit between native candidates"
      (same (raw target) (MP rule (EQT_ELIM (hd facts))) andalso
       !attempts = 1)) ()
  val _ = check "live default restored" (!Cond_rewr.stack_limit = saved)
  val native = Traverse.TRAVERSE
    (traversedata_for_ss pureSimps.pure_ss) [rule,ASSUME condition]
  val _ = Lib.with_flag (Cond_rewr.stack_limit,0)
    (fn () => check "reusable legacy depth zero"
      (same (total native target) (REFL target))) ()
  val _ = Lib.with_flag (Cond_rewr.stack_limit,1)
    (fn () => check "reusable legacy reads depth at application"
      (same (native target) (UNDISCH rule))) ()
in record ("restored-depth:" ^ Int.toString (!Cond_rewr.stack_limit)) end

fun exceptions record = let
  val atom = ``lifetime_exception_atom:bool``
  val raw = Traverse.TRAVERSE (traversedata_for_ss boolSimps.bool_ss) []
  val _ = expect_exception record "raw unchanged"
    (fn HOL_ERR _ => true | _ => false) (fn () => raw atom)
  val _ = expect_exception record "public unchanged"
    (fn UNCHANGED => true | _ => false)
    (fn () => SIMP_CONV boolSimps.bool_ss [] atom)
  val token = ref ()
  val calls = ref 0
  val reducer = Traverse.REDUCER
    {name=NONE,initial=Context 0,addcontext=fn (c,_) => c,
     apply=fn _ => fn _ =>
       (calls := !calls + 1; record "foreign-reducer"; raise Stop token)}
  val ss = pureSimps.pure_ss ++ dproc_ss reducer
  val _ = record "construct-foreign"
  val cv = Traverse.TRAVERSE (traversedata_for_ss ss) []
  val _ = check "foreign exception delayed until application" (!calls = 0)
  val _ = expect_exception record "raw foreign payload"
    (fn Stop r => Portable.pointer_eq (r,token) | _ => false)
    (fn () => cv atom)
  val _ = expect_exception record "public foreign payload"
    (fn Stop r => Portable.pointer_eq (r,token) | _ => false)
    (fn () => SIMP_CONV ss [] atom)
  val _ = expect_exception record "cong total foreign payload"
    (fn Stop r => Portable.pointer_eq (r,token) | _ => false)
    (fn () => congLib.CONGRUENCE_SIMP_CONV boolSyntax.equality
      (congLib.mk_congset []) ss [] atom)
  val _ = check "foreign callback frequency" (!calls = 3)
  val rule = ASSUME
    ``lifetime_condition ==> ((lifetime_result:bool) = T)``
  val runner = Cond_rewr.COND_REWR_CONV ("lifetime solver",rule) false
  fun failed e = expect_exception record ("solver " ^ General.exnName e)
    (case e of Portable.Interrupt =>
         (fn Portable.Interrupt => true | _ => false)
     | _ => (fn HOL_ERR _ => true | _ => false))
    (fn () => runner (fn _ => fn _ => raise e) []
      ``lifetime_result:bool``)
in
  Lib.with_flag (Cond_rewr.stack_limit,1)
    (fn () => List.app failed
      [mk_HOL_ERR "lifetime solver" "callback" "failure",
       UNCHANGED,Stop token,Portable.Interrupt]) ()
end

fun makers record = let
  val rule = CONJUNCT1 (SPEC ``lifetime_maker_p:bool`` AND_CLAUSES)
  val calls = ref 0
  fun maker th = (calls := !calls + 1; record "maker"; [th])
  val ss = empty_ss ++ SSFRAG
    {name=NONE,congs=[],convs=[],rewrs=[],ac=[],dprocs=[],
     filter=SOME maker}
  val malformed = ADD_ASSUM
    (mk_comb (boolSyntax.bounded_tm,mk_var ("not_a_number",bool))) rule
  val _ = expect_exception record "malformed bound precedes maker"
    (fn Option => true | _ => false)
    (fn () => ss ++ rewrites [rule,malformed])
  val _ = check "no maker before malformed rejection" (!calls = 0)
  val _ = record "install-two"
  val installed = ss ++ rewrites [rule,rule]
  val _ = record "project-two"
  val _ = traversedata_for_ss installed
in check "all makers at installation only" (!calls = 2) end

fun warnings record = let
  val count = ref 0
  val reducer = Traverse.REDUCER
    {name=NONE,initial=Context 0,
     addcontext=fn (ctxt,_) =>
       (count := !count + 1;
        HOL_WARNING "TraversalContracts" "collector" "lifetime warning";
        record "warning-collector-return"; ctxt),
     apply=fn _ => NO_CONV}
  val ss = pureSimps.pure_ss ++ dproc_ss reducer
  val prior_count = !count
  val _ = record "warning-construct"
  val cv = Traverse.TRAVERSE (traversedata_for_ss ss) [TRUTH]
  val _ = record "warning-apply-twice"
  val a = ``lifetime_warning_atom:bool``
  val _ = total cv a
  val _ = total cv a
in check "warning collector runs once, not on reuse"
     (!count = prior_count+1)
end

fun run () =
  (check "warning capture preconditions"
     (!Feedback.emit_WARNING andalso not (!Feedback.WARNINGs_as_ERRs));
   List.app (fn (name,test) => scenario name test)
     [("lifetime",lifetime),("collector",collectors),("quota",quotas),
      ("factory",factories),
      ("default",defaults),("exception",exceptions),("maker",makers),
      ("warning",warnings)])
end
