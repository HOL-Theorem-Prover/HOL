open HolKernel Parse boolLib testutils markerLib

val _ = new_theory "scratch"

val _ = HOLFlags.set_bflag (Parse.avoid_unicode, true)

(* Every directive constructor must be recognised with the identity and
   payload its consumer needs, and nothing else may be. *)
val _ =
  let
    val th = ASSUME “p:bool”
    fun same th' =
        HOLset.equal(hypset th, hypset th') andalso concl th ~~ concl th'
    fun check (name, mk, ok) =
        (tprint ("dest_directive: " ^ name);
         case dest_directive (mk ()) of
             NONE => die "not recognised"
           | SOME d => if ok d then OK ()
                       else die "wrong identity or payload")
    fun rejects (name, mk) =
        (tprint ("dest_directive: " ^ name ^ " is not a directive");
         if isSome (dest_directive (mk ())) then die "recognised"
         else OK ())
  in
    List.app check [
      ("AC", fn () => AC th TRUTH,
       fn DAC (a, b) => same a andalso concl b ~~ T | _ => false),
      ("Cong", fn () => Cong th, fn DCong a => same a | _ => false),
      ("Split", fn () => Split th, fn DSplit a => same a | _ => false),
      ("Excl", fn () => Excl "nm", fn DExcl "nm" => true | _ => false),
      ("ExclSF", fn () => ExclSF "nm", fn DExclSF "nm" => true | _ => false),
      ("ExclX", fn () => ExclX "nm", fn DExclX "nm" => true | _ => false),
      ("FRAG", fn () => FRAG "nm", fn DFRAG "nm" => true | _ => false),
      ("Req0", fn () => mk_Req0 th, fn DReq0 a => same a | _ => false),
      ("ReqD", fn () => mk_ReqD th, fn DReqD a => same a | _ => false),
      ("Once", fn () => BoundedRewrites.Once th,
       fn DBounded (a, 1) => same a | _ => false),
      ("Ntimes 3", fn () => BoundedRewrites.Ntimes th 3,
       fn DBounded (a, 3) => same a | _ => false),
      ("NoAsms", fn () => NoAsms, fn DNoAsms => true | _ => false),
      ("IgnAsm", fn () => IgnAsm ‘x = _’,
       fn DIgnAsm s => String.isSuffix "x = _" s | _ => false),
      ("Abbr", fn () => Abbr`v`, fn DAbbr "v" => true | _ => false),
      ("L", fn () => L "lab", fn DLabel "lab" => true | _ => false),
      ("Req0 wraps Cong", fn () => mk_Req0 (Cong th),
       fn DReq0 a => (case dest_directive a of
                          SOME (DCong b) => same b
                        | _ => false)
        | _ => false)
    ];
    tprint "strip_wrappers: Req0 over ReqD over Once";
    if same (strip_wrappers (mk_Req0 (mk_ReqD (BoundedRewrites.Once th))))
    then OK () else die "payload not reached";
    List.app rejects [
      ("TRUTH", fn () => TRUTH),
      ("assumption", fn () => th),
      ("reflexive equation", fn () => REFL “x:'a”),
      ("equation", fn () => ASSUME “x:'a = y”),
      ("implication from a marker", fn () => ASSUME “marker$Req0 ==> p”)
    ]
  end

val _ =
  (tprint "Split parses as a variable";
   require_msg
     (check_result (fn t => is_var t andalso #1 (dest_var t) = "Split"))
     term_to_string I “Split”)

val _ =
  (tprint "ExcludeX parses as a variable without extension opt-in";
   require_msg
     (check_result (fn t => is_var t andalso #1 (dest_var t) = "ExcludeX"))
     term_to_string I “ExcludeX”)

val _ =
  (tprint "qualified ExcludeX remains available";
   require_msg
     (check_result (same_const
       (prim_mk_const {Thy="marker", Name="ExcludeX"})))
     term_to_string I “marker$ExcludeX”)

(* Named markers store literal variable names, not parsed names or string
   encodings. Check all byte values as well as likely exclusion spellings. *)
val _ =
  let
    val bytes = List.tabulate (256, Char.chr)
    val names = ["", "nm", "rule:foo", "solver:foo", "looper:foo",
                 "split:foo", "case:bool", "Thy$Name", "Thy.Name.2",
                 "rule:", " leading and trailing ", "quote\"\\slash",
                 "\n\t\000", "λ∀"] @
                [String.implode bytes] @ map String.str bytes
    fun check label p = (tprint label; if p then OK () else die "mismatch")
    fun legacy nm =
        destExcl (Excl nm) = SOME nm andalso
        destExclSF (ExclSF nm) = SOME nm andalso
        destFRAG (FRAG nm) = SOME nm andalso
        (case dest_directive (Excl nm) of
             SOME (DExcl s) => s = nm | _ => false) andalso
        (case dest_directive (ExclSF nm) of
             SOME (DExclSF s) => s = nm | _ => false) andalso
        (case dest_directive (FRAG nm) of
             SOME (DFRAG s) => s = nm | _ => false)
    fun extended nm =
        let val th = ExclX nm
        in
          null (hyp th) andalso destExclX th = SOME nm andalso
          is_directive th andalso
          (case dest_directive th of
               SOME (DExclX s) => s = nm | _ => false)
        end
    fun distinct nm =
        destExcl (ExclX nm) = NONE andalso
        destExclSF (ExclX nm) = NONE andalso
        destFRAG (ExclX nm) = NONE andalso
        destExclX (Excl nm) = NONE andalso
        destExclX (ExclSF nm) = NONE andalso
        destExclX (FRAG nm) = NONE
    val x = ExclX "rule:Thy$Name"
    fun same th = concl th ~~ concl x andalso null (hyp th)
    fun payload th = same (strip_wrappers th) andalso
                     destExclX th = SOME "rule:Thy$Name"
    val wrapped = [mk_Req0 x, mk_ReqD x, BoundedRewrites.Once x,
                   mk_Req0 (mk_ReqD (BoundedRewrites.Once x)),
                   BoundedRewrites.Ntimes (mk_ReqD (mk_Req0 x)) 3]
    val nonvar = EQT_ELIM (ISPEC T markerTheory.ExcludeX_def)
    val impostor = ASSUME
      (mk_comb (mk_var ("ExcludeX", alpha --> bool), mk_var ("nm", alpha)))
  in
    check "ExclX literal string round trips (including every byte)"
      (List.all extended names);
    check "legacy named markers still preserve every literal string"
      (List.all legacy names);
    check "ExclX and legacy named recognizers are disjoint"
      (List.all distinct names);
    check "ExclX uses its own theory constant"
      (same_const (rator (concl x))
                  (prim_mk_const {Thy="marker", Name="ExcludeX"}));
    check "ExclX rejects non-markers, non-variable args and variable heads"
      (List.all (fn th => destExclX th = NONE)
                [TRUTH, ASSUME T, nonvar, impostor] andalso
       not (is_directive nonvar) andalso not (is_directive impostor));
    check "ExclX requirement/bounded wrappers preserve payload and hyps"
      (List.all payload wrapped);
    check "ExclX Req0 takes precedence over ReqD and bounds"
      (case dest_directive (mk_Req0 (mk_ReqD (BoundedRewrites.Once x))) of
           SOME (DReq0 p) =>
           (case dest_directive p of
                SOME (DReqD q) =>
                (case dest_directive q of
                     SOME (DBounded (r, 1)) => same r | _ => false)
              | _ => false)
         | _ => false);
    check "ExclX bounds take precedence over the marker head"
      (case dest_directive (BoundedRewrites.Ntimes x 3) of
           SOME (DBounded (p, 3)) => same p | _ => false)
  end

val _ =
    let val th = ASSUME “p:bool”
    in
      tprint "Split marker round-trip";
      require_msg
        (check_result (fn th' => HOLset.equal (hypset th, hypset th') andalso
                                 concl th ~~ concl th'))
        thm_to_string
        (destSplit o Split)
        th
    end


fun testtac tac = #1 o runtac (VALID tac)
val goal_print = HOLPP.pp_to_string 75 goalStack.pp_goal

val _ =
  let
    val seen = ref ([] : string list)
    val first = Cong (REFL T)
    val last = Cong (REFL F)
    val goal = ([], concl first)
    val pattern = “marker$Cong (p:bool)”
    val printer_name = "marker-selftest.RequirementOrder"
    fun print _ _ _ (ppfns : term_pp_types.ppstream_funs) _ _ tm =
      let val name = if lhs (rand tm) ~~ T then "first" else "last"
      in seen := name :: !seen; #add_string ppfns name end
    fun callback ths =
      (if List.all (null o hyp) ths then seen := "callback" :: !seen
       else die "requirement hypotheses reached the tactic";
       ALL_TAC)
    fun run () = testtac (process_taclist_then
        {arg=[mk_Req0 first, mk_Req0 last]} callback) goal
    val _ = tprint "process_taclist_then constructs each requirement in order"
    val _ = Parse.temp_add_user_printer (printer_name, pattern, print)
    val result = Exn.capture run ()
    val _ = Parse.temp_remove_user_printer (printer_name, pattern)
  in
    if boolSyntax.goals_eq (Exn.release result) [goal] andalso
       List.rev (!seen) = ["first", "last", "callback"] then OK ()
    else die (String.concatWith ", " (List.rev (!seen)))
  end

val goals_print =
    HOLPP.pp_to_string 75(
      HOLPP.block HOLPP.CONSISTENT 0 o
      HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
    )

(* The arguments handed to the continuation, which may use them on later
   goals, must be stripped of Req0/ReqD.  A marker surviving there is used
   as an ordinary rewrite, and the marker$Req0 hypothesis it carries then
   lands in the justification of the subgoal it rewrote, which fails the
   enclosing proof. *)
val _ =
  let
    val leaked = ref ([] : term list)
    val calls = ref 0
    fun marker_hyps th =
        List.filter (fn t => #Thy (dest_thy_const t) = "marker"
                             handle HOL_ERR _ => false)
                    (hyp th)
    fun start args recur =
        let
          fun main asms =
              (leaked := !leaked @ List.concat (map marker_hyps (args @ asms));
               calls := !calls + 1;
               if !calls >= 2 then ALL_TAC else recur main)
        in
          main
        end
  in
    tprint "process_taclist_then_bind strips Req0 for later goals";
    ignore (runtac (process_taclist_then_bind
              {arg = [mk_Req0 TRUTH]} start) ([], “p:bool”));
    if !calls < 2 then die "the recursive pass never ran"
    else if null (!leaked) then OK()
    else die ("marker hypotheses reached the tactic: " ^
              String.concatWith ", " (map term_to_string (!leaked)))
  end

(* The non-recursive entry point retains the ordinary ordering: filter the
   goal assumptions first, then strip every Req0/ReqD payload.  Only the
   final theorem's requirement checks survive across arguments. *)
val _ =
  let
    fun req_test (name, thl, input, output) =
        (tprint ("process_taclist_then: " ^ name);
         require_msg (check_result (goals_eq [([], output)])) goals_print
           (testtac (process_taclist_then {arg = thl} PURE_REWRITE_TAC))
           ([], input))
  in
    List.app req_test [
      ("Req0 fires", [mk_Req0 AND_CLAUSES], “p /\ T”, “p:bool”),
      ("Req0 succeeds without a match", [mk_Req0 AND_CLAUSES],
       “p /\ q”, “p /\ q”),
      ("ReqD fires", [mk_ReqD AND_CLAUSES], “p /\ T”, “p:bool”),
      ("Req0 over ReqD", [mk_Req0 (mk_ReqD AND_CLAUSES)],
       “p /\ T”, “p:bool”)
    ];
    List.app
      (fn (name, marked, input, errname) =>
          shouldfail {
            checkexn = check_HOL_ERRexn
                         (fn (_, f, _) => f = errname),
            printarg = K ("process_taclist_then: " ^ name),
            printresult = goals_print,
            testfn = testtac
                       (process_taclist_then {arg = [marked]} (K ALL_TAC))
          } ([], input))
      [("Req0 rejects remaining matches", mk_Req0 AND_CLAUSES,
        “p /\ T”, "REQUIRE0_TAC"),
       ("ReqD rejects no decrease", mk_ReqD AND_CLAUSES,
        “p /\ q”, "REQUIRE_DECREASE_TAC")]
  end

(* The ordinary entry point restarts wrapper construction from the
   original tactic for each argument: even an unmarked final theorem
   drops earlier checks. Check payload stripping/order as well as the
   surviving requirement. *)
val _ =
  let
    val goal = ([], “p /\ T”)
    fun strip th =
        let val th = case dest_Req0 th of SOME t => t | NONE => th
        in case dest_ReqD th of SOME t => t | NONE => th end
    fun same (a, b) =
        HOLset.equal(hypset a, hypset b) andalso concl a ~~ concl b
    fun stripped expected actual =
        if ListPair.allEq same (expected, actual) then ALL_TAC
        else raise Fail "requirement payloads changed or leaked"
    fun check route (name, thl, errname) =
        let
          val tac = route (stripped (map strip thl)) thl
          val label = "multiple requirements: " ^ name
        in
          case errname of
              NONE =>
              (tprint label;
               require_msg (check_result (goals_eq [goal])) goals_print
                 (testtac tac) goal)
            | SOME f =>
              shouldfail {
                checkexn = check_HOL_ERRexn (fn (_, name, _) => name = f),
                printarg = K label, printresult = goals_print,
                testfn = testtac tac
              } goal
        end
    val req0err = SOME "REQUIRE0_TAC"
    val reqDerr = SOME "REQUIRE_DECREASE_TAC"
  in
    List.app (check mk_require_tac) [
      ("ReqD then unmarked drops ReqD", [mk_ReqD AND_CLAUSES, TRUTH], NONE),
      ("unmarked then ReqD checks ReqD", [TRUTH, mk_ReqD AND_CLAUSES],
       reqDerr),
      ("Req0 then unmarked drops Req0", [mk_Req0 AND_CLAUSES, TRUTH], NONE),
      ("unmarked then Req0 checks Req0", [TRUTH, mk_Req0 AND_CLAUSES],
       req0err),
      ("ReqD then distinct Req0 drops ReqD",
       [mk_ReqD AND_CLAUSES, mk_Req0 NOT_CLAUSES], NONE),
      ("distinct Req0 then ReqD checks ReqD",
       [mk_Req0 NOT_CLAUSES, mk_ReqD AND_CLAUSES], reqDerr),
      ("Req0 then distinct Req0 drops first check",
       [mk_Req0 AND_CLAUSES, mk_Req0 NOT_CLAUSES], NONE),
      ("distinct Req0 then Req0 checks last argument",
       [mk_Req0 NOT_CLAUSES, mk_Req0 AND_CLAUSES], req0err)
    ];
    List.app
      (check (fn tac => fn thl =>
          process_taclist_then_bind {arg = thl}
            (fn args => fn _ => fn _ => tac args))) [
      ("bind retains earlier ReqD",
       [mk_ReqD AND_CLAUSES, TRUTH], reqDerr),
      ("bind retains earlier Req0",
       [mk_Req0 AND_CLAUSES, TRUTH], req0err)
    ]
  end

(* Unlike process_taclist_then_bind, the ordinary entry point also strips
   the wrappers from goal assumptions *)
val _ =
  let
    val req0 = prim_mk_const {Thy = "marker", Name = "Req0"}
    fun stripped thl =
        if List.exists (fn th => isSome (dest_Req0 th) orelse
                                 isSome (dest_ReqD th)) thl then
          raise mk_HOL_ERR "markerSelftest" "stripped" "Req wrapper leaked"
        else ALL_TAC
    val goal = ([req0], “p:bool”)
  in
    tprint "process_taclist_then strips Req0 from goal assumptions";
    require_msg (check_result (goals_eq [goal])) goals_print
      (testtac (process_taclist_then {arg = []} stripped)) goal
  end

(* UNABBREV_TAC would fail on a second pass, after its abbreviation has
   been removed. Recursive filtering must also see newly added assumptions,
   rather than reuse the initial fact list. VALID checks the composed proof. *)
val _ =
  let
    val p = “recursive_policy_p:bool”
    val q = mk_conj (p,p)
    val ignored0 = “recursive_ignored F:bool”
    val ignored1 = “recursive_ignored T:bool”
    val ignored_seed = mk_conj (ignored0,ignored1)
    val abbreviation = markerSyntax.mk_abbrev ("recursive_alias",boolSyntax.T)
    val goal = ([abbreviation,ignored_seed,p],p)
    fun check (name,policy,expected) =
      let
        val _ = tprint ("recursive arguments: " ^ name)
        val observed = ref ([] : term list list)
        fun record thl = observed := !observed @ [map concl thl]
        fun start args recur asms =
          (record (args @ asms);
           ASSUME_TAC (CONJUNCT2 (ASSUME ignored_seed)) THEN
           ASSUME_TAC (CONJ (ASSUME p) (ASSUME p)) THEN
           recur (fn thl => (record thl; ACCEPT_TAC (ASSUME p))))
        val tac = process_taclist_then_bind
          {arg=markerSyntax.Abbr ‘recursive_alias’ :: policy} start
        val (goals,justify) = runtac (VALID tac) goal
        val result = justify []
      in
        if null goals andalso
           list_compare (list_compare Term.compare) (!observed,expected) = EQUAL
           andalso concl result ~~ p andalso
           HOLset.isSubset (hypset result,
                            HOLset.fromList Term.compare (#1 goal))
        then OK () else die "recursive policy or once-only pretactic changed"
      end
  in
    check ("pretactic once and IgnAsm reapplied to new assumptions",
           [IgnAsm ‘recursive_ignored _ (* sa *)’],[[p],[q,p]]);
    check ("NoAsms retained across recursive passes",[NoAsms],[[],[]])
  end

val L12_asms = [“L1 :- (x:'a) = a”, “L2 :- (y:'a) = b”]
val _ = tprint "LLABEL_RES_THEN(1)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = y”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(2)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = b”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1", L"L2"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(3)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(x:'a) = y”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(4)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (“y:'a = c ” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(5)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN REWRITE_TAC [ASSUME “y:'a = c”]))
      (“y:'a = c” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(6)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(a:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN REWRITE_TAC [ASSUME “y:'a = c”, L"L1"]))
      (“y:'a = c” :: L12_asms, “x:'a = y”)

val _ = new_type ("tyop", 0);
val _ = new_constant("c1", “:tyop”)
val _ = new_constant("c2", “:tyop”)
val _ = overload_on ("hide", “marker$hide”);
val typed_goals_print =
    HOLFlags.with_bflags [(Parse.show_types, true)] goals_print
val asl0 = [“hide foo (P c1 /\ T /\ P x)”,
            “R c1 /\ T /\ R x”]
val _ = tprint "RULE_ASSUM_TAC doesn't hit hide"
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c1 /\ R x”],
                                    “Q c1 c2:bool”)]))
          typed_goals_print
          (testtac (RULE_ASSUM_TAC (REWRITE_RULE[])))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC doesn't hit hide"
val tyopEQ = new_axiom("tyopEQ", “c1:tyop = c2”);
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c2 /\ T /\ R x”],
                                    “Q c2 c2:bool”)]))
          typed_goals_print
          (testtac (SUBST_ALL_TAC tyopEQ))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC/CONJ_VALIDATE doesn't hit hide"
val _ = require_msg
          (check_result (goals_eq [(asl0, “x = c1”),
                                   ([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c1 /\ T /\ R c1”],
                                    “Q c1 c2:bool”)]))
          typed_goals_print
          (testtac (CONJ_VALIDATE (SUBST_ALL_TAC (ASSUME “x = c1”))))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "RULE_ASSUM_TAC hits unignored hide"
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ P x)”,
                                     “R c1 /\ R x”],
                                    “Q c1 c2:bool”)]))
          typed_goals_print
          (testtac $ unignoring_hide $ RULE_ASSUM_TAC $ REWRITE_RULE[])
          (asl0, “Q c1 c2:bool”)

val _ = new_constant("TEST", “:tyop -> bool”)
val condrwt = new_axiom("condrwt", “!x. TEST x ==> x = c1”);
val crwt = MATCH_MP condrwt (ASSUME “TEST y”)
val _ = tprint "CONJ_VALIDATE(1)"
val _ = require_msg
          (check_result (goals_eq[([], “TEST y /\ P c1”)]))
          typed_goals_print
          (testtac (CONJ_VALIDATE (REWRITE_TAC[crwt])))
          ([], “P (y:tyop):bool”)

fun thm_eq (hyps,t) th =
    HOLset.equal(hyps, hypset th) andalso t ~~ concl th

fun mklab s t = mk_comb(mk_comb(“suspendlabel”, mk_var(s, “:ind”)), t)
val rhyp = mklab "3 r" “!r q p. suspendimp p (suspendimp q r)”
val shyp = mklab "3 s" “!s q p. suspendimp p (suspendimp q s)”
val rshyp = mklab "3 r" “!s q p. suspendimp p (suspendimp q s)”
val p = mk_var("p", bool)
val q = mk_var("q", bool)

val _ = tprint "suspend (1)"
val _ = require_msg
          (check_result
             (thm_eq (
                 HOLset.fromList Term.compare [rhyp, shyp],
                 “p /\ q ==> r /\ s”)
             )
          )
          thm_to_string
          (fn tac => TAC_PROOF(([], “p /\ q ==> r /\ s”), tac))
          (rpt strip_tac >- suspend "r" >- suspend "s")

val _ = tprint "suspend (2)"
val _ = require_msg
          (check_result
             (thm_eq (
                 HOLset.fromList Term.compare [rshyp, rhyp],
                 “p /\ q ==> r /\ s”)
             )
          )
          thm_to_string
          (fn tac => TAC_PROOF(([], “p /\ q ==> r /\ s”), tac))
          (rpt strip_tac >- suspend "r" >- suspend "r")

val pq_th1 =
    TAC_PROOF(([], “p /\ q ==> q /\ p”),
              strip_tac >> conj_tac >- suspend "q" >- suspend "p")
val pq_th2 =
    TAC_PROOF(([], “p /\ q ==> q /\ p”),
              strip_tac >> conj_tac >> suspend "pq")

val _ = tprint "extract_suspended_goal (1)"
val _ = require_msg
          (check_result (goal_eq ([q, p], p)))
          goal_print
          (fn th => resumption_to_goal (extract_suspended_goal [th] "p"))
          pq_th1

val _ = tprint "extract_suspended_goal (2)"
val _ = require_msg
          (check_result (
              goal_eq (
                [],
                “resconj (suspendimp p (suspendimp q p))
                         (suspendimp p (suspendimp q q))”
              )
            )
          )
          goal_print
          (fn th => resumption_to_goal (extract_suspended_goal [th] "pq"))
          pq_th2

val _ = shouldfail {checkexn = is_struct_HOL_ERR "markerLib",
                    printarg = K "extract_suspended_goal fails (1)",
                    printresult = goal_print,
                    testfn = (fn th => resumption_to_goal (extract_suspended_goal [th] "pq"))}
                   pq_th1

val _ = HOLFlags.set_bflag (show_assums,true)
val _ = tprint "prim_resume (1a)"
fun pp {subresult,updated_main} =
    let open HOLPP
    in
      PrettyBlock(0,true,[],[
                    pp_thm subresult,
                    PrettyLineBreak,
                    pp_thm updated_main
                    ])
    end
fun one_b (Res {subresult,updated_main}) = (
  tprint "prim_resume (1b)";
  require_msg(check_result
                (fn {subresult,updated_main} =>
                    thm_eq (HOLset.fromList Term.compare [q], q)
                           subresult
                    andalso
                    thm_eq (HOLset.empty Term.compare, “p /\ q ==> q /\ p”)
                           updated_main))
             (HOLPP.pp_to_string 75 pp)
             (fn th => prim_resume (th, "q", first_assum ACCEPT_TAC))
             updated_main
)
  | one_b (Exn _) = die "Shouldn't happen in test"
val _ = require_msgk (check_result
                        (fn {subresult,updated_main} =>
                            thm_eq (HOLset.fromList Term.compare [p],p)
                                   subresult andalso
                            thm_eq (HOLset.fromList Term.compare [
                                       mklab "2 q"
                                             “!q p. suspendimp p (suspendimp q q)”
                                     ],
                                    “p /\ q ==> q /\ p”) updated_main))
                     pp
                     (fn th => prim_resume(th,"p",first_assum ACCEPT_TAC))
                     one_b
                     pq_th1
(* Test resconj with different closure-variable counts across sub-goals.
   After gen_tac on "!x. T /\ (x ==> x)", conj_tac gives:
     sub-goal 1 "([], T)" with fvs=[] so nclosure=0, and
     sub-goal 2 "([], x ==> x)" with fvs=[x] so nclosure=1.
   The two hypotheses have different nclosure counts encoded in their labels;
   extract_suspended_goal and resumption_to_goal must handle both correctly,
   stripping the right number of closure foralls per component. *)
val resconj_closure_th =
    TAC_PROOF(([], “!x:bool. T /\ (x ==> x)”),
              gen_tac >> conj_tac >> suspend "s")

val _ = tprint "prim_resume resconj+closure"
val _ = require_msg
          (check_result
             (fn {subresult,updated_main} =>
                  null (hyp updated_main) andalso
                  concl updated_main ~~ “!x:bool. T /\ (x ==> x)”))
          (HOLPP.pp_to_string 75 pp)
          (fn th => prim_resume(th, "s",
                                RESUME_TAC >>
                                TRY (ACCEPT_TAC TRUTH) >>
                                disch_then  ACCEPT_TAC))
          resconj_closure_th

val three_goals = “p /\ q /\ r ==> p /\ q /\ r”
val three_suspended = Feedback.quiet_messages store_thm
  ("three_suspended", three_goals,
   strip_tac >> conj_tac >- suspend "same"
   >- (conj_tac >> suspend "same"))

val _ = resume {suspension_name = "three_suspended", label_name = "same"}
               (RESUME_TAC >> FIRST_ASSUM ACCEPT_TAC) (Context.snapshot ())

val _ = tprint "Finalise three goals sharing one suspension label"
val _ = require_msg
          (check_result (thm_eq (HOLset.empty Term.compare, three_goals)))
          thm_to_string
          (finalise_suspended_thm DB.Unknown)
          "three_suspended"

val _ = tprint "prim_resume preserves order for three suspended goals"
val _ = require_msg
          (check_result
             (fn {subresult,updated_main} =>
                  thm_eq (HOLset.empty Term.compare, three_goals) updated_main))
          (HOLPP.pp_to_string 75 pp)
          (fn th => prim_resume(th, "same",
                               RESUME_TAC >> FIRST_ASSUM ACCEPT_TAC))
          three_suspended

val nested_goal = “(marker$resconj T T) /\ T”
val nested_suspended = Feedback.quiet_messages store_thm
  ("nested_suspended", nested_goal, conj_tac >> suspend "nested")

val _ = resume {suspension_name = "nested_suspended", label_name = "nested"}
               (RESUME_TAC >> ACCEPT_TAC TRUTH) (Context.snapshot ())

val _ = tprint "Finalise preserves resconj inside a suspended goal"
val _ = require_msg
          (check_result (thm_eq (HOLset.empty Term.compare, nested_goal)))
          thm_to_string
          (finalise_suspended_thm DB.Unknown)
          "nested_suspended"

val _ = tprint "prim_resume preserves resconj inside a suspended goal"
val _ = require_msg
          (check_result
             (fn {subresult,updated_main} =>
                  thm_eq (HOLset.empty Term.compare, nested_goal) updated_main))
          (HOLPP.pp_to_string 75 pp)
          (fn th => prim_resume(th, "nested", RESUME_TAC >> ACCEPT_TAC TRUTH))
          nested_suspended

(* Under the new cross-file suspend/resume design, a suspended theorem is
   a perfectly valid export (as a theorem with suspendlabel hypotheses);
   export_theory no longer fails on unfinalised suspensions. *)
val incomplete_th = Feedback.quiet_messages save_thm("incomplete_th", pq_th1)

(* UNABBREV_TAC on a name with no matching abbrev assumption used to fail
   inside FIRST_ASSUM with an empty error message; it should now report a
   clear UNABBREV_TAC error mentioning the missing abbreviation. (#1483) *)
val _ = tprint "UNABBREV_TAC missing abbrev gives clear error"
val _ = shouldfail {
  checkexn = check_HOL_ERRexn
               (fn (_, fnnm, msg) =>
                   fnnm = "UNABBREV_TAC" andalso
                   String.isSubstring "MISSING_ABBR" msg),
  printarg = K "UNABBREV_TAC \"MISSING_ABBR\" with no such abbrev",
  printresult = goals_print,
  testfn = (fn g => testtac (UNABBREV_TAC "MISSING_ABBR") g)
} ([“(P:'a -> bool) x”], “(Q:'a -> bool) x”)
