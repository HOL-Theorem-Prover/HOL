open HolKernel Parse boolLib testutils markerLib simpMarkerLib
val _ = new_theory "simpMarkerTest"
val _ = HOLFlags.set_bflag (Parse.avoid_unicode, true)
val goal_compare = pair_compare (list_compare Term.compare, Term.compare)
fun goals_eq a b = list_compare goal_compare (a,b) = EQUAL
fun thm_eq (hyps,t) th = HOLset.equal (hyps,hypset th) andalso t ~~ concl th
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
       (prim_mk_const {Thy="simpMarker", Name="ExcludeX"})))
     term_to_string I “simpMarker$ExcludeX”)

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
       fn Legacy (DAC (a, b)) => same a andalso concl b ~~ T | _ => false),
      ("Cong", fn () => Cong th, fn Legacy (DCong a) => same a | _ => false),
      ("Split", fn () => simpMarkerLib.Split th,
       fn DSplit a => same a | _ => false),
      ("Excl", fn () => Excl "nm", fn Legacy (DExcl "nm") => true | _ => false),
      ("ExclX", fn () => ExclX "nm", fn DExclX "nm" => true | _ => false),
      ("ExclSF", fn () => ExclSF "nm", fn Legacy (DExclSF "nm") => true | _ => false),
      ("FRAG", fn () => FRAG "nm", fn Legacy (DFRAG "nm") => true | _ => false),
      ("Req0", fn () => mk_Req0 th, fn Legacy (DReq0 a) => same a | _ => false),
      ("ReqD", fn () => mk_ReqD th, fn Legacy (DReqD a) => same a | _ => false),
      ("Once", fn () => BoundedRewrites.Once th,
       fn Legacy (DBounded (a, 1)) => same a | _ => false),
      ("Ntimes 3", fn () => BoundedRewrites.Ntimes th 3,
       fn Legacy (DBounded (a, 3)) => same a | _ => false),
      ("NoAsms", fn () => NoAsms, fn Legacy (DNoAsms) => true | _ => false),
      ("IgnAsm", fn () => IgnAsm ‘x = _’,
       fn Legacy (DIgnAsm s) => String.isSuffix "x = _" s | _ => false),
      ("Abbr", fn () => Abbr`v`, fn Legacy (DAbbr "v") => true | _ => false),
      ("L", fn () => L "lab", fn Legacy (DLabel "lab") => true | _ => false),
      ("Req0 wraps Cong", fn () => mk_Req0 (Cong th),
       fn Legacy (DReq0 a) => (case dest_directive a of
                          SOME (Legacy (DCong b)) => same b
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
             SOME (Legacy (DExcl s)) => s = nm | _ => false) andalso
        (case dest_directive (ExclSF nm) of
             SOME (Legacy (DExclSF s)) => s = nm | _ => false) andalso
        (case dest_directive (FRAG nm) of
             SOME (Legacy (DFRAG s)) => s = nm | _ => false)
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
    val nonvar = EQT_ELIM (ISPEC T simpMarkerTheory.ExcludeX_def)
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
                  (prim_mk_const {Thy="simpMarker", Name="ExcludeX"}));
    check "ExclX rejects non-markers, non-variable args and variable heads"
      (List.all (fn th => destExclX th = NONE)
                [TRUTH, ASSUME T, nonvar, impostor] andalso
       not (is_directive nonvar) andalso not (is_directive impostor));
    check "ExclX requirement/bounded wrappers preserve payload and hyps"
      (List.all payload wrapped);
    check "ExclX Req0 takes precedence over ReqD and bounds"
      (case dest_directive (mk_Req0 (mk_ReqD (BoundedRewrites.Once x))) of
           SOME (Legacy (DReq0 p)) =>
           (case dest_directive p of
                SOME (Legacy (DReqD q)) =>
                (case dest_directive q of
                     SOME (Legacy (DBounded (r, 1))) => same r | _ => false)
              | _ => false)
         | _ => false);
    check "ExclX bounds take precedence over the marker head"
      (case dest_directive (BoundedRewrites.Ntimes x 3) of
           SOME (Legacy (DBounded (p, 3))) => same p | _ => false)
  end

(* The theorem list handed to the recursive pass must be stripped of
   Req0/ReqD just like the outer one.  simpLib re-enters through [recur]
   after a looper fires; a marker surviving there is used as an ordinary
   rewrite, and the marker$Req0 hypothesis it carries then lands in the
   justification of the subgoal it rewrote, which fails the enclosing
   proof. *)
val _ =
  let
    val leaked = ref ([] : term list)
    val calls = ref 0
    fun marker_hyps th =
        List.filter (fn t => #Thy (dest_thy_const t) = "marker"
                             handle HOL_ERR _ => false)
                    (hyp th)
    fun start recur =
        let
          fun main thl =
              (leaked := !leaked @ List.concat (map marker_hyps thl);
               calls := !calls + 1;
               if !calls >= 2 then ALL_TAC else recur main)
        in
          main
        end
  in
    tprint "process_taclist_then_recur strips Req0 for recursion";
    ignore (runtac (process_taclist_then_recur
              {arg = [mk_Req0 TRUTH]} start) ([], “p:bool”));
    if !calls < 2 then die "the recursive pass never ran"
    else if null (!leaked) then OK()
    else die ("marker hypotheses reached the tactic: " ^
              String.concatWith ", " (map term_to_string (!leaked)))
  end

fun testtac tac = #1 o runtac (VALID tac)
val goal_print = HOLPP.pp_to_string 75 goalStack.pp_goal

val goals_print =
    HOLPP.pp_to_string 75(
      HOLPP.block HOLPP.CONSISTENT 0 o
      HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
    )

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
          process_taclist_then_recur {arg = thl} (K tac))) [
      ("recursive route retains earlier ReqD",
       [mk_ReqD AND_CLAUSES, TRUTH], reqDerr),
      ("recursive route retains earlier Req0",
       [mk_Req0 AND_CLAUSES, TRUTH], req0err)
    ]
  end

(* This distinguishes the ordinary entry point from a delegation to
   [recur]: the latter strips only the supplied arguments, not goal
   assumptions. *)
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

val _ =
    let val th = ASSUME “p:bool”
    in
      tprint "Split marker round-trip";
      require_msg
        (check_result (thm_eq (hypset th, concl th)))
        thm_to_string
        (destSplit o Split)
        th
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
        fun start recur thl =
          (record thl;
           ASSUME_TAC (CONJUNCT2 (ASSUME ignored_seed)) THEN
           ASSUME_TAC (CONJ (ASSUME p) (ASSUME p)) THEN
           recur (fn thl => (record thl; ACCEPT_TAC (ASSUME p))))
        val tac = process_taclist_then_recur
          {arg=markerSyntax.Abbr ‘recursive_alias’ :: policy} start
        val (goals,justify) = runtac (VALID tac) goal
        val result = justify []
      in
        if null goals andalso
           list_compare (list_compare Term.compare) (!observed,expected) = EQUAL
           andalso concl result ~~ p andalso
           HOLset.isSubset (hypset result,HOLset.fromList Term.compare (#1 goal))
        then OK () else die "recursive policy or once-only pretactic changed"
      end
  in
    check ("pretactic once and IgnAsm reapplied to new assumptions",
           [IgnAsm ‘recursive_ignored _ (* sa *)’],[[p],[q,p]]);
    check ("NoAsms retained across recursive passes",[NoAsms],[[],[]])
  end

val _ = OS.Process.exit OS.Process.success
