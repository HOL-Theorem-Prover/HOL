open HolKernel Parse boolLib
open testutils TotalDefn numLib

val _ = new_theory "scratch"

val _ = Feedback.emit_MESG := false

fun badpp x = HOLPP.add_string "<Can't print this>"

fun EVAL t = computeLib.CBV_CONV (computeLib.the_compset()) t
val _ = tprint "Testing mutually recursive function definition"

val f_def = require (check_result (K true)) Define`
  (f x = if x = 0 then T else ~g(x - 1)) /\
  (g x = if x = 0 then F else ~f(x - 1))
`

val _ = tprint "Testing definition over literals"

val h_def = Define`
  (h 0 = T) /\ (h 1 = F)
`;

val _ = let
  val cs = strip_conj (concl h_def)
  val _ = if length cs = 2 then () else die "FAILED!"
  val _ = if List.all (is_const o rhs) cs then () else die "FAILED!"
in
  OK()
end

val _ = tprint "Testing form of derived induction principle"
val fact_def = Define`fact n = if n < 2 then 1 else n * fact(n - 1)`;

val desired_ind =
  ``!P. (!n. (~(n < 2) ==> P (n - 1)) ==> P n) ==> !v. P v``

val _ = if aconv desired_ind (concl (theorem "fact_ind")) then OK()
        else die "FAILED!\n"

val _ = tprint "Define schema(1)"
val _ = require (check_result (K true)) (quietly DefineSchema)
                `(fs 0 y = z + y) /\ (fs x y = x)`;
val _ = tprint "Define schema(2)"
val _ = require (check_result (K true)) (quietly DefineSchema)
                `(gs 0 y = x + y) /\ (gs x y = x)`;

val _ = tprint "Testing 0-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f1 = \x. case x of 0 => 0n | SUC n => f1 n
`

val _ = tprint "Testing 1-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f2 (y : 'a) = \x. case x of 0 => 0n | SUC n => f2 y n
`;

val _ = tprint "Testing 2-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f3 (y : 'a) (z : 'a) = \x. case x of 0 => 0n | SUC n => f3 y z n
`;

val _ = tprint "Testing 2-arg mutual recursive function"

val f4_def = require (check_result (K true)) (quietly Define)`
  f4 0 x = (0, x) /\
  f4 (SUC n) x = f5 n (x, x) /\
  f5 0 (x, y) = (0, y) /\
  f5 (SUC n) (x, y) = f4 n x
`;

fun rhs_abstractions n th =
  let val cs = strip_conj (concl th)
  in length cs = n andalso List.all (is_abs o rhs o snd o strip_forall) cs
  end

val _ = tprint "Testing mutual recursion with lambda-valued equations"

val f6_def = require (check_result (rhs_abstractions 4)) (quietly Define)`
  f6 0 = (\b. b) /\
  f6 (SUC n) = (\b. f7 n b) /\
  f7 0 = (\b. ~b) /\
  f7 (SUC n) = (\b. f6 n b)
`;

val _ = tprint "Testing 2-arg mutual recursion with lambda-valued equations"

val h1_def = require (check_result (rhs_abstractions 4)) (quietly Define)`
  h1 0 m = (\b. if b then m else 0n) /\
  h1 (SUC n) m = (\b. h2 n b m) /\
  h2 0 b = (\m. m:num) /\
  h2 (SUC n) b = (\m. h1 n m b)
`;

val _ = tprint "Testing multi-clause recursion with lambda-valued equations"

val g_def = require (check_result (rhs_abstractions 2)) (quietly Define)`
  g 0 = (\x. x) /\
  g (SUC n) = (\x. g (n DIV 2) x)
`;

fun tdefoutput_pp(th,thopt) =
    "(" ^ thm_to_string th ^ ", " ^
    (case thopt of NONE => "NONE"
                 | SOME th' => "SOME " ^ thm_to_string th') ^ ")"

fun quietDefn f x =
    Lib.with_flag (Globals.interactive, false) f x

val _  =
  shouldfail
    { checkexn = is_struct_HOL_ERR "TotalDefn",
      printarg = K "tDefine: no schematic defs when termination tac is supplied",
      printresult = tdefoutput_pp,
      testfn = (fn q => in_repl_mode (TotalDefn.tDefine "foo" q) (WF_REL_TAC ‘$<’))}
   ‘foo x = if x = 0 then y else foo(x - 1)*2’;

val _  =
  shouldfail
    { checkexn = is_struct_HOL_ERR "TotalDefn",
      printarg = K "qDefine: no schematic defs when termination tac is supplied",
      printresult = thm_to_string,
      testfn = (fn q => in_repl_mode(TotalDefn.qDefine "foo" q) (SOME (WF_REL_TAC ‘$<’)))}
   ‘foo x = if x = 0 then y else foo(x - 1)*2’;

fun lhs_has_two_args th =
    th |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #2 |> length
       |> equal 2

val _ = tprint "qDefine/schematic, no termination"
val _ = require_msg (check_result lhs_has_two_args)
                    thm_to_string
                    (fn q => quiet_messages
                               (quietDefn
                                  (TotalDefn.qDefine "foo1[schematic]" q))
                               NONE)
                    ‘foo1 x = if x = 0 then y else foo1(x - 1)*2’;

fun allquiet f x =
    quiet_messages (quiet_warnings (quietDefn f)) x

val _ = tprint "qDefine/schematic, termination"
val _ = require_msg (check_result lhs_has_two_args)
                    thm_to_string
                    (fn q => allquiet
                               (TotalDefn.qDefine "foo2[schematic]" q)
                               (SOME (WF_REL_TAC ‘$<’)))
                    ‘foo2 x = if x = 0 then y else foo2(x - 1)*2’;

val _ = tprint "tailrecDefine (simple recursion: fact2)"
val expected_pat = “!A n. ff A n = if n < 1 then A else ff (A * n) (n - 1)”
fun check1 th =
    case match_term expected_pat (concl th) of
        ([{redex,residue}], []) =>
          aconv redex “ff:num->num->num” andalso
          #1 (dest_const residue) = "fact2"
      | _ => false
fun check2 _ = convtest("fact2 evaluates OK", EVAL, “fact2 1 6”, “720”)
val _ = require_msgk (check_result check1) pp_thm
                     (fn q => TotalDefn.qDefine "fact2_def[tailrecursive]"
                                                q NONE)
                     check2
                     ‘fact2 A n = if n < 1 then A else fact2 (A * n) (n-1)’;

val _ = tprint "tailrecDefine (simple recursion + rebind: fact)"
val expected_pat = “!A n. ff A n = if n < 1 then A else ff (A * n) (n - 1)”
fun check1 th =
    case match_term expected_pat (concl th) of
        ([{redex,residue}], []) =>
          aconv redex “ff:num->num->num” andalso
          #1 (dest_const residue) = "fact"
      | _ => false
fun check2 _ = convtest("fact evaluates OK", EVAL, “fact 1 5”, “120”)
val _ = require_msgk (check_result check1) pp_thm
                     (allquiet
                        (fn q =>
                            TotalDefn.qDefine
                              "fact_def[tailrecursive,allow_rebind]" q NONE))
                     check2
                     ‘fact A n = if n < 1 then A else fact (A * n) (n-1)’;

val _ = tprint "tailrecDefine (2-way mutual recursion)"
val expected_pat = “(!x. ff1 x = if x = 0 then F else ff2 (x + 1)) /\
                    (!n. ff2 n = if n = 0 then T
                                else if n = 1 then F
                                else if n = 2 then T
                                else ff1 (n - 3))”
fun check1 th =
    case match_term expected_pat (concl th) of
        (tms as [rr1,rr2], []) => List.all (is_const o #residue) tms
      | _ => false
fun check2 _ =
    (tprint "DefnBase has record for even";
     require_msgk (check_result Option.isSome) badpp DefnBase.lookup_userdef
                  (fn _ => convtest ("even evaluates OK", EVAL, “even 11”, “F”))
                  “even”)
val _ = require_msgk (check_result check1) pp_thm
                     (allquiet
                        (fn q =>
                            TotalDefn.qDefine
                              "odd_def[tailrecursive]" q NONE))
                     check2
                     ‘(odd x = if x = 0 then F else even (x + 1)) /\
                      (even n = if n = 0 then T
                                    else if n = 1 then F
                                    else if n = 2 then T
                                    else odd (n - 3))’;

val _ = tprint "tailrecDefine (2-way + isolate & nocompute)"
val _ = require_msgk (check_result (K true)) pp_thm
                     (fn q =>
                         TotalDefn.qDefine
                           "urk_def[tailrecursive,nocompute]" q NONE)
                     (fn _ => convtest("urk unevals", EVAL,
                                       “urk x + urk' m”, “urk x + urk' m”))
                     ‘(urk n = urk2 (n + 1)) /\
                      (urk' n = n + 1) /\
                      (urk2 m = if m = 0 then 1 else urk (2 * m))’;

val _ = tprint "DB doesn't pick up location-info"
val _ = let
  val loc = DB_dtype.mkloc("foo", 11, true)
  val expected = {loc = loc, class = DB_dtype.Def, private = false}
in
  require_msg (check_result (equal expected o #2))
              (DB_dtype.thminfo_toString o #2)
              (fn () => (TotalDefn.located_qDefine loc "bar" `bar=1` NONE
                                                   (Context.snapshot());
                         valOf $ DB.lookup{Thy="-", Name = "bar"}))
              ()
end

(* ----------------------------------------------------------------------
    TFL registers the support definitions it makes on the way
    (<stem>_tupled_primitive and the like) as user definitions, then
    deletes their constants once the real definition is made.  Walking
    the user definitions must skip those entries rather than fail.
   ---------------------------------------------------------------------- *)

val _ = tprint "current_userdefs/thy_userdefs after TFL deletes _tupled"
val _ = quietly (fn q => TotalDefn.qDefine "udef_rec_def" q NONE)
          ‘udef_rec x (y:num) = if y = 0 then x else udef_rec (x + 1) (y - 1)’
val _ = let
  fun defines_udef_rec (p : DefnBase.defn_presentation) =
      same_const (#const p) “udef_rec”
  fun support_entry (p : DefnBase.defn_presentation) =
      String.isSubstring "_tupled" (#Name (#thmname p))
  val cur = DefnBase.current_userdefs ()
  val thy = DefnBase.thy_userdefs {thyname = current_theory ()}
in
  if List.exists defines_udef_rec cur andalso
     List.exists defines_udef_rec thy andalso
     not (List.exists support_entry thy)
  then OK ()
  else die "udef_rec missing, or a deleted support constant listed"
end

(* ----------------------------------------------------------------------
    A failed definition made from inside a goalstack tactic.  TotalDefn
    hands the termination goal to the proof manager, so expand must let
    the tactic re-enter the proof manager.  The deadlock itself is guarded
    by src/proofman/interactive_tests.
   ---------------------------------------------------------------------- *)

val _ = HOLFlags.set_bflag (proofManagerLib.chatting, false)
val user_goal : goal = ([], mk_var ("user_goal", Type.bool))
fun top_is (g : goal) =
    aconv (snd (proofManagerLib.top_goal ())) (snd g) handle _ => false
val _ = proofManagerLib.drop_all ()
val _ = proofManagerLib.set_goal user_goal

val _ = tprint "Define's failed termination goal reaches the goalstack"
fun bad_define_tac (g : goal) =
    (Define ‘bad_in_tac (n:num) = bad_in_tac (n + 1)’; ALL_TAC g)
val _ = (in_repl_mode (quietly proofManagerLib.e) bad_define_tac;
         die "e succeeded")
        handle HOL_ERR _ => ()
val _ = if is_exists (snd (proofManagerLib.top_goal ())) andalso
           (proofManagerLib.drop (); top_is user_goal)
        then OK () else die "wrong proof state"
val _ = proofManagerLib.drop_all ()

(* Definitions with an explicit termination proof, in stages *)
fun rejects f = (f (); false) handle HOL_ERR _ => true
fun assert b = if b then () else die "staged termination check failed"
fun auto_import () = HOLFlags.get_bflag computeLib.auto_import_definitions
fun stored nm = Option.isSome (DB.lookup {Thy = "-", Name = nm})
fun no_pending nm = rejects (fn () => complete_definition nm TRUTH)

val attribute_calls = ref ([] : string list)
fun staged_attribute {name,attrname,args,thm} =
  (assert (auto_import ());
   attribute_calls := name :: !attribute_calls)
val _ = ThmAttribute.register_attribute
          ("staged_test", {localf = staged_attribute,
                           storedf = staged_attribute})

val _ = tprint "native completion stores, registers and runs attributes"
val native_loc = DB_dtype.mkloc ("staged-test", 42, true)
val native_fac = located_qDefine native_loc
  "native_fac_def[staged_test,induction=native_fac_steps]"
  ‘native_fac n = if n < 2 then 1 else n * native_fac (n - 1)’
  (SOME (WF_REL_TAC ‘$<’)) (Context.snapshot ())
val _ = assert (!attribute_calls = ["native_fac_def"])
val _ = assert (#loc (#2 (valOf (DB.lookup {Thy="-",Name="native_fac_def"})))
                = native_loc)
val _ = assert (stored "native_fac_steps")
val _ = assert (Option.isSome (DefnBase.lookup_userdef “native_fac”))
val _ = assert (Option.isSome (DefnBase.lookup_indn “native_fac”))
val _ = assert (no_pending "native_fac_def")
val _ = OK ()
val _ = convtest ("native definition enters EVAL", EVAL,
                 “native_fac 5”, “120”)

val _ = tprint "flags surround the termination proof, not the attributes"
fun check_flags g =
  (assert (not (auto_import ()));
   assert (HOLFlags.get_bflag allow_schema_definition);
   assert (HOLFlags.get_bflag Theory.allow_rebinds);
   assert (!Defn.def_suffix = "" andalso !Defn.ind_suffix = " flag_steps");
   WF_REL_TAC ‘$<’ g)
val _ = qDefine
  "flag_def[nocompute,schematic,allow_rebind,induction=flag_steps,staged_test]"
  ‘flag_fun n = if n = 0 then y else flag_fun (n - 1) * 2’
  (SOME check_flags)
val _ = assert (auto_import () andalso stored "flag_steps")
val _ = assert (hd (!attribute_calls) = "flag_def")
val _ = OK ()
val _ = convtest ("nocompute stays out of EVAL", EVAL,
                 “flag_fun y 2”, “flag_fun y 2”)

val _ = tprint "trivial definitions ignore explicit tactics"
val ignored_calls = ref 0
fun ignored_tac g = (ignored_calls := !ignored_calls + 1; ALL_TAC g)
val _ = qDefine "staged_abbrev_def" ‘staged_abbrev = 7n’ (SOME ignored_tac)
val _ = qDefine "staged_prim_def"
    ‘(staged_prim 0 = 0n) /\
     (staged_prim (SUC n) = SUC (staged_prim n))’ (SOME ignored_tac)
val _ = assert (!ignored_calls = 0)
val _ = assert (not (Option.isSome
  (prepare_qDefine "staged_abbrev2_def" ‘staged_abbrev2 = 8n’)))
val _ = assert (stored "staged_abbrev2_def")
val _ = OK ()

val _ = tprint "a failed termination proof leaves nothing pending"
val _ = assert (rejects (fn () => ignore
  (in_repl_mode (qDefine "bad_staged_def"
    ‘bad_staged n = if n = 0 then 0n else bad_staged (n - 1) + 1’)
    (SOME ALL_TAC))))
val _ = assert (no_pending "bad_staged_def" andalso
                not (stored "bad_staged_def"))
val _ = OK ()

val _ = tprint "prepare_qDefine keeps support constants until completion"
val consts_before = length (thy_consts (current_theory ()))
val nested_goal = valOf (prepare_qDefine
  "nested_def[staged_test,induction=nested_steps]"
  ‘nested n = if n = 0 then 0n else nested (nested (n - 1) MOD n)’)
val consts_pending = length (thy_consts (current_theory ()))
val _ = assert (consts_pending > consts_before + 1)
val _ = assert (not (stored "nested_def") andalso not (stored "nested_steps"))
val _ = assert (rejects (fn () => complete_definition "nested_def" TRUTH))
val _ = assert (rejects (fn () =>
  located_finalise_definition DB.Unknown "nested_def"))
val nested_def =
    complete_definition "nested_def" (TAC_PROOF (nested_goal, WF_REL_TAC ‘$<’))
val _ = assert (length (thy_consts (current_theory ())) < consts_pending)
val _ = assert (null (hyp nested_def) andalso stored "nested_steps")
val _ = assert (hd (!attribute_calls) = "nested_def")
val _ = assert (Option.isSome (DefnBase.lookup_indn “nested”))
val _ = assert (no_pending "nested_def")
val _ = assert (rejects (fn () => complete_definition "nowhere_def" TRUTH))
val _ = OK ()

val _ = tprint "deferred completion keeps the flags of its preparation"
val ambient_goal = valOf (HOLFlags.with_bflags
  [(computeLib.auto_import_definitions, false)]
  (prepare_qDefine "ambient_def")
  ‘ambient n = if n = 0 then 0n else ambient (n - 1) + 1’)
val _ = assert (rejects (fn () => in_repl_mode (prepare_qDefine "ambient_def")
  ‘ambient2 n = if n = 0 then 0n else ambient2 (n - 1) + 1’))
val _ = assert (auto_import ())
val _ = complete_definition "ambient_def"
          (TAC_PROOF (ambient_goal, WF_REL_TAC ‘$<’))
val _ = OK ()
val _ = convtest ("ambient nocompute stays out of EVAL", EVAL,
                 “ambient 2”, “ambient 2”)

val _ = tprint "a suspended termination proof completes at finalisation"
val suspend_loc = DB_dtype.mkloc ("staged-test", 77, true)
val suspended_eqns = located_qDefine suspend_loc
  "susp_def[staged_test,induction=susp_steps]"
  ‘susp n = if n = 0 then 0n else susp (n - 1) + 1’
  (SOME (Q.EXISTS_TAC ‘$<’ THEN markerLib.suspend "tc"))
  (Context.snapshot ())
val _ = assert (not (null (hyp suspended_eqns)))
val _ = assert (not (stored "susp_def") andalso not (stored "susp_steps"))
val _ = assert (hd (!attribute_calls) <> "susp_def")
val _ = assert (Option.isSome (markerLib.lookup_suspension "susp_def"))
val _ = assert (rejects (fn () => complete_definition "susp_def" TRUTH))
val susp_helper = store_thm ("susp_helper", “!n. n <> 0 ==> n - 1 < n”,
                             DECIDE_TAC)
val _ = markerLib.resume {suspension_name = "susp_def", label_name = "tc"}
          (markerLib.RESUME_TAC THEN CONJ_TAC THENL
             [WF_TAC, REPEAT STRIP_TAC THEN MATCH_MP_TAC susp_helper THEN
                      FIRST_ASSUM ACCEPT_TAC])
          (Context.snapshot ())
val _ = assert (rejects (fn () =>
  located_finalise_definition DB.Unknown "susp_def[simp]"))
val susp_def = located_finalise_definition suspend_loc "susp_def"
val _ = assert (null (hyp susp_def) andalso
                aconv (concl susp_def) (concl suspended_eqns))
val _ = assert (null (hyp (DB.fetch "-" "susp_steps")))
val _ = assert (#loc (#2 (valOf (DB.lookup {Thy="-",Name="susp_def"})))
                = suspend_loc)
val _ = assert (hd (!attribute_calls) = "susp_def")
val _ = assert (Option.isSome (DefnBase.lookup_userdef “susp”))
val _ = assert (Option.isSome (DefnBase.lookup_indn “susp”))
val _ = assert (not (Option.isSome (markerLib.lookup_suspension "susp_def")))
val _ = assert (no_pending "susp_def")
val _ = OK ()
val _ = convtest ("finalised definition enters EVAL", EVAL,
                 “susp 3”, “3”)

val _ = tprint "a failed finalisation can be retried"
val fail_next = ref true
fun fail_once {name,attrname,args,thm} =
  if !fail_next then (fail_next := false; raise mk_HOL_ERR "" "" "once")
  else ()
val _ = ThmAttribute.register_attribute
          ("fail_once", {localf = fail_once, storedf = fail_once})
val _ = located_qDefine DB.Unknown "retry_def[allow_rebind,fail_once]"
  ‘retry n = if n = 0 then 0n else retry (n - 1) + 1’
  (SOME (Q.EXISTS_TAC ‘$<’ THEN markerLib.suspend "tc"))
  (Context.snapshot ())
val _ = markerLib.resume {suspension_name = "retry_def", label_name = "tc"}
          (markerLib.RESUME_TAC THEN CONJ_TAC THENL
             [WF_TAC, REPEAT STRIP_TAC THEN MATCH_MP_TAC susp_helper THEN
                      FIRST_ASSUM ACCEPT_TAC])
          (Context.snapshot ())
val _ = assert (rejects (fn () =>
  located_finalise_definition DB.Unknown "retry_def"))
val retry_def = located_finalise_definition DB.Unknown "retry_def"
val _ = assert (aconv (concl retry_def) (concl (DB.fetch "-" "retry_def")))
val _ = assert (not (is_conj (concl retry_def)) andalso
                Option.isSome (DefnBase.lookup_userdef “retry”) andalso
                no_pending "retry_def")
val _ = OK ()

val _ = tprint "mutual definitions complete through prepare_qDefine"
val mutual_goal = valOf (prepare_qDefine "mev_def[induction=mev_steps]"
  ‘(mev n = if n = 0 then T else mod (n - 1)) /\
   (mod n = if n = 0 then F else mev (n - 1))’)
val mev_def = complete_definition "mev_def"
  (TAC_PROOF (mutual_goal, WF_REL_TAC ‘measure (\x. sum_CASE x I I)’))
val _ = assert (length (strip_conj (concl mev_def)) = 2 andalso
                stored "mev_steps" andalso no_pending "mev_def")
val _ = OK ()
val _ = convtest ("mutual definition enters EVAL", EVAL, “mod 3”, “T”)

(* Last, since it discards the scratch theory *)
val _ = tprint "a definition pending in another theory is not completed"
fun rejects_with s f =
  (f (); false) handle HOL_ERR e => String.isSubstring s (message_of e)
val _ = prepare_qDefine "elsewhere_def"
  ‘elsewhere n = if n = 0 then 0n else elsewhere (n - 1) + 1’
val _ = with_flag (Globals.interactive, true) new_theory "staged_other"
val _ = assert (rejects_with "pending in theory scratch"
                  (fn () => complete_definition "elsewhere_def" TRUTH))
val _ = OK ()

val _ = if Systeml.ML_SYSNAME <> "poly" then () else let
  val hol = OS.Path.concat (Systeml.HOLDIR, "bin/hol")
  val heap = "staged-termination.save"
  fun remove f = OS.FileSys.remove f handle OS.SysErr _ => ()
  fun run args = OS.Process.isSuccess (Systeml.systeml (hol :: args))
  val _ = remove heap
  val _ = tprint "a heap saved mid-proof completes the definition once"
  val _ = assert (run ["run", "--holstate=numheap", "tests/staged-save.sml"])
  val _ = assert (run ["run", "--holstate=" ^ heap,
                       "tests/staged-restore.sml"])
  val _ = remove heap
in OK () end
