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
    A failed definition made from inside a goalstack tactic.  TotalDefn
    hands the termination goal to the proof manager, so expand must let
    the tactic re-enter the proof manager.  The deadlock itself is guarded
    by src/proofman/interactive_tests.
   ---------------------------------------------------------------------- *)

val _ = proofManagerLib.chatting := false
val user_goal : goal = ([], mk_var ("user_goal", Type.bool))
fun top_is (g : goal) =
    aconv (snd (proofManagerLib.top_goal ())) (snd g) handle _ => false
val _ = proofManagerLib.drop_all ()

(* Completion is private to the proof context, and is consumed by both
   native completion and failed direct completion. *)
fun rejects f = (f (); false) handle HOL_ERR _ => true
fun assert b = if b then () else die "termination finisher check failed"
fun consumed finish th =
  (finish th; false) handle HOL_ERR e =>
    Feedback.top_function_of e = "termination_finisher" andalso
    Feedback.message_of e = "Definition already completed or failed"
val pending : (thm -> thm) option ref = ref NONE
fun capture g ctxt =
  (pending := current_termination_finisher ctxt; ALL_TAC g ctxt)
val _ = assert (not (Option.isSome
  (current_termination_finisher (Context.snapshot ()))))

val attribute_calls = ref ([] : string list)
fun finisher_attribute {name,attrname,args,thm} =
  (assert (Feedback.current_trace "computeLib.auto_import_definitions" = 1);
   attribute_calls := name :: !attribute_calls)
val _ = ThmAttribute.register_attribute
          ("finisher_test", {localf = finisher_attribute,
                             storedf = finisher_attribute})

val _ = tprint "native completion consumes its context finisher"
val finisher_loc = DB_dtype.mkloc ("finisher-test", 42, true)
val native_fac = located_qDefine finisher_loc
  "native_fac_def[finisher_test,induction=native_fac_steps]"
  ‘native_fac n = if n < 2 then 1 else n * native_fac (n - 1)’
  (SOME (capture THEN WF_REL_TAC ‘$<’)) (Context.snapshot ())
val _ = assert (Option.isSome (!pending))
val _ = assert (consumed (valOf (!pending)) TRUTH)
val _ = assert (!attribute_calls = ["native_fac_def"])
val _ = assert (#loc (#2 (valOf (DB.lookup {Thy="-",Name="native_fac_def"})))
                = finisher_loc)
val _ = assert (Option.isSome (DefnBase.lookup_userdef “native_fac”))
val _ = assert (Option.isSome (DefnBase.lookup_indn “native_fac”))
val _ = assert (not (Option.isSome
  (current_termination_finisher (Context.snapshot ()))))
val _ = OK ()
val _ = convtest ("native definition enters EVAL", EVAL,
                 “native_fac 5”, “120”)

val _ = tprint "tactic flag changes control native support cleanup"
val support_before = length (thy_consts (current_theory ()))
val support_count = ref 0
fun keep_support_tac g =
  (Feedback.set_trace "Definition.delete support defs" 0;
   support_count := length (thy_consts (current_theory ()));
   WF_REL_TAC ‘$<’ g)
val _ = qDefine "native_keep_support_def"
  ‘native_keep_support n = if n = 0 then 0n
     else native_keep_support (native_keep_support (n - 1) MOD n)’
  (SOME keep_support_tac)
val _ = assert (!support_count > support_before + 1)
val _ = assert (length (thy_consts (current_theory ())) = !support_count)
val _ = assert (Feedback.current_trace "Definition.delete support defs" = 0)
val _ = Feedback.set_trace "Definition.delete support defs" 1
val saved_def_suffix = !Defn.def_suffix
val (_,direct_ind) = tDefine "native_changed_suffix"
  ‘native_changed_suffix n =
     if n = 0 then 0n else native_changed_suffix (n - 1) + 1’
  (capture THEN
   (fn g => (Defn.def_suffix := "_from_tactic"; WF_REL_TAC ‘$<’ g)))
val _ = assert (Option.isSome direct_ind)
val _ = assert (consumed (valOf (!pending)) TRUTH)
val _ = assert (Option.isSome
  (DB.lookup {Thy="-",Name="native_changed_suffix_from_tactic"}))
val _ = assert (!Defn.def_suffix = "_from_tactic")
val _ = Defn.def_suffix := saved_def_suffix
val _ = OK ()

val _ = tprint "explicit flags surround tactics and exit before attributes"
fun check_flags g =
  (assert (Feedback.current_trace "computeLib.auto_import_definitions" = 0);
   assert (Feedback.current_trace "Definition.allow_schema_definition" = 1);
   assert (Feedback.current_trace "Theory.allow_rebinds" = 1);
   assert (!Defn.def_suffix = "" andalso !Defn.ind_suffix = " flag_steps");
   WF_REL_TAC ‘$<’ g)
val _ = qDefine
  "flag_def[nocompute,schematic,allow_rebind,induction=flag_steps,finisher_test]"
  ‘flag_fun n = if n = 0 then y else flag_fun (n - 1) * 2’
  (SOME check_flags)
val _ = assert (Feedback.current_trace "computeLib.auto_import_definitions" = 1)
val _ = OK ()
val _ = convtest ("nocompute stays out of EVAL", EVAL,
                 “flag_fun y 2”, “flag_fun y 2”)

val _ = tprint "trivial definitions ignore explicit tactics"
val ignored_calls = ref 0
fun ignored_tac g = (ignored_calls := !ignored_calls + 1; ALL_TAC g)
val _ = qDefine "finisher_abbrev_def" ‘finisher_abbrev = 7n’
                (SOME ignored_tac)
val _ = qDefine "finisher_prim_def"
    ‘(finisher_prim 0 = 0n) /\
     (finisher_prim (SUC n) = SUC (finisher_prim n))’ (SOME ignored_tac)
val _ = assert (!ignored_calls = 0)
val _ = OK ()

val _ = tprint "invalid completion consumes finisher before registration"
fun invalid_completion g ctxt =
  let val finish = valOf (current_termination_finisher ctxt)
      val _ = assert (rejects (fn () => ignore (finish TRUTH)))
      val _ = assert (consumed finish TRUTH)
  in raise mk_HOL_ERR "selftest" "invalid_completion" "expected failure" end
val _ = assert (rejects (fn () => ignore
  (in_repl_mode (qDefine "bad_finisher_def"
    ‘bad_finisher n = if n = 0 then 0n else bad_finisher (n - 1) + 1’)
    (SOME invalid_completion))))
val _ = assert (not (Option.isSome
  (DB.lookup {Thy="-",Name="bad_finisher_def"})))
val _ = OK ()
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

val _ = if Systeml.ML_SYSNAME <> "poly" then () else let
  val hol = OS.Path.concat (Systeml.HOLDIR, "bin/hol")
  val heap = "staged-checkpoint.save"
  val markers = "staged-checkpoint.markers"
  fun remove f = OS.FileSys.remove f handle OS.SysErr _ => ()
  fun run args = OS.Process.isSuccess (Systeml.systeml (hol :: args))
  val _ = remove heap
  val _ = remove markers
  val _ = tprint "termination finisher saves a prefix in an isolated process"
  val _ = assert (run ["run", "--holstate=numheap", "tests/staged-save.sml"])
  val _ = assert (OS.FileSys.access (heap, []))
  val _ = OK ()
  val _ = tprint "a fresh process restores and completes without preparation"
  val _ = assert (run ["run", "--holstate=" ^ heap, "tests/staged-restore.sml"])
  val input = TextIO.openIn markers
  val contents = TextIO.inputAll input
  val _ = TextIO.closeIn input
  val _ = assert (contents = "prepared\nprefix\nfinished\n")
  val _ = remove heap
  val _ = remove markers
in OK () end
