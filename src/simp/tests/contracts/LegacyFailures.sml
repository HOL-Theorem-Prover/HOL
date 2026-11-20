(* Legacy-only assertions shared by the eleven isolated failure probes.
   No expected failures: each executable must succeed after the repairs. *)
structure LegacyFailures =
struct
open HolKernel Parse boolLib simpLib testutils

fun observe label value = print ("OBS " ^ label ^ "=" ^ value ^ "\n")
fun check label b =
  (tprint label; if b then OK () else die ("mismatch: " ^ label))

fun exception_observations label e =
  (observe (label ^ ".exception")
     (String.toString (Feedback.exn_to_string e));
   case e of
       HOL_ERR err =>
         (observe (label ^ ".exception.kind") "HOL_ERR";
          observe (label ^ ".exception.structure")
            (Feedback.top_structure_of err);
          observe (label ^ ".exception.function")
            (Feedback.top_function_of err);
          observe (label ^ ".exception.message")
            (String.toString (Feedback.message_of err)))
     | Bind => observe (label ^ ".exception.kind") "Bind"
     | _ => observe (label ^ ".exception.kind") "other")

datatype 'a outcome = Returned of 'a | Raised of exn

(* Forward warnings, record them in order, and restore the sink even if the
   operation throws. Unexpected exceptions are reported and re-raised. *)
fun during label f =
  let
    val warnings = ref ([] : string list)
    val sink = !Feedback.WARNING_outstream
    val _ = observe "stage" label
    val _ = Feedback.WARNING_outstream :=
      (fn s => (warnings := s :: !warnings; sink s))
    val outcome = Returned (f ()) handle e => Raised e
    val _ = Feedback.WARNING_outstream := sink
    val _ = observe (label ^ ".warning.count")
      (Int.toString (length (!warnings)))
    val _ = List.app
      (fn s => observe (label ^ ".warning") (String.toString s))
      (rev (!warnings))
  in
    case outcome of
        Raised e =>
          (exception_observations label e;
           observe (label ^ ".result") "exception";
           raise e)
      | Returned result =>
          (observe (label ^ ".exception") "none";
           check (label ^ " is silent") (null (!warnings));
           result)
  end

val input = ``T /\ (compat_p:bool)``
val simplified = ``compat_p:bool``

fun theorem label th =
  (observe (label ^ ".conclusion") (term_to_string (concl th));
   observe (label ^ ".hypotheses")
     (String.concatWith ";" (map term_to_string (hyp th))))

fun result_is th expected =
  aconv (concl th) (mk_eq (input, expected)) andalso null (hyp th)

fun start name =
  let
    val _ = observe "probe" name
    val _ = new_theory "legacyfailure"
    val _ = check "setup: warnings enabled, not promoted to errors"
      (!Feedback.emit_WARNING andalso not (!Feedback.WARNINGs_as_ERRs))
    val _ = check "setup: fail-fast testutils" (!diemode = ProcessExit)
    val control = during "setup.control" (fn () =>
      SIMP_CONV boolSimps.bool_ss [] input)
    val _ = theorem "setup.control" control
  in
    check "setup: ordinary simplification works"
      (result_is control simplified)
  end

fun finish () =
  (observe "assertion.result" "pass";
   OS.Process.exit OS.Process.success)

fun constructor () =
  let
    val _ = start "reducer-shape"
    val data = during "setup.projection"
      (fn () => simpLib.traversedata_for_ss simpLib.empty_ss)
    val _ = check "setup: public projection has a first rewriter"
      (not (null (#rewriters data)))
    val _ = observe "setup.result" "ready"
    val _ = during "assertion.constructor" (fn () =>
      (* Exhaustive assertion avoids a fixture compiler warning when the
         datatype has additional constructors. Only REDUCER may pass. *)
      case #rewriters (simpLib.traversedata_for_ss simpLib.empty_ss) of
          Traverse.REDUCER _ :: _ =>
            observe "assertion.constructor.result" "REDUCER"
        | _ => die "public legacy projection is not REDUCER")
  in
    finish ()
  end

(* Literal prefixed rewrites and dprocs use the same deletion route as
   conversions. A longer overlapping name must survive exact deletion. *)
fun prefix_stores name installed = let
  val other = ``F \/ (compat_q:bool)``
  val other_rhs = ``compat_q:bool``
  val and_rule = CONJUNCT1 (SPEC_ALL boolTheory.AND_CLAUSES)
  val or_rule = List.nth (CONJUNCTS (SPEC_ALL boolTheory.OR_CLAUSES),2)
  val dummy = "prefix store replay dummy"
  fun store kind = let
    val calls = ref ([] : string list)
    fun entry (n,th) =
      if kind = "rewrite" then
        rewrites_with_names [({Thy="bool",Name=n},th)]
      else dproc_ss (Traverse.REDUCER
        {name=SOME n,initial=Fail "prefix context",
         addcontext=fn (ctxt,_) => ctxt,
         apply=fn _ => fn tm =>
           (calls := (n ^ ":" ^ term_to_string tm) :: !calls;
            REWR_CONV th tm)})
    val base = empty_ss ++ name_ss dummy empty_ssfrag ++
               entry (name ^ "_tail",or_rule)
    val ss = if installed then base ++ entry (name,and_rule) else base
    fun results label set expected = let
      val _ = calls := []
      val (a,b) = during (kind ^ "." ^ label) (fn () =>
        (QCONV (SIMP_CONV set []) input,
         QCONV (SIMP_CONV set []) other))
      val _ = theorem (kind ^ "." ^ label ^ ".target") a
      val _ = theorem (kind ^ "." ^ label ^ ".overlap") b
      val _ = observe (kind ^ "." ^ label ^ ".callbacks")
        (String.concatWith ";" (rev (!calls)))
    in
      check (kind ^ " " ^ label ^ " deletes only the literal target")
        (result_is a expected andalso
         aconv (concl b) (mk_eq (other,other_rhs)) andalso null (hyp b)
         andalso (label = "before" orelse
           not (List.exists (String.isPrefix (name ^ ":")) (!calls))))
    end
    val _ = results "before" ss (if installed then simplified else input)
    val literal = during (kind ^ ".Excl") (fn () => ss && [Excl name])
    val operator = during (kind ^ ".operator") (fn () => ss -* [name])
  in
    results "Excl" literal input;
    results "operator" operator input;
    results "Excl.replay" (remove_ssfrags [dummy] literal) input;
    results "operator.replay" (remove_ssfrags [dummy] operator) input
  end
in List.app store ["rewrite","dproc"] end

(* Also run by the normal exclusion-contracts target, without exiting or
   resetting the theory between cases. Keep the original fixture checks. *)
fun prefix_checks {prefix, installed} =
  let
    val name = prefix ^ (if installed then "compat_probe"
                          else "compat_missing")
    val _ = observe "literal.name" name
    val calls = ref ([] : term list)
    fun callbacks label =
      observe (label ^ ".callbacks")
        (String.concatWith ";" (map term_to_string (rev (!calls))))
    val _ = check "setup: empty_ss has no installed fragments"
      (null (ssfrags_of empty_ss))
    val bare = during "setup.empty" (fn () =>
      QCONV (SIMP_CONV empty_ss []) input)
    val _ = theorem "setup.empty" bare
    val _ = check "setup: empty_ss leaves the test term unchanged"
      (result_is bare input)
    val ss = during "setup.install" (fn () =>
      if installed then
        empty_ss ++ std_conv_ss
          {name = name, pats = [input], conv = fn tm =>
             (calls := tm :: !calls;
              REWR_CONV (CONJUNCT1 (SPEC_ALL boolTheory.AND_CLAUSES)) tm)}
      else empty_ss)
    val before_excl = during "setup.before" (fn () =>
      QCONV (SIMP_CONV ss []) input)
    val _ = theorem "setup.before" before_excl
    val _ = callbacks "setup.before"
    val _ = check "setup: literal conversion is active iff installed"
      (if installed then
         result_is before_excl simplified andalso not (null (!calls))
       else result_is before_excl input andalso null (!calls))
    val directive = during "setup.directive" (fn () => Excl name)
    val _ = calls := []
    val _ = observe "setup.result" "ready"
    val excluded = during "assertion.exclude" (fn () => ss && [directive])
    val after_excl = during "assertion.apply" (fn () =>
      QCONV (SIMP_CONV excluded []) input)
    val _ = theorem "assertion.apply" after_excl
    val _ = callbacks "assertion.apply"
    val _ = check "legacy Excl leaves no active literal conversion"
      (result_is after_excl input andalso null (!calls))
    val direct = during "assertion.direct" (fn () => ss -* [name])
    val direct_th = during "assertion.direct.apply" (fn () =>
      QCONV (SIMP_CONV direct []) input)
  in
    check "literal Excl agrees with -*, including no conversion callbacks"
      (aconv (concl after_excl) (concl direct_th) andalso
       HOLset.equal (hypset after_excl,hypset direct_th) andalso
       null (!calls));
    prefix_stores name installed
  end

fun prefix (args as {prefix, installed}) =
  (start (prefix ^ (if installed then "installed" else "unmatched"));
   prefix_checks args;
   finish ())
end
