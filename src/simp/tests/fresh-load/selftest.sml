(* Deliberately no static dependency on the simplifier or its splitter.
   The runtime checks cover the initial heap as well as launcher imports. *)
open HolKernel testutils

val _ = boolTheory.TRUTH
val _ = Theory.new_theory "fresh_load"

fun obs key value = print ("OBS " ^ key ^ "=" ^
  String.translate (fn #"\n" => "\\n" | c => str c) value ^ "\n")
fun check label ok =
  (tprint label; if ok then OK () else die label)
fun member s = List.exists (fn x => x = s)
fun env s =
  case OS.Process.getEnv s of
      SOME v => v
    | NONE => raise Fail ("missing environment variable " ^ s)
val scenario = env "SIMP_COMPAT_SCENARIO"
val _ = obs "scenario" scenario
val _ = check "fail-fast test mode" (!diemode = ProcessExit)
val _ = check "warnings enabled"
  (!Feedback.emit_WARNING andalso not (!Feedback.WARNINGs_as_ERRs))

fun registry stage =
  let
    val attr = ThmAttribute.is_attribute "split"
    val set = member "split" (ThmSetData.all_set_types ())
  in
    obs (stage ^ ".attribute") (Bool.toString attr);
    obs (stage ^ ".set") (Bool.toString set);
    (attr,set)
  end
val initial = registry "initial"
val _ = check "both initial registries unclaimed" (initial = (false,false))
val _ = List.app (fn name =>
  let
    val loaded = member name (Meta.loaded ())
    val bound = Option.isSome (#lookupStruct PolyML.globalNameSpace name)
  in
    obs ("initial.loaded." ^ name) (Bool.toString loaded);
    obs ("initial.bound." ^ name) (Bool.toString bound);
    check ("no preloaded " ^ name) (not loaded andalso not bound)
  end) ["simpLib", "splitLib", "splitPersistLib"]
val _ = obs "precondition" "clean"

(* Capture stage/frequency without suppressing the normal warning stream.
   A caught error permits post-failure ownership checks, but never passes. *)
fun observed stage f =
  let
    val old = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    val _ = Feedback.WARNING_outstream :=
      (fn s => (warnings := s :: !warnings; old s))
    val result = (SOME (f ()) handle e =>
      (obs (stage ^ ".exception")
         (General.exnName e ^ ": " ^ Feedback.exn_to_string e); NONE))
    val _ = Feedback.WARNING_outstream := old
    val _ = if Option.isSome result then obs (stage ^ ".exception") "none"
            else ()
    val _ = List.app (obs (stage ^ ".warning")) (rev (!warnings))
    val _ = obs (stage ^ ".warnings") (Int.toString (length (!warnings)))
  in
    (Option.isSome result, null (!warnings))
  end

val p = Term.mk_var ("fresh_foreign_p", Type.bool)
val foreign = Thm.ASSUME p
fun same_thm th =
  Term.aconv (Thm.concl th) p andalso
  (case Thm.hyp th of [h] => Term.aconv h p | _ => false)
val calls = ref ([] : string list)
fun attribute kind {name,attrname,args,thm} =
  (check (kind ^ " handler arguments")
     (name = "foreign" andalso attrname = "split" andalso
      args = ["identity"] andalso same_thm thm);
   calls := !calls @ [kind])
fun install_attribute () = ThmAttribute.register_attribute
  ("split", {localf=attribute "local", storedf=attribute "stored"})
fun attribute_identity () =
  let
    val _ = calls := []
    val arg = {name="foreign",attrname="split",args=["identity"],thm=foreign}
    val _ = ThmAttribute.local_attribute arg
    val _ = ThmAttribute.store_at_attribute arg
    val ok = !calls = ["local","stored"]
    val _ = obs "identity.attribute.calls" (String.concatWith "," (!calls))
  in check "custom attribute handler identity" ok end

val setcalls = ref ([] : string list)
val thy = Theory.current_theory ()
val knm = {Thy=thy,Name="foreign"}
fun add {thy=t,named_thm=(n,th)} =
  (check "foreign add arguments" (t = thy andalso n = knm andalso same_thm th);
   setcalls := !setcalls @ ["add"])
fun remove {thy=t,remove=n} =
  (check "foreign remove arguments" (t = thy andalso n = "foreign");
   setcalls := !setcalls @ ["remove"])
fun install_set () =
  let
    val _ = Theory.save_thm ("foreign",foreign)
    val {export,...} = ThmSetData.new_exporter
      {settype="split",efns={add=add,remove=remove}}
  in export "foreign" end
fun set_identity () =
  let
    val data = ThmSetData.current_data {settype="split"}
    val data_ok =
      case data of [ThmSetData.ADD (n,th)] => n = knm andalso same_thm th
                 | _ => false
    val _ = obs "identity.set.data" (Bool.toString data_ok)
    val _ = check "foreign set data identity" data_ok
    val _ = setcalls := []
    val efns = valOf (ThmSetData.data_exportfns {settype="split"})
    val _ = #add efns {thy=thy,named_thm=(knm,foreign)}
    val _ = #remove efns {thy=thy,remove="foreign"}
    val _ = obs "identity.set.calls" (String.concatWith "," (!setcalls))
  in check "foreign exporter handler identity" (!setcalls = ["add","remove"])
  end

fun dynamic_load () =
  let val path = env "SIMP_COMPAT_PATH"
  in obs "load.path" path; Meta.load path end
fun control () =
  (Meta.load (OS.Path.concat (OS.Path.dir (env "SIMP_COMPAT_PATH"),
                             "boolSimps"));
   Meta.qquse (env "SIMP_COMPAT_CONTROL"))
fun require_result label (succeeded,silent) =
  (check (label ^ " succeeds") succeeded;
   check (label ^ " without warnings") silent)

(* Native-only pointer inspection uses the new ownership accessors.
   Keep those APIs out of the shared legacy launcher's static closure. *)
fun native_identity stage =
  case OS.Process.getEnv "SIMP_COMPAT_IDENTITY_PREFIX" of
      NONE => ()
    | SOME prefix => Meta.qquse (prefix ^ stage ^ ".ML")

fun owner_first install identity =
  let
    val _ = require_result "custom registration" (observed "register" install)
    val _ = identity ()
    val _ = native_identity "before"
    val _ = registry "before-load"
    val result = observed "load" dynamic_load
    val _ = registry "after-load"
    (* Even a failed load must not corrupt the existing owner's state. *)
    val _ = identity ()
    val _ = require_result "dynamic simpLib load" result
    val _ = native_identity "after"
  in require_result "ordinary simplification" (observed "control" control) end

fun owner_after install identity =
  let
    val _ = require_result "dynamic simpLib load" (observed "load" dynamic_load)
    val free = registry "after-load"
    val _ = require_result "ordinary simplification" (observed "control" control)
    (* Attempt even if loading claimed ownership: retain collision warnings
       and error identities before asserting namespace neutrality. *)
    val result = observed "register" install
    val _ = registry "after-register"
    val _ = if #1 result then identity () else ()
    val _ = check "loading leaves both registries unclaimed"
      (free = (false,false))
  in require_result "custom registration" result end

val _ =
  case scenario of
      "attribute-first" => owner_first install_attribute attribute_identity
    | "set-first" => owner_first install_set set_identity
    | "attribute-after" => owner_after install_attribute attribute_identity
    | "set-after" => owner_after install_set set_identity
    | "syntax-first" =>
        (require_result "foreign syntax registration"
           (observed "register" (fn () =>
             List.app (fn name => Parse.temp_overload_on (name,boolSyntax.T))
               ["Split","ExcludeX"]));
         require_result "dynamic simpLib load" (observed "load" dynamic_load);
         require_result "foreign syntax preservation"
           (observed "syntax" (fn () => Meta.qquse
             (OS.Path.concat (OS.Path.dir (env "SIMP_COMPAT_CONTROL"),
                              "syntax.ML"))));
         check "syntax test never claims split registries"
           (registry "after-syntax" = (false,false)))
    | "control" =>
        (require_result "normal dynamic load" (observed "load" dynamic_load);
         ignore (registry "after-load");
         require_result "ordinary simplification" (observed "control" control))
    | _ => raise Fail ("unknown scenario " ^ scenario)
val _ = obs "result" "pass"
val _ = OS.Process.exit OS.Process.success
