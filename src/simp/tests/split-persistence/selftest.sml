(* Link only the launcher: each scenario starts with an unclaimed namespace
   and no splitter, opt-in module, or fixture theory loaded. *)
open HolKernel testutils

(* Whether a split attribute is registered; the foreign scenarios check
   which handler answers by dispatching to it *)
fun split_attribute_now () = ThmAttribute.is_attribute "split"

fun check label ok = (tprint label; if ok then OK () else die label)
fun env name = valOf (OS.Process.getEnv name)
fun loaded name = List.exists (equal name) (Meta.loaded ()) orelse
  Option.isSome (#lookupStruct PolyML.globalNameSpace name)
fun fixture name = OS.Path.concat (OS.FileSys.getDir (), name)
val scenario = env "SPLIT_PERSIST_SCENARIO"
val _ = print ("OBS scenario=" ^ scenario ^ "\n")
val _ = boolTheory.TRUTH
val _ = Theory.new_theory "split_import_test"
val initial_context = Context.snapshot ()
val _ = check "clean registries in fresh executable"
  (not (ThmAttribute.is_attribute "split") andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())))
val _ = List.app (fn name => check ("not preloaded: " ^ name)
  (not (loaded name)))
  ["splitLib", "simpLib", "splitPersistLib", "splitParentTheory",
   "splitChildTheory", "splitDescendantTheory"]

(* A new launcher process loads the saved heap, not a second import in
   the exporting process. The verifier runs in the restored namespace. *)
val _ = if scenario = "heap-reload" then
  (PolyML.SaveState.loadState (fixture "split-lifecycle.state");
   Meta.qquse "heapVerify.ML";
   OS.Process.exit OS.Process.success)
  else ()

val warnings = ref ([] : string list)
val old_warning = !Feedback.WARNING_outstream
val _ = Feedback.WARNING_outstream :=
  (fn s => (warnings := s :: !warnings; old_warning s))
val calls = ref ([] : string list)
val handlers = {localf=fn _ => calls := "local" :: !calls,
                storedf=fn _ => calls := "stored" :: !calls}
val exporter = {add=fn _ => calls := "add" :: !calls,
                remove=fn _ => calls := "remove" :: !calls}
val _ = if scenario = "foreign-attribute" then
          ThmAttribute.register_attribute ("split", handlers)
        else if scenario = "foreign-set" then
          let
            val _ = Theory.save_thm ("foreign",boolTheory.TRUTH)
            val {export,...} = ThmSetData.new_exporter
              {settype="split",efns=exporter}
            val _ = export "foreign"
          in calls := [] end
        else ()
val _ = if scenario = "owned" then
          (Meta.load "splitLib"; Meta.qquse "optIn.ML")
        else ()
val before_attribute = split_attribute_now ()
val before_exporter = ThmSetData.data_exportfns {settype="split"}
val target = case scenario of "parent" => "splitParentTheory"
                           | "child" => "splitChildTheory"
                           | _ => "splitDescendantTheory"
val failure =
  (Meta.load (fixture target); NONE)
  handle e => (print ("OBS import.exception=" ^
                        Feedback.exn_to_string e ^ "\n"); SOME e)
val foreign = String.isPrefix "foreign-" scenario
val _ = check "fresh import has expected success/failure"
  (Option.isSome failure = foreign)
val _ = if not foreign then () else
  check "import rejected at explicit registration, not decoding/replay"
    (case failure of
         SOME (HOL_ERR e) =>
           Feedback.top_structure_of e = "splitLib" andalso
           Feedback.top_function_of e = "enable_split_attribute" andalso
           Feedback.message_of e = "settype or attribute split already exists"
       | _ => false)
val _ = check "import never replaces handlers or emits warnings"
  (null (!warnings))
val _ = if scenario <> "owned" then () else
  check "exported initializer keeps the enabled registration"
    (before_attribute andalso split_attribute_now () andalso
     not (Option.isSome (ThmSetData.data_exportfns {settype="split"})))

val _ = if not foreign then
          (check "persistent import does not load simpLib"
             (not (loaded "simpLib"));
           Meta.load "boolSimps"; Meta.load "simpExtLib";
           Meta.qquse "verify.ML")
        else
          let
            val _ = check "failed import did not finish parent theory"
              (not (loaded "splitParentTheory"))
            val _ = check "failed import did not call foreign handlers"
              (null (!calls))
            val arg = {name="foreign",attrname="split",args=[],
                       thm=boolTheory.TRUTH}
          in
            if scenario = "foreign-attribute" then
              (check "no partial exporter registration"
                 (not (List.exists (equal "split")
                         (ThmSetData.all_set_types ())));
               ThmAttribute.local_attribute arg;
               ThmAttribute.store_at_attribute arg;
               check "foreign attribute callbacks still work"
                 (!calls = ["stored","local"]))
            else
              (check "foreign exporter identity preserved"
                 (Portable.pointer_eq (exporter,
                    valOf (ThmSetData.data_exportfns {settype="split"})));
               check "foreign set attribute preserved"
                 (before_attribute andalso split_attribute_now ());
               check "foreign set data untouched"
                 (case ThmSetData.current_data {settype="split"} of
                      [ThmSetData.ADD ({Thy,Name},th)] =>
                        Thy = "split_import_test" andalso Name = "foreign"
                        andalso Portable.pointer_eq
                          (th,DB.fetch "split_import_test" "foreign")
                    | _ => false);
               #add exporter {thy=Theory.current_theory (),
                              named_thm=({Thy="bool",Name="TRUTH"},
                                         boolTheory.TRUTH)};
               #remove exporter {thy=Theory.current_theory (),remove="x"};
               check "foreign exporter callbacks still work"
                 (!calls = ["remove","add"]))
          end
val _ = Feedback.WARNING_outstream := old_warning
val _ = if scenario = "heap-save" then Meta.qquse "heapSave.ML" else ()
val _ = print "OBS result=pass\n"
val _ = OS.Process.exit OS.Process.success
