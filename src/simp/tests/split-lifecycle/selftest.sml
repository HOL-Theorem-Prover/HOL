(* Only this launcher is linked: all simplifier imports happen at runtime. *)
open HolKernel testutils

(* Whether a split attribute is registered; verify_owner checks which
   handler answers by dispatching to it *)
fun split_attribute_now () = ThmAttribute.is_attribute "split"

fun check label ok = (tprint label; if ok then OK () else die label)
fun env name = valOf (OS.Process.getEnv name)
fun loaded name = List.exists (equal name) (Meta.loaded ()) orelse
  Option.isSome (#lookupStruct PolyML.globalNameSpace name)
fun absent names = List.app (fn name =>
  check ("not loaded: " ^ name) (not (loaded name))) names
val extensions =
  ["TraverseExt","Cond_rewrExt",
   "simpExtLib","congExtLib","splitLib","SplitData","splitPersistLib"]
val mode = env "SPLIT_LIFECYCLE_MODE"
val _ = print ("OBS mode=" ^ mode ^ "\n")
val _ = boolTheory.TRUTH
val _ = Theory.new_theory "split_lifecycle"
val _ = absent ("simpLib" :: "congLib" :: extensions @
  ["splitParentTheory","splitChildTheory","splitDescendantTheory"])
fun hooks () = Listener.listeners Theory.delta_hook
val private_name = "splitLib.persistence.onload"
fun no_private () = not (List.exists (fn (n,_) => n = private_name) (hooks ()))
val _ = check "fresh entry has no private listener" (no_private ())
val _ = check "fresh entry has no split registries"
  (not (ThmAttribute.is_attribute "split") andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())))
fun files prefix = List.app (fn (file,dir) =>
  print (prefix ^ OS.Path.concat (dir,file) ^ "\n"))
  (Binarymap.listItems (Meta.fileDirMap ()))
val _ = files "OBS heapfile="
fun traced_use path =
  let val path = OS.Path.mkAbsolute
        {path=holpathdb.subst_pathvars path,relativeTo=OS.FileSys.getDir ()}
  in print ("OBS used.path=" ^ path ^ "\n"); Meta.qquse path end
fun load name =
  let val path = OS.Path.concat (env "SPLIT_LIFECYCLE_SRC",name)
  in print ("OBS load.path=" ^ path ^ "\n"); Meta.loadPlan traced_use path end
fun use name = traced_use name
fun same_option (NONE,NONE) = true
  | same_option (SOME a,SOME b) = Portable.pointer_eq (a,b)
  | same_option _ = false
fun same_hooks xs ys = ListPair.allEq
  (fn ((n,f),(m,g)) => n = m andalso Portable.pointer_eq (f,g)) (xs,ys)
fun retained old = check "listener identities and relative order retained"
  (same_hooks old (List.filter (fn (n,_) =>
    List.exists (fn (m,_) => n = m) old) (hooks ())))
val warnings = ref ([] : string list)
val old_warning = !Feedback.WARNING_outstream
val _ = Feedback.WARNING_outstream :=
  (fn s => (warnings := s :: !warnings; old_warning s))

(* Fresh exported-theory and restored-heap checks are independent processes.
   No opt-in or splitter is loaded before the import. *)
val _ = if mode = "export-save" then
  (Meta.loadPlan traced_use (env "SPLIT_LIFECYCLE_THEORY");
   check "export import initializes without loading simplifier"
     (loaded "splitPersistLib" andalso not (loaded "simpLib"));
   load "boolSimps"; load "simpExtLib"; use "persistent.ML";
   files "OBS loaded.path=";
   PolyML.SaveState.saveState "split-proof.state";
   print "OBS heap=saved\nOBS result=pass\n";
   OS.Process.exit OS.Process.success)
  else if mode = "export-reload" then
  (PolyML.SaveState.loadState "split-proof.state";
   use "persistent.ML";
   files "OBS loaded.path=";
   print "OBS heap=reloaded\nOBS result=pass\n";
   OS.Process.exit OS.Process.success)
  else ()

val owner = env "SPLIT_LIFECYCLE_OWNER"
val timing = env "SPLIT_LIFECYCLE_TIMING"
val order = env "SPLIT_LIFECYCLE_ORDER"
val _ = print ("OBS case=" ^ order ^ "/" ^ owner ^ "/" ^ timing ^ "\n")
val calls = ref ([] : string list)
val handlers = {localf=fn _ => calls := !calls @ ["local"],
                storedf=fn _ => calls := !calls @ ["stored"]}
val exporters = {add=fn _ => calls := !calls @ ["add"],
                 remove=fn _ => calls := !calls @ ["remove"]}
fun quiet label f =
  let val previous = !calls
      val result = f ()
      val _ = check (label ^ ": no foreign callbacks") (!calls = previous)
  in result end
fun install () =
  (case owner of
       "attribute" => ThmAttribute.register_attribute ("split",handlers)
     | "set" =>
         let val _ = Theory.save_thm ("foreign",boolTheory.TRUTH)
             val {export,...} = ThmSetData.new_exporter
               {settype="split",efns=exporters}
         in export "foreign" end
     | "syntax" => List.app (fn name =>
         Parse.temp_overload_on (name,boolSyntax.T)) ["Split","ExcludeX"]
     | "none" => ()
     | _ => raise Fail "unknown owner";
   calls := [])
fun verify_owner () =
  let
    val _ = calls := []
    val arg = {name="foreign",attrname="split",args=[],thm=boolTheory.TRUTH}
  in
    case owner of
        "attribute" =>
          (ThmAttribute.local_attribute arg;
           ThmAttribute.store_at_attribute arg;
           check "foreign attribute callbacks" (!calls = ["local","stored"]))
      | "set" =>
          (check "foreign exporter exact record"
             (Portable.pointer_eq (exporters,
                valOf (ThmSetData.data_exportfns {settype="split"})));
           check "foreign set theorem and data unchanged"
             (case ThmSetData.current_data {settype="split"} of
                  [ThmSetData.ADD ({Thy,Name},th)] =>
                    Thy = Theory.current_theory () andalso Name = "foreign"
                    andalso Portable.pointer_eq (th,DB.fetch Thy Name)
                | _ => false);
           #add exporters {thy=Theory.current_theory (),
             named_thm=({Thy="bool",Name="TRUTH"},boolTheory.TRUTH)};
           #remove exporters {thy=Theory.current_theory (),remove="foreign"};
           check "foreign exporter callbacks" (!calls = ["add","remove"]))
      | "syntax" => List.app (fn name =>
          check ("foreign syntax unchanged: " ^ name)
            (aconv (Parse.Term [QUOTE name]) boolSyntax.T))
          ["Split","ExcludeX"]
      | _ => ()
  end
fun at stage = if timing = stage then (install (); verify_owner ()) else ()
val _ = at "before"
val entry_attribute = split_attribute_now ()
val entry_exporter = ThmSetData.data_exportfns {settype="split"}
val initial_hooks = hooks ()
val _ = List.app (fn name =>
  (quiet name (fn () => load name); absent extensions;
   check "ordinary load creates no private listener" (no_private ())))
  (if order = "simp" then ["simpLib","congLib"] else ["congLib","simpLib"])
val _ = retained initial_hooks
(* congLib also imports unchanged computeLib, unlike the simp-only fixture. *)
val legacy_listeners =
  ["ThmSetData.onload.computeLib.delta.parents",
   "ThmSetData.onload.computeLib.delta.deltas",
   "ThmSetData.onload.compute",
   "markerLib.no_suspended_in_DB",
   "ThmSetData.onload.suspension.resumptions.parents",
   "ThmSetData.onload.suspension.resumptions.deltas",
   "ThmSetData.onload.suspension.theorems.parents",
   "ThmSetData.onload.suspension.theorems.deltas"]
val _ = print ("OBS listeners=" ^ String.concatWith "," (map #1 (hooks ())) ^
  "\n")
val _ = check "ordinary load adds only exact legacy listener names"
  (map #1 (List.filter (fn (n,_) =>
     not (List.exists (fn (m,_) => n = m) initial_hooks)) (hooks ())) =
   List.filter (fn n => not (List.exists (fn (m,_) => n = m) initial_hooks))
     legacy_listeners)
val _ = check "ordinary load preserves both registry records"
  (entry_attribute = split_attribute_now () andalso
   same_option (entry_exporter,ThmSetData.data_exportfns {settype="split"}))
val _ = if timing = "before" then verify_owner () else ()
val _ = quiet "boolSimps" (fn () => load "boolSimps")
val _ = quiet "ordinary proof" (fn () => use "ordinary.ML")
val _ = at "middle"
val extension_hooks = hooks ()
val attribute_before = split_attribute_now ()
val exporter_before = ThmSetData.data_exportfns {settype="split"}
val _ = List.app (fn name => quiet name (fn () => load name))
  (if order = "simp" then ["simpExtLib","congExtLib"]
   else ["congExtLib","simpExtLib"])
val _ = check "extension loads preserve exact listeners"
  (same_hooks extension_hooks (hooks ()))
val _ = check "extension loads preserve registry records"
  (attribute_before = split_attribute_now () andalso
   same_option (exporter_before,ThmSetData.data_exportfns {settype="split"}))
val _ = check "extension loads never opt into persistence"
  (not (loaded "splitPersistLib") andalso no_private ())
val _ = List.app (fn name => check ("explicitly reachable: " ^ name)
  (loaded name)) ["splitLib","SplitData","congExtLib"]
val _ = if timing <> "after" then verify_owner () else ()
val _ = at "after"
val _ = quiet "extension use and initialization" (fn () => use "extension.ML")
val _ = verify_owner ()
val _ = quiet "ordinary proof after extension" (fn () => use "ordinary.ML")
val _ = files "OBS loaded.path="
val _ = check "all loads and callbacks emit no warnings" (null (!warnings))
val _ = Feedback.WARNING_outstream := old_warning
val _ = print "OBS result=pass\n"
val _ = OS.Process.exit OS.Process.success
