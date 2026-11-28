(* The launcher must have NO static simplifier dependency. *)
open HolKernel testutils

(* Whether a split attribute is registered; verify_owner checks which
   handler answers by dispatching to it *)
fun split_attribute_now () = ThmAttribute.is_attribute "split"

fun check label ok = (tprint label; if ok then OK () else die label)
fun env name = valOf (OS.Process.getEnv name)
fun member x = List.exists (equal x)
fun loaded name = member name (Meta.loaded ()) orelse
  Option.isSome (#lookupStruct PolyML.globalNameSpace name)
fun forbidden name = String.isSuffix "Ext" name orelse
  String.isSuffix "ExtLib" name orelse
  member name ["SplitData","splitLib","splitPersistLib"]
val forbidden_names =
  ["TraverseExt","Cond_rewrExt",
   "simpExtLib","congExtLib","SplitData","splitLib","splitPersistLib"]
val used = ref ([] : string list)
fun files stage = List.app (fn (file,dir) =>
  print ("OBS " ^ stage ^ ".loaded.path=" ^ OS.Path.concat (dir,file) ^ "\n"))
  (Binarymap.listItems (Meta.fileDirMap ()))
fun ordinary_only stage =
  (files stage;
   check (stage ^ ": no forbidden loaded module")
     (not (List.exists forbidden (Meta.loaded ())));
   check (stage ^ ": no forbidden source path")
     (not (List.exists (forbidden o OS.Path.base o OS.Path.file) (!used))
      andalso not (List.exists (fn (file,_) =>
        forbidden (OS.Path.base file))
        (Binarymap.listItems (Meta.fileDirMap ()))));
   List.app (fn name => check (stage ^ ": absent " ^ name)
     (not (loaded name))) forbidden_names)
fun traced_use path = let
  val absolute = OS.Path.mkAbsolute
    {path=holpathdb.subst_pathvars path,relativeTo=OS.FileSys.getDir ()}
in
  used := absolute :: !used;
  print ("OBS used.path=" ^ absolute ^ "\n"); Meta.qquse absolute
end
fun load name = let val path = OS.Path.concat (env "API_AUDIT_SRC",name)
  in print ("OBS requested.path=" ^ path ^ "\n");
     Meta.loadPlan traced_use path end
fun hooks () = Listener.listeners Theory.delta_hook
fun same_hooks xs ys = ListPair.allEq
  (fn ((n,f),(m,g)) => n = m andalso Portable.pointer_eq (f,g)) (xs,ys)
fun same_option (NONE,NONE) = true
  | same_option (SOME a,SOME b) = Portable.pointer_eq (a,b)
  | same_option _ = false
fun no_private () = not (member "splitLib.persistence.onload"
  (map #1 (hooks ())))
val _ = check "fail-fast testutils" (!diemode = ProcessExit)
val _ = boolTheory.TRUTH
val _ = Theory.new_theory "api_audit"
val _ = ordinary_only "entry"
val _ = check "fresh launcher has neither ordinary library"
  (not (loaded "simpLib") andalso not (loaded "congLib"))
val _ = check "fresh launcher has no split owners or listener"
  (not (ThmAttribute.is_attribute "split") andalso no_private () andalso
   not (member "split" (ThmSetData.all_set_types ())))
val calls = ref ([] : string list)
val handlers = {localf=fn _ => calls := !calls @ ["local"],
                storedf=fn _ => calls := !calls @ ["stored"]}
val exporters = {add=fn _ => calls := !calls @ ["add"],
                 remove=fn _ => calls := !calls @ ["remove"]}
val kind = env "API_AUDIT_KIND"
val owned_attribute = ref (split_attribute_now ())
val owned_exporter = ref (ThmSetData.data_exportfns {settype="split"})
fun install () =
  ((case kind of
      "attribute" => ThmAttribute.register_attribute ("split",handlers)
    | "exporter" =>
        let val _ = Theory.save_thm ("foreign",boolTheory.TRUTH)
            val {export,...} = ThmSetData.new_exporter
              {settype="split",efns=exporters}
        in export "foreign" end
    | _ => raise Fail "unknown foreign owner");
   owned_attribute := split_attribute_now ();
   owned_exporter := ThmSetData.data_exportfns {settype="split"};
   calls := [])
fun verify_owner () = let
  val _ = check "foreign attribute presence (or absence)"
    (!owned_attribute = split_attribute_now ())
  val _ = check "foreign exporter exact record (or absence)"
    (same_option (!owned_exporter,
       ThmSetData.data_exportfns {settype="split"}))
  val _ = calls := []
  val expected = if kind = "attribute" then let
      val arg = {name="foreign",attrname="split",args=[],
                 thm=boolTheory.TRUTH}
      val _ = ThmAttribute.local_attribute arg
      val _ = ThmAttribute.store_at_attribute arg
    in ["local","stored"] end
    else let
      val efns = valOf (ThmSetData.data_exportfns {settype="split"})
      val _ = check "original exporter record identity"
        (Portable.pointer_eq (exporters,efns))
      val _ = check "foreign exporter data unchanged"
        (case ThmSetData.current_data {settype="split"} of
           [ThmSetData.ADD ({Thy,Name},th)] =>
             Thy = Theory.current_theory () andalso Name = "foreign" andalso
             Portable.pointer_eq (th,DB.fetch Thy Name)
         | _ => false)
      val _ = #add efns {thy=Theory.current_theory (),
        named_thm=({Thy="bool",Name="TRUTH"},boolTheory.TRUTH)}
      val _ = #remove efns {thy=Theory.current_theory (),remove="foreign"}
    in ["add","remove"] end
in check "original foreign callbacks remain callable" (!calls = expected);
   calls := [] end
fun quiet label f = let val before_calls = !calls
  val result = f ()
  val _ = check (label ^ ": no initialization callbacks")
    (!calls = before_calls)
in result end
val order = env "API_AUDIT_ORDER"
val timing = env "API_AUDIT_OWNER"
val _ = print ("OBS case=" ^ order ^ "/" ^ kind ^ "/" ^ timing ^ "\n")
val _ = if timing = "before" then (install (); verify_owner ()) else ()
val attribute = split_attribute_now ()
val exporter = ThmSetData.data_exportfns {settype="split"}
val initial_hooks = hooks ()
val warnings = ref ([] : string list)
val old_warning = !Feedback.WARNING_outstream
val _ = Feedback.WARNING_outstream :=
  (fn s => (warnings := s :: !warnings; old_warning s))
val _ = List.app (fn name =>
  (quiet name (fn () => load name); ordinary_only name;
   check "ordinary import creates no private listener" (no_private ())))
  (if order = "simp-first" then ["simpLib","congLib"]
   else ["congLib","simpLib"])
val legacy_listeners =
  ["ThmSetData.onload.computeLib.delta.parents",
   "ThmSetData.onload.computeLib.delta.deltas",
   "ThmSetData.onload.compute",
   "markerLib.no_suspended_in_DB",
   "ThmSetData.onload.suspension.resumptions.parents",
   "ThmSetData.onload.suspension.resumptions.deltas",
   "ThmSetData.onload.suspension.theorems.parents",
   "ThmSetData.onload.suspension.theorems.deltas"]
val _ = check "ordinary imports retain exact prior listeners and order"
  (same_hooks initial_hooks (List.filter (fn (n,_) =>
    member n (map #1 initial_hooks)) (hooks ())))
val _ = check "only unchanged ordinary listener additions"
  (map #1 (List.filter (fn (n,_) =>
     not (member n (map #1 initial_hooks))) (hooks ())) =
   List.filter (fn n => not (member n (map #1 initial_hooks)))
     legacy_listeners)
val _ = check "ordinary imports preserve exact registry records"
  (attribute = split_attribute_now () andalso
   same_option (exporter,ThmSetData.data_exportfns {settype="split"}))
val _ = if timing = "after" then install () else ()
val _ = verify_owner ()
val _ = quiet "boolSimps" (fn () => load "boolSimps")
val _ = ordinary_only "ordinary-recipes"
val _ = quiet "ordinary proof and original identities"
  (fn () => traced_use "ordinary.ML")
val extension_hooks = hooks ()
val extension_attributes = ThmAttribute.all_attributes ()
val extension_set_types = ThmSetData.all_set_types ()
val _ = List.app (fn name => quiet name (fn () => load name))
  (if order = "simp-first" then ["simpExtLib","congExtLib"]
   else ["congExtLib","simpExtLib"])
val _ = check "explicit extension imports preserve exact listeners"
  (same_hooks extension_hooks (hooks ()))
val _ = check "extension imports create no attribute or exporter slots"
  (extension_attributes = ThmAttribute.all_attributes () andalso
   extension_set_types = ThmSetData.all_set_types ())
val _ = verify_owner ()
val _ = quiet "compiled documentation import"
  (fn () => Meta.loadPlan traced_use
    (OS.Path.concat (OS.FileSys.getDir (),"Documentation")))
val _ = quiet "explicit extension controls and proofs"
  (fn () => traced_use "runtime.ML")
val _ = verify_owner ()
val _ = check "use leaves exact Theory listeners unchanged"
  (same_hooks extension_hooks (hooks ()))
val _ = check "use leaves attribute and exporter registries unchanged"
  (extension_attributes = ThmAttribute.all_attributes () andalso
   extension_set_types = ThmSetData.all_set_types ())
val _ = check "never imports persistence"
  (no_private () andalso not (loaded "splitPersistLib"))
val _ = files "final"
val _ = check "all imports and proofs warning-free" (null (!warnings))
val _ = Feedback.WARNING_outstream := old_warning
val _ = print "OBS result=pass\n"
val _ = OS.Process.exit OS.Process.success
