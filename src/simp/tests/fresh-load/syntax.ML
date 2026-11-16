(* Ordinary loading must not pull in extension syntax/theories. Explicitly
   load the marker service before the existing qualified-constant checks;
   it too must preserve the foreign overloads installed before simpLib. *)
val _ = List.app (fn name =>
  if List.exists (fn s => s = name) (Meta.loaded ()) orelse
     Option.isSome (#lookupStruct PolyML.globalNameSpace name)
  then raise Fail ("ordinary load imported extension module " ^ name)
  else ())
  ["TraverseExt","Cond_rewrExt",
   "simpExtLib","congExtLib","simpMarkerTheory","simpMarkerLib",
   "splitLib","SplitData","splitPersistLib"];
val _ = Meta.load
  (OS.Path.concat (OS.Path.dir (valOf (OS.Process.getEnv "SIMP_COMPAT_PATH")),
                   "simpMarkerLib"));
val _ = List.app (fn name =>
  (testutils.tprint ("ordinary load preserves foreign syntax: " ^ name);
   if Term.aconv (Parse.Term [QUOTE name]) boolSyntax.T
   then testutils.OK () else testutils.die "foreign overload changed"))
  ["Split","ExcludeX"];
val _ = List.app (fn name =>
  (testutils.tprint ("qualified marker constant remains available: " ^ name);
   if Term.same_const
        (Parse.Term [QUOTE ("simpMarker$" ^ name)])
        (Term.prim_mk_const {Thy="simpMarker",Name=name})
   then testutils.OK () else testutils.die "qualified marker unavailable"))
  ["Split","ExcludeX"];
