(* Ordinary loading must not pull in the extension modules, and loading
   the Split and ExcludeX markers' theory must preserve the foreign
   overloads installed before simpLib. *)
val _ = List.app (fn name =>
  if List.exists (fn s => s = name) (Meta.loaded ()) orelse
     Option.isSome (#lookupStruct PolyML.globalNameSpace name)
  then raise Fail ("ordinary load imported extension module " ^ name)
  else ())
  ["TraverseExt","Cond_rewrExt","simpExtLib","congExtLib",
   "splitLib","SplitData","splitPersistLib"];
val _ = List.app (fn name =>
  (testutils.tprint ("ordinary load preserves foreign syntax: " ^ name);
   if Term.aconv (Parse.Term [QUOTE name]) boolSyntax.T
   then testutils.OK () else testutils.die "foreign overload changed"))
  ["Split","ExcludeX"];
val _ = List.app (fn name =>
  (testutils.tprint ("qualified marker constant remains available: " ^ name);
   if Term.same_const
        (Parse.Term [QUOTE ("marker$" ^ name)])
        (Term.prim_mk_const {Thy="marker",Name=name})
   then testutils.OK () else testutils.die "qualified marker unavailable"))
  ["Split","ExcludeX"];
