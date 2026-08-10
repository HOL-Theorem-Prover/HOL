structure Refute_Skolem = struct
  type dependency =
    {origin : int,
     source_type : Type.hol_type}

  type info =
    {origin : int option,
     generated_name : string,
     source_name : string,
     source_type : Type.hol_type,
     dependencies : dependency list,
     arity : int,
     stage : string}

  (* Canonical replay identity is the descent index in the quantifier prefix
     of the normalized, prenexed goal.  Capture-renaming can prevent a later
     name-based lookup from finding this binder; callers must then record
     NONE rather than guess. *)
  fun prefix_binders term =
    if boolSyntax.is_forall term then
      let val (variable, body) = boolSyntax.dest_forall term
      in Term.dest_var variable :: prefix_binders body end
    else if boolSyntax.is_exists term then
      let val (variable, body) = boolSyntax.dest_exists term
      in Term.dest_var variable :: prefix_binders body end
    else
      []

  fun map_types copy_type
        ({origin, generated_name, source_name, source_type, dependencies,
          arity, stage} : info) : info =
    {origin = origin,
     generated_name = generated_name,
     source_name = source_name,
     source_type = copy_type source_type,
     dependencies = map (fn ({origin, source_type} : dependency) =>
       {origin = origin, source_type = copy_type source_type}) dependencies,
     arity = arity,
     stage = stage}
end
