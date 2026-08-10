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

  (* Prenex conversion may alpha-rename one of two source binders that had
     the same name and type.  Preserve that ambiguity explicitly by adding
     a duplicate lookup key after the real prefix; real indices do not move,
     but name-based lookup can no longer select the wrong surviving name. *)
  fun mark_source_ambiguities original prefix =
    let
      fun source_binders term =
        if boolSyntax.is_forall term then
          let val (variable, body) = boolSyntax.dest_forall term
          in Term.dest_var variable :: source_binders body end
        else if boolSyntax.is_exists term then
          let val (variable, body) = boolSyntax.dest_exists term
          in Term.dest_var variable :: source_binders body end
        else if Term.is_comb term then
          let val (left, right) = Term.dest_comb term
          in source_binders left @ source_binders right end
        else if Term.is_abs term then
          source_binders (#2 (Term.dest_abs term))
        else
          []
      fun same ((name, ty), (other, other_ty)) =
        name = other andalso Type.compare (ty, other_ty) = EQUAL
      val source = map Term.dest_var (Term.free_vars_lr original) @
        source_binders original
      fun ambiguous key =
        length (List.filter (fn other => same (key, other)) source) > 1
      fun add (key, keys) =
        if not (ambiguous key) orelse
           List.exists (fn old => same (key, old)) keys then keys
        else key :: keys
      val ambiguous = rev (List.foldl add [] source)
    in
      prefix @ ambiguous
    end

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
