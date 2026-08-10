structure Refute_Skolem = struct
  type dependency =
    {origin : int,
     source_type : Type.hol_type}

  type info =
    {origin : int,
     generated_name : string,
     source_name : string,
     source_type : Type.hol_type,
     dependencies : dependency list,
     arity : int,
     stage : string}

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
