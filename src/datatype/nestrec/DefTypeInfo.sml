structure DefTypeInfo :> DefTypeInfo =
    struct
        datatype type_info = 
            existing of Type.hol_type
          | type_op of {Tyop : string, Args : type_info list}
          | being_defined of string
    end;
