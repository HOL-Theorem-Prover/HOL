structure TypeInfo :> TypeInfo =
    struct
	datatype type_info = existing of Type.hol_type 
                           | being_defined of string
    end;
