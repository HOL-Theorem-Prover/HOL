signature TypeOpTable =
sig
  type hol_type = Type.hol_type
  type term = Term.term
  type thm = Thm.thm
  type type_info = TypeInfo.type_info

  val make : string * thm list 
             -> 
             {name:string, arity:int,
              rec_thm:thm,
              original_constructors : hol_type list -> term list,
              make_type: type_info list ->
			    {type_name : string,
			     constructors : {name : string,
					     arg_info : type_info list} list}}
             StringTable.table
            * 
            (string -> string)
end
