signature holindexData =
sig

   type data_entry =
   {label         : string option,
    in_index      : bool,
    full_index    : bool option,
    comment       : string option,
    pos_opt       : int option,
    options       : string,
    content       : string option,
    pages         : string Redblackset.set}

   type data_store_ty = ((string, data_entry) Redblackmap.dict * (string, data_entry) Redblackmap.dict * (string, data_entry) Redblackmap.dict);

   val default_data_entry : data_entry
   val new_data_store     : data_store_ty;
   val new_data_substore  : (string, data_entry) Redblackmap.dict

   val data_entry___update_in_index   : bool          -> data_entry -> data_entry
   val data_entry___update_full_index : bool          -> data_entry -> data_entry
   val data_entry___update_label      : string option -> data_entry -> data_entry
   val data_entry___update_options    : string        -> data_entry -> data_entry
   val data_entry___update_content    : string option -> data_entry -> data_entry
   val data_entry___update_comment    : string option -> data_entry -> data_entry
   val data_entry___add_page          : string        -> data_entry -> data_entry
   val data_entry_is_used : data_entry -> bool

   val update_data_store : 
        data_store_ty -> string -> string ->
        (data_entry -> data_entry) ->
        data_store_ty

   type parse_entry =
   {id          : (string * string),
    label       : string option,
    force_index : bool,
    full_index  : bool option,
    comment     : string option,
    options     : string option,
    content     : string option}

   val mk_parse_entry            : (string * string) -> parse_entry
   val mk_update_parse_entry     : (string * string) -> (parse_entry -> parse_entry) -> parse_entry
   val parse_entry___set_label   : string -> parse_entry -> parse_entry
   val parse_entry___set_options : string -> parse_entry -> parse_entry
   val parse_entry___set_content : string -> parse_entry -> parse_entry 
   val parse_entry___set_comment : string -> parse_entry -> parse_entry
   val parse_entry___force_index : parse_entry -> parse_entry
   val parse_entry___full_index  : bool -> parse_entry -> parse_entry

   val parse_entry___add_to_data_store :
      data_store_ty -> parse_entry -> data_store_ty
end
