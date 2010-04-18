signature holindexData =
sig

   type data_entry =
      {label    : string option,
       pages    : string Redblackset.set,
       content  : string, 
       options  : string, 
       in_index : bool};

   val default_data_entry : data_entry
   val new_data_store     : (string, (string, data_entry) Redblackmap.dict) Redblackmap.dict
   val new_data_substore  : (string, data_entry) Redblackmap.dict

   val data_entry___update_in_index : bool          -> data_entry -> data_entry
   val data_entry___update_label    : string option -> data_entry -> data_entry
   val data_entry___update_options  : string        -> data_entry -> data_entry
   val data_entry___update_content  : string        -> data_entry -> data_entry
   val data_entry___add_page        : string        -> data_entry -> data_entry
   val data_entry_is_used : data_entry -> bool

   val update_data_store : 
        (string, (string, data_entry) Redblackmap.dict) Redblackmap.dict ->
        string * string ->
        (data_entry -> data_entry) ->
        (string, (string, data_entry) Redblackmap.dict) Redblackmap.dict

   val get_data_store_keys : string -> string -> (string * string)

   type parse_entry =
      {id         : string,
       label      : string option,
       content    : string option, 
       options    : string option, 
       force_index: bool}

   val mk_parse_entry            : string -> parse_entry
   val mk_update_parse_entry     : string -> (parse_entry -> parse_entry) -> parse_entry
   val parse_entry___set_label   : string -> parse_entry -> parse_entry
   val parse_entry___set_options : string -> parse_entry -> parse_entry
   val parse_entry___set_content : string -> parse_entry -> parse_entry
   val parse_entry___force_index : parse_entry -> parse_entry

   val parse_entry___add_to_data_store :
      (string, (string, data_entry) Redblackmap.dict) Redblackmap.dict ->
      parse_entry ->
      (string, (string, data_entry) Redblackmap.dict) Redblackmap.dict
end
