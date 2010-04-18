structure holindexData =
struct

type data_entry = 
   {label    : string option, 
    in_index : bool, 
    options  : string,
    content  : string,
    pages    : string Redblackset.set}

val default_data_entry =
  ({label    = NONE, 
    in_index = false, 
    options  = "",
    content  = "",
    pages    = (Redblackset.empty String.compare)}:data_entry)

fun data_entry___update_in_index new_ii
  ({label    = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   {label       = label, 
    in_index = new_ii,
    options  = options,
    content  = content,
    pages    = pages}:data_entry;

fun data_entry___update_label new_label
  ({label    = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   {label    = new_label, 
    in_index = in_index,
    options  = options,
    content  = content,
    pages    = pages}:data_entry;

fun data_entry___update_options new_op
  ({label       = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   {label       = label, 
    in_index = in_index,
    options  = new_op,
    content  = content,
    pages    = pages}:data_entry;

fun data_entry___update_content new_content
  ({label       = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   {label       = label, 
    in_index = in_index,
    options  = options,
    content  = new_content,
    pages    = pages}:data_entry;

fun data_entry___add_page page
  ({label       = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   {label       = label, 
    in_index = in_index,
    options  = options,
    content  = content,
    pages    = Redblackset.add(pages,page)}:data_entry;


fun data_entry_is_used 
  ({label    = label, 
    in_index = in_index, 
    options  = options,
    content  = content,
    pages    = pages}:data_entry) =
   (in_index orelse not (Redblackset.isEmpty pages));


val new_data_substore = (Redblackmap.mkDict String.compare):(string, data_entry) Redblackmap.dict

val new_data_store  = (Redblackmap.mkDict String.compare):
   ((string, (string, data_entry) Redblackmap.dict) Redblackmap.dict)


fun get_data_store_keys "Thm" s2 = 
    let
       val ss2 = (Substring.full s2)
       val (x1,x2) = Substring.splitl (fn c => not (c = #".")) ss2
       val x2' = Substring.triml 1 x2
    in
       (Substring.string x1, Substring.string x2')
    end
 | get_data_store_keys s1 s2 = (s1, s2);

(*
   val key1 = "Term";
   val key2 = "Term_ID_1"
   fun upf e = data_entry___add_page e "1";
*)

fun update_data_store ds ((key1:string), (key2:string)) upf =
let
   open Redblackmap

   val sds = find (ds, key1) handle NotFound => new_data_substore
   val ent = find (sds, key2) handle NotFound => default_data_entry;

   val ent' = upf ent;
   val sds' = insert(sds,key2,ent')
   val ds' = insert(ds,key1,sds')
in
   ds'
end;













type parse_entry = 
   {id          : string, 
    label       : string option, 
    force_index : bool, 
    options     : string option,
    content     : string option}

fun mk_parse_entry id =
   {id          = id, 
    label       = NONE,
    force_index = false, 
    options     = NONE,
    content     = NONE}:parse_entry

fun mk_update_parse_entry id up =
   (up (mk_parse_entry id)):parse_entry

fun parse_entry___set_label l
   ({id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id, 
    label       = SOME l,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry;

fun parse_entry___set_options new_opt
   ({id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = SOME new_opt,
    content     = content_opt}:parse_entry;


fun parse_entry___set_content new_cont
   ({id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = SOME new_cont}:parse_entry;

fun parse_entry___force_index
   ({id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id, 
    label       = label_opt,
    force_index = true,
    options     = options_opt,
    content     = content_opt}:parse_entry;


fun parse_entry___add_to_data_store ds
  ({id          = id, 
    label       = label_opt,
    force_index = fi,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
let
   val keys = get_data_store_keys "Thm" id
   fun update_fun ({label    = label, 
                    in_index = in_index, 
                    options  = options,
                    content  = content,
                    pages    = pages}:data_entry) =
      ({label    = if isSome label_opt then label_opt else label, 
        in_index = fi orelse in_index, 
        options  = if isSome options_opt then valOf options_opt else options,
        content  = if isSome content_opt then valOf content_opt else content,
        pages    = pages}:data_entry);
in
   update_data_store ds keys update_fun
end;


end
