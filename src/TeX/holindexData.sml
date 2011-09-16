structure holindexData :> holindexData =
struct

open Lib Feedback

val scomp = String.collate (fn (c1, c2) =>
    Char.compare (Char.toUpper c1, Char.toUpper c2))

type data_entry =
   {label         : string option,
    in_index      : bool,
    printed       : bool,
    full_index    : bool option,
    comment       : string option,
    pos_opt       : int option,
    options       : string,
    content       : string option,
    latex         : string option,
    pages         : string Redblackset.set}

val default_data_entry =
  ({label         = NONE,
    in_index      = false,
    printed       = false,
    full_index    = NONE,
    pos_opt       = NONE,
    comment       = NONE,
    options       = "",
    content       = NONE,
    latex         = NONE,
    pages         = (Redblackset.empty String.compare)}:data_entry)

fun data_entry___update_in_index new_ii
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label            = label,
    in_index      = new_ii,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;

fun data_entry___update_printed new_printed
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label            = label,
    in_index      = in_index,
    printed       = new_printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;


fun data_entry___update_full_index new_fi
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label            = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = SOME new_fi,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;


fun data_entry___update_label new_label
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label         = new_label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;


fun data_entry___update_comment new_comment
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = new_comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;

fun data_entry___update_options new_op
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = new_op,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry;

fun data_entry___update_content new_content
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = new_content,
    latex         = latex,
    pages         = pages}:data_entry;



fun data_entry___update_latex new_latex
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   {label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = new_latex,
    pages         = pages}:data_entry;


val data_entry___pos_counter_ref = ref 0;
fun data_entry___add_page page
  ({label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = pages}:data_entry) =
   let
      val new_pos_opt =
         if isSome pos_opt then pos_opt else
         (data_entry___pos_counter_ref := (!data_entry___pos_counter_ref) + 1;
          SOME (!data_entry___pos_counter_ref));
   in
   {label         = label,
    in_index      = in_index,
    printed       = printed,
    full_index    = full_index,
    comment       = comment,
    pos_opt       = new_pos_opt,
    options       = options,
    content       = content,
    latex         = latex,
    pages         = Redblackset.add(pages,page)}:data_entry
   end;


fun data_entry_is_used
  ({in_index      = in_index,
    pos_opt       = pos_opt,
    ...}:data_entry) =
   (in_index orelse isSome pos_opt);


val new_data_substore = (Redblackmap.mkDict scomp):(string, data_entry) Redblackmap.dict

val new_data_store  =  (*Thms, Terms, Types*)
   (new_data_substore, new_data_substore, new_data_substore);


(*
   val key1 = "Term";
   val key2 = "Term_ID_1"
   fun upf e = data_entry___add_page e "1";
*)
type data_store_ty = ((string, data_entry) Redblackmap.dict * (string, data_entry) Redblackmap.dict * (string, data_entry) Redblackmap.dict);

local
   fun update_data_substore (allow_new,error_fun) sds (key:string) upf =
   let
      open Redblackmap
      val (ent,ok) = (find (sds, key),true) handle NotFound => (default_data_entry, allow_new);
      val sds' = if ok then (insert(sds,key,upf ent)) else
            (error_fun key;sds)
   in
      sds'
   end;

   fun unknown_def (type_def, error_fun:string->unit) s =
       error_fun ("Undefined "^type_def^" '"^s^"'!");
in

fun update_data_store (allow_new,error_fun) (sds_thm,sds_term,sds_type) "Thm" key upf =
   (update_data_substore (true, unknown_def ("Thm", error_fun)) sds_thm key upf,sds_term,sds_type)
| update_data_store (allow_new,error_fun) (sds_thm,sds_term,sds_type) "Term" key upf =
   (sds_thm, update_data_substore
        (allow_new, unknown_def ("Term", error_fun)) sds_term key upf,sds_type)
| update_data_store (allow_new,error_fun) (sds_thm,sds_term,sds_type) "Type" key upf =
   (sds_thm, sds_term, update_data_substore
       (allow_new, unknown_def ("Type", error_fun)) sds_type key upf)
| update_data_store _ _ ty _ _ =
   Feedback.failwith ("Unkwown entry_type '"^ty^"'!")

end;












type parse_entry =
   {id          : (string * string),
    label       : string option,
    force_index : bool,
    full_index  : bool option,
    comment     : string option,
    options     : string option,
    latex       : string option,
    content     : string option}

fun mk_parse_entry id =
   {id          = id,
    label       = NONE,
    force_index = false,
    full_index  = NONE,
    comment     = NONE,
    latex       = NONE,
    options     = NONE,
    content     = NONE}:parse_entry

fun mk_update_parse_entry id up =
   (up (mk_parse_entry id)):parse_entry


fun destruct_theory_thm s2 =
    let
       val ss2 = (Substring.full s2)
       val (x1,x2) = Substring.splitl (fn c => not (c = #".")) ss2
       val x2' = Substring.triml 1 x2
    in
       (Substring.string x1, Substring.string x2')
    end


fun mk_theorem_parse_entries ids up =
   let
      fun expand_theory_map id =
      let
          val (thy, thm) = destruct_theory_thm id
      in
          if not (String.isSuffix "*" thm) then [id] else
          let
             val thmL = List.map (snd o fst) (DB.thy thy);
             val pre = String.substring (thm, 0, String.size thm - 1);
             val thmL' = List.filter (String.isPrefix pre) thmL
          in
             List.map (fn s => String.concat [thy, ".",s]) thmL'
          end
      end;
      val ids' = Lib.flatten (List.map expand_theory_map ids)
   in
      List.map (fn id => mk_update_parse_entry ("Thm", id) up) ids'
   end;


fun parse_entry___set_label l
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = SOME l,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry;

fun parse_entry___set_comment c
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = SOME c,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry;

fun parse_entry___set_latex l
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = SOME l,
    options     = options_opt,
    content     = content_opt}:parse_entry;


fun parse_entry___set_options new_opt
   ({id          = id,
    label       = label_opt,
    latex       = latex,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = SOME new_opt,
    content     = content_opt}:parse_entry;


fun parse_entry___set_content new_cont
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = SOME new_cont}:parse_entry;

fun parse_entry___force_index
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    options     = options_opt,
    comment     = comment,
    latex       = latex,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = true,
    full_index  = full_index,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry;

fun parse_entry___full_index b
   ({id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = full_index,
    options     = options_opt,
    comment     = comment,
    latex       = latex,
    content     = content_opt}:parse_entry) =
   {id          = id,
    label       = label_opt,
    force_index = fi,
    full_index  = SOME b,
    comment     = comment,
    latex       = latex,
    options     = options_opt,
    content     = content_opt}:parse_entry;



fun parse_entry___add_to_data_store ds
  ({id          = (ety, id_s),
    label       = label_opt,
    force_index = fi,
    full_index  = full_i,
    comment     = comment_opt,
    latex       = latex_opt,
    options     = options_opt,
    content     = content_opt}:parse_entry) =
let
   fun update_fun ({label    = label,
                    in_index = in_index,
                    printed    = printed,
                    full_index = full_index,
                    comment    = comment,
                    latex      = latex,
                    pos_opt    = pos_opt,
                    options  = options,
                    content  = content,
                    pages    = pages}:data_entry) =
      ({label      = if isSome label_opt then label_opt else label,
        in_index   = fi orelse in_index,
        printed    = printed,
        full_index = if isSome full_i then full_i else full_index,
        comment    = if isSome comment_opt then comment_opt else comment,
        latex      = if isSome latex_opt then latex_opt else latex,
        pos_opt    = pos_opt,
        options    = if isSome options_opt then valOf options_opt else options,
        content    = if isSome content_opt then content_opt else content,
        pages      = pages}:data_entry);
in
   update_data_store (true, K ()) ds ety id_s update_fun
end;


end
