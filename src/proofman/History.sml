(*---------------------------------------------------------------------------*)
(* History provides "registers-with-bounded-history". You can read (via      *)
(* "project"), write (via "apply"), and undo.                                *)
(*---------------------------------------------------------------------------*)

structure History :> History =
struct

open Feedback Lib;

val HIST_ERR = mk_HOL_ERR "History";
exception CANT_BACKUP_ANYMORE;

datatype 'a history = HISTORY of {obj:'a, past:'a list, orig:'a, limit:int, save_points:'a list};

fun new_history {obj, limit} = HISTORY{obj=obj, past=[], orig=obj, limit=limit, save_points = []}

local fun chop n alist = fst (split_after n alist) handle _ => alist
in
fun apply f (HISTORY{obj, past, orig, limit, save_points}) =
      HISTORY{obj=f obj, past=chop limit (obj::past), orig=orig, limit=limit, save_points=save_points}

fun set_limit (HISTORY{obj,past,orig,limit,save_points}) n =
  if n<0 then raise HIST_ERR "set_limit" "negative limit"
  else HISTORY{obj=obj, past=chop n past, orig=orig, limit=n,save_points=save_points}
end;

fun remove_past (HISTORY{obj,past,orig,limit,save_points}) =
  new_history {obj=obj,limit=limit};

fun initialValue (HISTORY{orig, ...}) = orig;

fun project f (HISTORY{obj, ...}) = f obj;

fun undo (HISTORY{past=[], ...}) = raise CANT_BACKUP_ANYMORE
  | undo (HISTORY{past=h::rst, limit, orig,save_points,...}) =
          HISTORY{obj=h, past=rst, orig=orig, limit=limit,save_points=save_points}

fun restore (HISTORY{obj,past,orig,limit,save_points}) =
  let
     val (save_points',obj') = if (null save_points) then ([], orig) else
         (if not (null past) then (save_points, hd save_points) else
             (if null (tl save_points) then ([], orig) else
                 (tl save_points, hd (tl (save_points)))));
  in
     HISTORY{obj=obj', past=[], orig=orig, limit=limit, save_points=save_points'}     
  end;

fun save (HISTORY{obj,past,orig,limit,save_points}) =
     HISTORY{obj=obj, past=[], orig=orig, limit=limit, save_points=obj::save_points}     

end
