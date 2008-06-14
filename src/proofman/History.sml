(*---------------------------------------------------------------------------*)
(* History provides "registers-with-bounded-history". You can read (via      *)
(* "project"), write (via "apply"), and undo.                                *)
(*---------------------------------------------------------------------------*)

structure History :> History =
struct

open Feedback Lib;

val HIST_ERR = mk_HOL_ERR "History";
exception CANT_BACKUP_ANYMORE;

datatype 'a history = HISTORY of {obj:'a, past:'a list, orig:'a, limit:int};

fun new_history {obj, limit} = HISTORY{obj=obj, past=[], orig=obj, limit=limit}

local fun chop n alist = fst (split_after n alist) handle _ => alist
in
fun apply f (HISTORY{obj, past, orig, limit}) = 
      HISTORY{obj=f obj, past=chop limit (obj::past), orig=orig, limit=limit}

fun set_limit (HISTORY{obj,past,orig,limit}) n =
  if n<0 then raise HIST_ERR "set_limit" "negative limit"
  else HISTORY{obj=obj, past=chop n past, orig=orig, limit=n}
end;

fun initialValue (HISTORY{orig, ...}) = orig;

fun project f (HISTORY{obj, ...}) = f obj;

fun undo (HISTORY{past=[], ...}) = raise CANT_BACKUP_ANYMORE
  | undo (HISTORY{past=h::rst, limit, orig, ...}) =
          HISTORY{obj=h, past=rst, orig=orig, limit=limit}

end
