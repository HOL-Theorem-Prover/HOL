(*---------------------------------------------------------------------------
 * History provides "registers-with-bounded-history". You can read (via
 * "project"), write (via "apply"), and undo. This is a general purpose
 * type.
 *---------------------------------------------------------------------------*)

structure History :> History =
struct

open Exception Lib;

fun HIST_ERR func mesg =
    HOL_ERR{origin_structure = "History",
            origin_function = func,
            message = mesg}


datatype 'a history = HISTORY of {obj :'a, past :'a list, limit :int};

exception CANT_BACKUP_ANYMORE;

fun new_history {obj, limit} = HISTORY{obj = obj, past = [], limit = limit}

local
fun chop n alist = fst (split_after n alist) handle _ => alist
in
fun apply f (HISTORY{obj, past, limit}) = 
      HISTORY{obj = f obj, past = chop limit (obj :: past), limit = limit}

fun set_limit (HISTORY{obj,past,limit}) n =
   if (n<0) then raise HIST_ERR "set_limit" "negative limit"
   else HISTORY{obj = obj, past = chop n past, limit = n}
end;

fun project f (HISTORY{obj, ...}) = f obj;

fun undo (HISTORY{past = h::rst, limit,...}) = 
          HISTORY{obj = h, past = rst, limit = limit}
  | undo (HISTORY{past = [], ...}) = raise CANT_BACKUP_ANYMORE


end;
