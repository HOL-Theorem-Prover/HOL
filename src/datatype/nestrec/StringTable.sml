(* =====================================================================*)
(* FILE          : table.sml                                            *)
(* DESCRIPTION   : Functor for creating quick lookup tables.            *)
(*                 It's undefined what happens if we enter the same     *)
(*                 index but different entries                          *)
(*                                                                      *)
(* AUTHOR        : Healfdene Goguen, University of Edinburgh            *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure StringTable :> StringTable =
struct

datatype rel = Equal | Less | Grt;

 fun compare (s:string) (s':string) =
     if s = s' then Equal
     else if s < s' then Less
     else Grt;
     
 datatype 'a table_entry = InTable of 'a | NotFound

 type 'a table = (string * 'a) list

 val empty = []

 fun enter {key, entry, table = []} = [(key, entry)]
   | enter {key, entry, table = (key', entry')::l} =
        case compare key key' 
         of Equal => ((key, entry)::l)
          | Less => (key, entry)::(key', entry')::l
          | Grt => (key', entry') :: enter {key = key,
                                            entry = entry, table = l}

  fun lookup {key, table = []} = NotFound
    | lookup {key, table = (key', entry')::l} =
        case compare key key' 
        of Equal => InTable entry'
         | Less => NotFound
         | Grt => lookup {key = key, table = l}

  fun elts l = map (fn (_, b) => b) l

end;
