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

structure TypeTable :> TypeTable =
struct
 datatype 'a table_entry = InTable of 'a | NotFound

datatype rel = Equal | Less | Grt
type index = Type.hol_type

fun get_type t =
     Type.dest_type t handle Exception.HOL_ERR _ =>
		{Tyop = Type.dest_vartype t, Args = []}
fun compare t t' =
   if t = t' then Equal
   else
     let
        val {Tyop = Tyop_t, Args = Args_t} = get_type t
        val {Tyop = Tyop_t', Args = Args_t'} = get_type t'
     in
          if Tyop_t < Tyop_t' then Less
          else if Tyop_t' < Tyop_t then Grt
          else compare_args Args_t Args_t'
     end
and 
   compare_args [] [] = Equal
 | compare_args [] (_::_) = Less
 | compare_args (_::_) [] = Grt
 | compare_args (a::l) (a'::l') =
     case compare a a' of
        Equal => compare_args l l'
      | Less => Less
      | Grt => Grt

 type 'a table = (Type.hol_type * 'a) list

val empty = []

fun enter {key, entry, table = []} = [(key, entry)]
  | enter {key, entry, table = (key', entry')::l} =
      case compare key key' of
          Equal => ((key, entry)::l)
        | Less => (key, entry)::(key', entry')::l
        | Grt => (key', entry')::enter {key = key,entry = entry,table = l}

fun lookup {key, table = []} = NotFound
  | lookup {key, table = (key', entry')::l} =
        case compare key key' of
           Equal => InTable entry'
         | Less => NotFound
         | Grt => lookup {key = key, table = l}

fun elts l = map (fn (_, b) => b) l

end;
