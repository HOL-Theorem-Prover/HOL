(* ===================================================================== *)
(* FILE          : Dep.sml                                               *)
(* DESCRIPTION   : Dependency tracking between theorems                  *)
(*                 for holyhammer                                        *)
(*                                                                       *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure Dep :> Dep =
struct
open Lib Feedback

val ERR = mk_HOL_ERR "Dep"

(*---------------------------------------------------------------------------*)
(* We store the dependencies of a theorem as a list of dependencies          *)
(* identifiers (did).                                                        *)
(*---------------------------------------------------------------------------*)

type depid       = string * int
datatype dep     = DEP_SAVED of depid * depid list
                 | DEP_UNSAVED of deplist
type depdisk     = (string * int) * ((string * int list) list) 

val empty_deplist = []
val empty_dep     = DEP_UNSAVED empty_deplist

fun depthy_of depid = fst depid
fun depnumber_of depid = snd depid

fun depidlist_of dep = case dep of
    DEP_SAVED (did,dl) => dl
  | DEP_UNSAVED dl     => dl

fun depid_of d = case d of
    DEP_SAVED (did,_) => did
  | DEP_UNSAVED _     => raise ERR "depid_of_dep" ""

(* Comparison functions *)
fun couple_compare compare1 compare2 ((a1,a2),(b1,b2)) =
  case compare1 (a1,b1) of
    EQUAL   => compare2 (a2,b2)
  | LESS    => LESS
  | GREATER => GREATER

val depid_compare = couple_compare String.compare Int.compare

(*---------------------------------------------------------------------------
   Tracking dependencies in inference rules.
 ----------------------------------------------------------------------------*)

let transfer_didlist d = case d of
    DEP_SAVED (did,dl) => [did]
  | DEP_UNSAVED dl     => dl
 
let merge_dep d1 d2 = 
  let val (dl1,dl2) = (transfer_didlist d1, transfer_didlist d2) in
  DEP_UNSAVED (mk_set (dl1 @ dl2))

(*---------------------------------------------------------------------------
   Printing dependencies to disk.
 ----------------------------------------------------------------------------*)

(* Sorting dependencies by theory to minimize the space consumption *)
fun insert_did (did,acc) = 
  case acc of
    []           => [(depthy_of did,[did])]
  | (thy,l) :: m =>
    if thy = depthy_of did
    then (thy,did :: l) :: m
    else (thy,l)        :: insert_did (did,m)

fun regroup_didl l = List.foldl insert_did [] l

(* Pretty-printing *)
fun pp_dep_aux ppstrm (did,dt) =
  let
    open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
    fun pp_l_aux f L = case L of
        []     => ()
      | [a]    => f a
      | a :: m => (f a; add_string ","; add_break(0,0); pp_dl f m)
    fun pp_l f L =
      (begin_block INCONSISTENT 0;
         add_string "[";
         begin_block INCONSISTENT 0;
           pp_l_aux f L;
         end_block();
         add_string "]";
       end_block())
    fun pp_couple (f1,f2) (a1,a2) =
      (begin_block INCONSISTENT 0;
         add_string "("; f1 a1; add_string ","; add_break(0,0);
                         f2 a2; add_string ")";
       end_block())
    fun pp_scouple (s1,s2) = pp_couple (add_string,add_string) (s1,s2)
       end_block())
    fun pp_did (thy,n) = pp_scouple (Lib.quote thy, int_to_string n)
    fun pp_did_wothy (thy,n) = add_string (int_to_string n)
    fun pp_thyentry (thy,l) =
      pp_couple (add_string o Lib.quote, pp_l pp_did_wothy) (thy,l)
    fun pp_thyentryl l = pp_l pp_thyentry l
  in
    pp_couple (pp_did,pp_thyentryl o regroup dl) (did,dl)
  end

fun pp_dep ppstrm d = case d of
    DEP_SAVED (did,dl1,dl2) => pp_dep_aux ppstrm (did,dl2)
  | DEP_UNSAVED dl          => raise ERR "pp_dep" ""

(*---------------------------------------------------------------------------
   Reading dependencies from disk.
 ----------------------------------------------------------------------------*)

fun read_did thy n = (thy,n)
fun read_thyentry (thy,l) = map (read_did thy) l 
fun read_thyentryl l = List.concat (map read_thyentry l) 
fun read_dep (did,l) = DEP_SAVED(did, read_thyentryl l)

end
