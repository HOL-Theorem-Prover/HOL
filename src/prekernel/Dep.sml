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
(* We store the dependencies of a theorem as a sorted list of dependencies   *)
(* identifiers factorized by theory (thydepl).                               *)
(*---------------------------------------------------------------------------*)

type depid       = string * int
datatype dep     = DEP_SAVED of depid * (string * int list) list
                 | DEP_UNSAVED of (string * int list) list
type depdisk     = (string * int) * ((string * int list) list)

val empty_dep    = DEP_UNSAVED []

(*---------------------------------------------------------------------------
   Accessors
 ----------------------------------------------------------------------------*)

fun depthy_of depid = fst depid
fun depnumber_of depid = snd depid

fun depid_of d = case d of
    DEP_SAVED (did,_) => did
  | DEP_UNSAVED _     => raise ERR "depid_of_dep" ""

fun thydepl_of dep = case dep of
    DEP_SAVED (did,thydl) => thydl
  | DEP_UNSAVED thydl     => thydl

fun flatten_thydepl thydepl =
  let fun distrib (s,nl) = map (fn n => (s,n)) nl in
    List.concat (map distrib thydepl)
  end

fun depidl_of dep = flatten_thydepl (thydepl_of dep)

(*---------------------------------------------------------------------------
   Comparison
 ----------------------------------------------------------------------------*)

fun couple_compare compare1 compare2 ((a1,a2),(b1,b2)) =
  case compare1 (a1,b1) of
    LESS    => LESS
  | GREATER => GREATER
  | EQUAL   => compare2 (a2,b2)


val depid_compare = couple_compare String.compare Int.compare

(*---------------------------------------------------------------------------
   Tracking dependencies in inference rules.
 ----------------------------------------------------------------------------*)

fun transfer_thydepl d = case d of
    DEP_SAVED ((thy,n),thydl) => [(thy,[n])]
  | DEP_UNSAVED thydl     => thydl

fun merge_intl nl1 nl2 = case (nl1, nl2) of
     ([], _) => nl2
   | (_, []) => nl1
   | (n1 :: m1, n2 :: m2) =>
     (
     case Int.compare (n1,n2) of
        LESS    => n1 :: merge_intl m1 nl2
      | GREATER => n2 :: merge_intl nl1 m2
      | EQUAL   => n1 :: merge_intl m1 m2
     )

fun merge_thydepl thydl1 thydl2 = case (thydl1, thydl2) of
     ([], _) => thydl2
   | (_, []) => thydl1
   | ((thy1,nl1) :: m1, (thy2,nl2) :: m2) =>
     (
     case String.compare (thy1,thy2) of
        LESS    => (thy1, nl1) :: merge_thydepl m1 thydl2
      | GREATER => (thy2, nl2) :: merge_thydepl thydl1 m2
      | EQUAL   => (thy1, merge_intl nl1 nl2) :: merge_thydepl m1 m2
     )

fun merge_dep d1 d2 =
  let val (thydl1,thydl2) = (transfer_thydepl d1, transfer_thydepl d2) in
    DEP_UNSAVED (merge_thydepl thydl1 thydl2)
  end

(*---------------------------------------------------------------------------
   Printing dependencies to disk.
 ----------------------------------------------------------------------------*)

fun pp_dep_aux ppstrm (did,thydl) =
  let
    open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
    fun pp_l_aux f L = case L of
        []     => ()
      | [a]    => f a
      | a :: m => (f a; add_string ","; add_break(0,0); pp_l_aux f m)
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
    fun pp_did (thy,n) = pp_scouple (Lib.quote thy, int_to_string n)
    fun pp_thyentry (thy,l) =
      pp_couple (add_string o Lib.quote, pp_l add_string) (thy,map int_to_string l)
    fun pp_thydepl l = pp_l pp_thyentry l
  in
    pp_couple (pp_did, pp_thydepl) (did,thydl)
  end

fun pp_dep ppstrm d = case d of
    DEP_SAVED (did,thydl) => pp_dep_aux ppstrm (did,thydl)
  | DEP_UNSAVED dl     => raise ERR "pp_dep" ""

(*---------------------------------------------------------------------------
   Reading dependencies from disk.
 ----------------------------------------------------------------------------*)

fun read_dep (did,l) = DEP_SAVED(did,l)

end
