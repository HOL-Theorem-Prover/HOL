(* ===================================================================== *)
(* FILE          : Dep.sml                                               *)
(* DESCRIPTION   : Dependency tracking between conjuncts of theorems     *)
(*                 for holyhammer (under universal quantifiers).         *)
(*                                                                       *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure Dep :> Dep =
struct
open Lib Feedback

val ERR = mk_HOL_ERR "Dep"

(*---------------------------------------------------------------------------*)
(* A theorem is tagged DEP_NAMED when it is saved, its conjuncts are tagged  *)
(* DEP_CONJ. Otherwise, theorems are tagged DEP_INTER. We store the          *)
(* dependencies of a theorem as a tree. Each leaf is associated with a       *)
(* conjunct of this theorem and contains the set of its dependencies.        *)
(*---------------------------------------------------------------------------*)

type depid       = string * int
datatype depchoice = DEP_LEFT | DEP_RIGHT
type depaddress  = depchoice list
type depconj     = depid * depaddress
datatype deptree = DEP_NODE of deptree * deptree 
                 | DEP_LEAF of depconj list
datatype dep     = DEP_SAVED of depid * deptree * deptree
                 | DEP_UNSAVED of deptree
type depdisk     =  
  (string * int) * 
  (string * (string * int list * (int * string) list) list) list

val empty_deptree = DEP_LEAF []
val empty_dep     = DEP_UNSAVED empty_deptree

fun depthy_of depid = fst depid
fun depnumber_of depid = snd depid
fun depid_of depconj  = fst depconj
(* for efficiency, the list returned is in reverse order. *)
fun depaddress_of depconj = snd depconj

fun deptree_of dep = case dep of
    DEP_SAVED (did,dt1,dt2) => dt1
  | DEP_UNSAVED dt          => dt

fun saveddeptree_of dep = case dep of
    DEP_SAVED (did,dt1,dt2) => dt2
  | DEP_UNSAVED dt          => raise ERR "saveddeptree_of" "" 

fun depid_of_dep dep = case dep of
    DEP_SAVED (did,dt1,dt2) => did
  | DEP_UNSAVED dt          => raise ERR "depid_of_dep" ""
   

(* Comparison functions *)
fun couple_compare compare1 compare2 ((a1,a2),(b1,b2)) = 
  case compare1 (a1,b1) of
    EQUAL   => compare2 (a2,b2)
  | LESS    => LESS
  | GREATER => GREATER

fun depchoice_compare (lr1,lr2) = case (lr1,lr2) of
    (DEP_LEFT,DEP_RIGHT) => LESS
  | (DEP_RIGHT,DEP_LESS) => GREATER
  | _                    => EQUAL

val depid_compare = couple_compare String.compare Int.compare
val depaddress_compare = list_compare depchoice_compare
val depconj_compare = couple_compare depid_compare depaddress_compare 

(*---------------------------------------------------------------------------
   Dependency tree constructors and destructors.
 ----------------------------------------------------------------------------*)

fun mk_deptree (dt1,dt2) = DEP_NODE(dt1,dt2)
fun dest_deptree (DEP_NODE(dt1,dt2)) = (dt1,dt2)
  | dest_deptree _                    = raise ERR "dest_deptree" ""
 
fun mk_depleaf dcl = DEP_LEAF dcl
fun dest_depleaf (DEP_LEAF dcl) = dcl
  | dest_depleaf (DEP_NODE _)   = raise ERR "dest_leaf" ""
        
(*---------------------------------------------------------------------------
   Transfering the dependency trees from parents to children of a rule.
 ----------------------------------------------------------------------------*)

(* used when a rule modifies the top-level structure of conjuncts *)
fun collapse_deptree deptree = 
  let 
    val l = ref [] 
    fun loop dt = case dt of
      DEP_LEAF dcl      => l := dcl :: (!l)
    | DEP_NODE(dt1,dt2) => (loop dt1; loop dt2)
  in 
    (loop deptree; DEP_LEAF (mk_set (List.concat (!l))))
  end

(*---------------------------------------------------------------------------
   Printing dependencies to disk. 
 ----------------------------------------------------------------------------*)

(* Numbering the conjuncts when possible. *)

fun number_depaddress a = 
  if null a then "" 
  else if all (equal DEP_RIGHT) (tl a) 
       then case hd a of 
              DEP_LEFT  => int_to_string ((length a) - 1)
            | DEP_RIGHT => "e" ^ int_to_string (length a)
       else "t" ^ concat (map (fn DEP_LEFT => "L" | DEP_RIGHT => "R") a) 

(* Changing the representation of the tree to a list of leafs with addresses.
   The list is sorted so that the tree can be rebuild later. *)

fun flatten_deptree a dt = 
 let 
   val l = ref [] 
   fun loop a' dt' = case dt' of
     DEP_LEAF dcl      => l := (a',dcl) :: (!l)
   | DEP_NODE(dt1,dt2) => (loop (DEP_RIGHT :: a') dt2; loop (DEP_LEFT :: a') dt1) 
 in
   (loop a dt; !l)
 end

(* Sorting the dependencies by theory. *)
(* We don't print the addresses of the conjuncts if they are empty. *)

fun insert_dc_empty ((dc,thy),l) = case l of
   []                => [(thy,[dc],[])] 
 | (thy',l1,l2) :: m => 
     if thy' = thy 
     then (thy',dc :: l1,l2) :: m 
     else (thy',l1,l2) :: insert_dc_empty ((dc,thy),m) 

fun insert_dc_conj ((dc,thy),l) = case l of
   []                => [(thy,[],[dc])]
 | (thy',l1,l2) :: m => 
     if thy' = thy 
     then (thy',l1,dc :: l2) :: m 
     else (thy',l1,l2) :: insert_dc_conj ((dc,thy),m)

fun insert_dc ((dc,thy),l) = 
  if null (depaddress_of dc)
  then insert_dc_empty ((dc,thy),l)
  else insert_dc_conj ((dc,thy),l)

fun sort_dcl dcl = 
  let fun f dc = (dc, depthy_of (depid_of dc)) in
    List.foldl insert_dc [] (List.map f dcl)
  end

(* Pretty-printing *)
fun pp_dep_aux ppstrm (did,dt) =
  let 
    open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
    val num_address = Lib.quote o number_depaddress
    fun pp_dl f L = case L of
        []     => ()
      | [a]    => f a 
      | a :: m => (f a; add_string ","; add_break(0,0); pp_dl f m)   
    fun pp_l f L =
      (begin_block INCONSISTENT 0;
         add_string "[";
         begin_block INCONSISTENT 0;
           pp_dl f L;
         end_block();  
         add_string "]";
       end_block())
    fun pp_couple (f1,f2) (a1,a2) =
      (begin_block INCONSISTENT 0;
         add_string "("; f1 a1; add_string ","; add_break(0,0);
                         f2 a2; add_string ")";
       end_block())
    fun pp_scouple (s1,s2) = pp_couple (add_string,add_string) (s1,s2)
    fun pp_triple (f1,f2,f3) (a1,a2,a3) =
      (begin_block INCONSISTENT 0;
          add_string "("; f1 a1; add_string ","; add_break(0,0);
                          f2 a2; add_string ","; add_break(0,0);
                          f3 a3; add_string ")";
       end_block())
    fun pp_did (s,n) = pp_scouple (Lib.quote s, int_to_string n)
    fun pp_dc_empty ((s,n),a) = add_string (int_to_string n)
    fun pp_dc_conj ((s,n),a) =
      pp_scouple (int_to_string n, num_address a)
    fun pp_thyentry (thy,l1,l2) = 
      pp_triple (add_string o Lib.quote, pp_l pp_dc_empty, pp_l pp_dc_conj) 
                (thy,l1,l2)
    fun pp_dcl l = pp_l pp_thyentry l 
    fun pp_dt dt = 
      let fun pp_f (a,dcl) = 
        pp_couple (add_string o num_address, pp_dcl o sort_dcl) (a,dcl)
      in
        pp_l pp_f (flatten_deptree [] dt)
      end
  in
    pp_couple (pp_did,pp_dt) (did,dt)
  end

fun pp_dep ppstrm d = case d of
    DEP_SAVED (did,dt1,dt2) => pp_dep_aux ppstrm (did,dt2) 
  | DEP_UNSAVED dt          => raise ERR "pp_dep" ""


(*---------------------------------------------------------------------------
   Reading dependencies from disk. 
 ----------------------------------------------------------------------------*)

(* Decoding the address. *)

fun read_depaddress a = 
       if a = ""                then [] 
  else if String.isPrefix "e" a then 
         let val n = string_to_int (String.extract (a, 1, NONE)) in 
           List.tabulate (n,(fn _ => DEP_RIGHT))
         end
  else if String.isPrefix "t" a then 
         map (fn #"L" => DEP_LEFT 
               | #"R" => DEP_RIGHT 
               | _    => raise ERR "read_depaddress" "") (tl (explode a))
  else DEP_LEFT :: List.tabulate (string_to_int a, fn _ => DEP_RIGHT) 

(* Rebuild the tree from its leafs and their addresses. *)

fun build_tree leafl current_address = case leafl of
    []           => raise ERR "build_tree" "empty_tree"
  | [(a,dcl)]    => (DEP_LEAF dcl, [])
  | (a,dcl) :: m => 
      if a = current_address then (DEP_LEAF dcl, m)
      else
        let 
          val (t_left,leafl_right) = 
            build_tree leafl (DEP_LEFT :: current_address) 
          val (t_right,leafl_next) = 
            build_tree leafl_right (DEP_RIGHT :: current_address)
        in
          (DEP_NODE (t_left,t_right), leafl_next)
        end

(* Reading *)

fun read_dc_empty thy n    = ((thy,n), [])
fun read_dc_conj thy (n,a) = ((thy,n), read_depaddress a)

fun read_thyentry (thy,l1,l2) = 
  map (read_dc_empty thy) l1 @ map (read_dc_conj thy) l2

fun read_leaf (a,l) = 
  (read_depaddress a, List.concat (map read_thyentry l))

fun read_deptree dt = fst (build_tree (map read_leaf dt) [])

(* Replace dependencies by conjuncts identifiers (dep_conj) *)
fun new_deptree a (did,dt) = case dt of
    DEP_NODE(dt1,dt2) => DEP_NODE(
                           new_deptree (DEP_LEFT :: a) (did,dt1),
                           new_deptree (DEP_RIGHT :: a) (did,dt2)
                         )
  | DEP_LEAF _        => DEP_LEAF [(did,a)]


fun read_dep (did,dt) = 
  let val dt' = read_deptree dt in
    DEP_SAVED(did, new_deptree [] (did,dt'), dt')
  end

end
