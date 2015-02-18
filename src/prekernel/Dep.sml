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
(* conjunct of this theorem and contains the set of its dependencies.       *)
(*---------------------------------------------------------------------------*)

type depid       = string * int
datatype depchoice = DEP_LEFT | DEP_RIGHT
type depaddress  = depchoice list
datatype depsort = DEP_NAMED of depid
                 | DEP_CONJ of depid * depaddress
                 | DEP_INTER
datatype deptree = DEP_NODE of deptree * deptree 
                 | DEP_LEAF of depsort list
 
type dep         = depsort * deptree
type depdisk     =  
  (string * int) * 
  (string * (string * int list * (int * string) list) list) list

val empty_deptree = DEP_LEAF []
val empty_dep     = (DEP_INTER,empty_deptree)

fun depthy_of depid = fst depid
fun depnumber_of depid = snd depid

fun depid_of depsort  = case depsort of
    DEP_NAMED depid    => depid
  | DEP_CONJ (depid,a) => depid 
  | _                  => raise ERR "depid_of" ""

(* For efficiency, the list should be read in reverse order. *)
fun address_of depsort = case depsort of
    DEP_NAMED depid => []
  | DEP_CONJ(depid,a) => a
  | _                  => raise ERR "address_of" "" 


fun deptree_of dep = snd dep
fun depsort_of dep = fst dep

(* Comparisons functions *)

fun depchoice_compare (lr1,lr2) = case (lr1,lr2) of
    (DEP_LEFT,DEP_RIGHT) => LESS
  | (DEP_RIGHT,DEP_LESS) => GREATER
  | _                    => EQUAL

fun depid_compare ((s1,n1),(s2,n2)) = case String.compare (s1,s2) of
    LESS => LESS
  | GREATER => GREATER
  | EQUAL => Int.compare (n1,n2)

val depaddress_compare = list_compare depchoice_compare

fun depsort_compare (ds1,ds2) = case (ds1,ds2) of
    (DEP_INTER,DEP_INTER) => EQUAL
  | (DEP_INTER,_)         => LESS
  | (_,DEP_INTER)         => GREATER
  | _                     => 
      case depid_compare (depid_of ds1, depid_of ds2) of
        EQUAL   => depaddress_compare (address_of ds1, address_of ds2)
      | LESS    => LESS
      | GREATER => GREATER 

(*---------------------------------------------------------------------------
   Dependency tree constructors and destructors.
 ----------------------------------------------------------------------------*)

fun mk_deptree (dt1,dt2) = DEP_NODE(dt1,dt2)
fun dest_deptree (DEP_NODE(dt1,dt2)) = (dt1,dt2)
  | dest_deptree _                    = raise ERR "dest_deptree" ""
 
fun mk_depleaf dsl = DEP_LEAF dsl
fun dest_depleaf (DEP_LEAF dsl) = dsl
  | dest_depleaf (DEP_NODE _)   = raise ERR "dest_leaf" ""
        
(*---------------------------------------------------------------------------
   Transfering the dependency trees from parents to children of a rule.
 ----------------------------------------------------------------------------*)

fun merge_deptree deptree = 
  let 
    val l = ref [] 
    fun loop dt = case dt of
      DEP_LEAF dsl      => l := dsl :: (!l)
    | DEP_NODE(dt1,dt2) => (loop dt1; loop dt2)
  in 
    (loop deptree; DEP_LEAF (mk_set (List.concat (!l))))
  end

fun passed_deptree (depsort,deptree) = case depsort of 
    DEP_NAMED _ => DEP_LEAF [depsort]
  | _           => deptree

(* conjuncts of theorems depend on themselves *)
fun self_dep depsort = (depsort, DEP_LEAF [depsort])

(*---------------------------------------------------------------------------
   Printing dependencies to disk. 
 ----------------------------------------------------------------------------*)

(* Numbering the conjuncts when possible *)

fun number_address a = 
  if null a then "" 
  else if all (equal DEP_RIGHT) (tl a) 
       then case hd a of 
              DEP_LEFT  => int_to_string ((length a) - 1)
            | DEP_RIGHT => "e" ^ int_to_string (length a)
       else "t" ^ concat (map (fn DEP_LEFT => "L" | DEP_RIGHT => "R") a) 

fun quote_of_address a = Lib.quote (number_address a)

(* Changing the representation of the tree to a list of leafs with addresses.
   The list is sorted so that the tree can be rebuild later. *)

fun flatten_deptree a dt = 
 let 
   val l = ref [] 
   fun loop a' dt' = case dt' of
     DEP_LEAF dsl      => l := (a',dsl) :: (!l)
   | DEP_NODE(dt1,dt2) => (loop (DEP_RIGHT :: a') dt2; loop (DEP_LEFT :: a') dt1) 
 in
   (loop a dt; !l)
 end

(* Sorting the dependencies by theory and sort *)

fun insert_ds_named ((ds,thy),l) = case l of
   []                => [(thy,[ds],[])] 
 | (thy',l1,l2) :: m => 
     if thy' = thy 
     then (thy',ds :: l1,l2) :: m 
     else (thy',l1,l2) :: insert_ds_named ((ds,thy),m) 

fun insert_ds_conj ((ds,thy),l) = case l of
   []                => [(thy,[],[ds])]
 | (thy',l1,l2) :: m => 
     if thy' = thy 
     then (thy',l1,ds :: l2) :: m 
     else (thy',l1,l2) :: insert_ds_conj ((ds,thy),m)

fun insert_ds ((ds,thy),l) = case ds of 
   DEP_NAMED _ => insert_ds_named ((ds,thy),l)
 | DEP_CONJ  _ => insert_ds_conj ((ds,thy),l)
 | _           => raise ERR "insert_ds" ""

fun sort_dsl dsl = 
  let fun f ds = (ds, depthy_of (depid_of ds)) in
    List.foldl insert_ds [] (List.map f dsl)
  end

(* Pretty-printing *)

fun pp_dep ppstrm (ds,dt) =
  let 
    open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm	
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
    fun pp_ds ds = case ds of
        DEP_NAMED(s,n) => pp_scouple (Lib.quote s, int_to_string n)
      | _ => raise ERR "pp_dep" "pp_ds"
    fun pp_nds ds = case ds of
        DEP_NAMED(s,n)   => add_string (int_to_string n)
      | DEP_CONJ((s,n),a) => pp_scouple (int_to_string n, quote_of_address a)
      | _ => raise ERR "pp_dep" "pp_nds"
    fun pp_thyentry (thy,l1,l2) = 
      pp_triple (add_string o Lib.quote, pp_l pp_nds, pp_l pp_nds) (thy,l1,l2)
    fun pp_dsl l = pp_l pp_thyentry l 
    fun pp_dt dt = 
      let fun pp_f (a,dsl) = 
        pp_couple (add_string o quote_of_address, pp_dsl o sort_dsl) (a,dsl)
      in
        pp_l pp_f (flatten_deptree [] dt)
      end
  in
    pp_couple (pp_ds,pp_dt) (ds,dt)
  end

(*---------------------------------------------------------------------------
   Reading dependencies from disk. 
 ----------------------------------------------------------------------------*)

(* Decoding the address *)

fun read_address a = 
       if a = ""                then [] 
  else if String.isPrefix "e" a then 
         let val n = string_to_int (String.extract (a, 1, NONE)) in 
           List.tabulate (n,(fn _ => DEP_RIGHT))
         end
  else if String.isPrefix "t" a then 
         map (fn #"L" => DEP_LEFT 
               | #"R" => DEP_RIGHT 
               | _    => raise ERR "read_address" "") (tl (explode a))
  else DEP_LEFT :: List.tabulate (string_to_int a,fn _ => DEP_RIGHT) 

(* Rebuild the tree from its leafs and their addresses. *)
fun build_tree leafl current_address = case leafl of
    []           => raise ERR "build_tree" "empty_tree"
  | [(a,dsl)]    => (DEP_LEAF dsl, [])
  | (a,dsl) :: m => 
      if a = current_address then (DEP_LEAF dsl, m)
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

fun read_depsort_named thy n = DEP_NAMED (thy,n)
fun read_depsort_conj thy (n,a) = DEP_CONJ ((thy,n), read_address a)

fun read_thyentry (thy,l1,l2) = 
  map (read_depsort_named thy) l1 @ map (read_depsort_conj thy) l2

fun read_leaf (a,l) = 
  (read_address a, List.concat (map read_thyentry l))

fun read_deptree dt = fst (build_tree (map read_leaf dt) [])

fun read_depsort_thy (thy,n) = DEP_NAMED(thy,n)
fun read_dep (ds,dt) = (read_depsort_thy ds,read_deptree dt) 

end
