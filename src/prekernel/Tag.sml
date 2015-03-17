(* ===================================================================== *)
(* FILE          : Tag.sml                                               *)
(* DESCRIPTION   : Theorem tagging (for oracles and other stuff)         *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(*                 Modified by Thibault Gauthier 2015                    *)
(* DATE          : 1998                                                  *)
(* ===================================================================== *)

structure Tag :> Tag =
struct

open Lib Feedback Dep

val ERR = mk_HOL_ERR "Tag";

(*---------------------------------------------------------------------------*)
(* A tag is represented by a pair (D,O,A) where O is a list of oracles       *)
(* (represented by strings) and A is a list of axioms (a list of references  *)
(* to strings). The axioms are used to track the use of axioms in proofs in  *)
(* the current theory. D represents a list of dependencies for each conjuncts*)
(* of the theorem.                                                           *)
(*---------------------------------------------------------------------------*)

datatype tag = TAG of dep * string list * string Nonce.t list

fun dest_tag (TAG(D,O,A)) = (O, map Nonce.dest A)
fun oracles_of (TAG(_,O,_)) = O
fun axioms_of  (TAG(_,_,A)) = A
fun dep_of (TAG(D,_,_)) = D

val empty_tag = TAG (empty_dep,[],[])
val disk_only_tag  = TAG (empty_dep,["DISK_THM"],[])
fun ax_tag r = TAG (empty_dep,[],[r])

fun isEmpty tg = null (oracles_of tg) andalso null (axioms_of tg)
fun isDisk tg = oracles_of tg = ["DISK_THM"] andalso null (axioms_of tg)

(*---------------------------------------------------------------------------
   Create a tag. A tag is a string with only printable characters (as        
   defined by Char.isPrint) and without spaces.                              
 ----------------------------------------------------------------------------*)

fun read s =
 let open Substring
 in if isEmpty(dropl Char.isPrint (full s))
     then TAG (empty_dep,[s],[])
     else raise ERR "read"
           (Lib.quote s^" has unprintable characters")
 end;

(*---------------------------------------------------------------------------
   Tag a theorem with the flag DEP_NAMED when it is saved. 
   Distinguish between saved and passed dependency trees.
 ----------------------------------------------------------------------------*)

fun give_dep d (TAG(_,O,A)) = TAG(d,O,A)

(*---------------------------------------------------------------------------
   Merge two tags. 
   Tracking conjuncts' dependencies require to treat specially CONJ and 
   CONJUNCT. Dependencies are not flattened in SPEC, GEN and Spec as we will 
   track conjuncts also under the quantifiers.
   Read tags from disk.
 ----------------------------------------------------------------------------*)

local fun smerge t1 [] = t1
        | smerge [] t2 = t2
        | smerge (t as ["DISK_THM"]) ["DISK_THM"] = t
        | smerge (l0 as s0::rst0) (l1 as s1::rst1) =
            case String.compare (s0,s1)
             of LESS    => s0::smerge rst0 l1
              | GREATER => s1::smerge l0 rst1
              | EQUAL   => s0::smerge rst0 rst1
in

fun collapse_dep (TAG(D,O,A)) = TAG(DEP_UNSAVED(collapse_deptree D),O,A)

fun merge (TAG(d1,o1,ax1)) (TAG(d2,o2,ax2)) = 
  let 
    val (dt1,dt2) = (deptree_of d1, deptree_of d2) 
    val dt = mk_deptree (dt1,dt2)
    val d = DEP_UNSAVED(collapse_deptree dt) 
  in
    TAG(d, smerge o1 o2, Lib.union ax1 ax2)
  end

fun merge_conj (TAG(d1,o1,ax1)) (TAG(d2,o2,ax2)) = 
  let 
    val (dt1,dt2) = (deptree_of d1, deptree_of d2) 
    val d = DEP_UNSAVED(mk_deptree (dt1,dt2)) 
  in
    TAG(d, smerge o1 o2, Lib.union ax1 ax2)
  end

fun merge_conjunct lr (TAG(D,O,A)) = 
  case (dt as deptree_of D) of
    DEP_NODE(dt1,dt2) => (
                         case lr of
                           DEP_LEFT  => DEP_UNSAVED dt1
                         | DEP_RIGHT => DEP_UNSAVED dt2
                         )
  | DEP_LEAF _        => DEP_UNSAVED dt

fun merge_conjunct1 tg = merge_conjunct DEP_LEFT tg
fun merge_conjunct2 tg = merge_conjunct DEP_RIGHT tg

fun read_disk_tag (d,[]) = TAG (read_dep d, ["DISK_THM"], [])
  | read_disk_tag (d,sl) = TAG (read_dep d, smerge ["DISK_THM"] sl, [])

end;


(*---------------------------------------------------------------------------
   In a theory file, the list of oracles gets dumped out as a list of        
   strings. The axioms are not currently dumped, since they are being used 
   only for ensuring that no out-of-date objects in the current theory       
   become persistent. Concrening dependencies, we only print the dependency  
   number inside the tag. Other informations are retrieved from the dependency 
   graph.                                                        
 ----------------------------------------------------------------------------*)

fun pp_to_disk ppstrm (TAG (d,olist,_)) =
  let 
    open Portable
    val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
    fun pp_sl l =   
      (
      begin_block CONSISTENT 0;
      add_string "[";
      begin_block INCONSISTENT 1;
      pr_list add_string (fn () => add_string ",")
                         (fn () => add_break(1,0)) l;
      end_block();
      add_string "]";
      end_block()
      )
   in
    (
    begin_block CONSISTENT 0;
      add_string "(";
      pp_dep ppstrm d;
      add_string ",";
      pp_sl (map Lib.mlquote olist);
      add_string ")";
    end_block()
    ) 
  end

(*---------------------------------------------------------------------------
     Prettyprint a tag (for interactive work).
 ---------------------------------------------------------------------------*)

local open Portable
      fun repl ch alist =
           String.implode (itlist (fn _ => fn chs => (ch::chs)) alist [])
in
fun pp_tag ppstrm (TAG (_,olist,axlist)) =
   let val {add_string,add_break,begin_block,end_block,...} =
       with_ppstream ppstrm
   in
     begin_block CONSISTENT 0;
      add_string "[oracles: ";
        begin_block INCONSISTENT 1;
        if !Globals.show_tags
        then pr_list add_string (fn () => add_string ",")
                                (fn () => add_break(1,0)) olist
        else add_string(repl #"#" olist); end_block();
      add_string "]";
      add_break(1,0);
      add_string "[axioms: ";
        begin_block INCONSISTENT 1;
        if !Globals.show_axioms
        then pr_list (add_string o Nonce.dest)
             (fn () => add_string ",") (fn () => add_break(1,0)) axlist
        else add_string(repl #"#" axlist); end_block();
      add_string "]";
     end_block()
   end
end;

end
