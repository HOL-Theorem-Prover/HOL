(* ===================================================================== *)
(* FILE          : Tag.sml                                               *)
(* DESCRIPTION   : Theorem tagging (for oracles and other stuff)         *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : 1998                                                  *)
(* ===================================================================== *)

structure Tag :> Tag =
struct

open Lib Feedback

val ERR = mk_HOL_ERR "Tag";

(*---------------------------------------------------------------------------*)
(* A tag is represented by a pair (O,A) where O is a list of oracles         *)
(* (represented by strings) and A is a list of axioms (a list of references  *)
(* to strings). The axioms are used to track the use of axioms in proofs in  *)
(* the current theory.                                                       *)
(*---------------------------------------------------------------------------*)

datatype tag = TAG of string list * string Nonce.t list

fun dest_tag (TAG(O,A)) = (O, map Nonce.dest A)
fun oracles_of (TAG(O,_)) = O;
fun axioms_of  (TAG(_,A)) = A;

val empty_tag  = TAG ([],[])
val disk_only_tag  = TAG (["DISK_THM"],[])
fun ax_tag r = TAG ([],[r])

val isEmpty = equal empty_tag;
val isDisk = equal disk_only_tag;

(*---------------------------------------------------------------------------*)
(* Create a tag. A tag is a string with only printable characters (as        *)
(* defined by Char.isPrint) and without spaces.                              *)
(*---------------------------------------------------------------------------*)

fun read s =
 let open Substring
 in if isEmpty(dropl Char.isPrint (full s))
     then TAG ([s],[])
     else raise ERR "read"
           (Lib.quote s^" has unprintable characters")
 end;

(*---------------------------------------------------------------------------
      Merge two tags; read tags from disk
 ---------------------------------------------------------------------------*)

local fun smerge t1 [] = t1
        | smerge [] t2 = t2
        | smerge (t as ["DISK_THM"]) ["DISK_THM"] = t
        | smerge (l0 as s0::rst0) (l1 as s1::rst1) =
            case String.compare (s0,s1)
             of LESS    => s0::smerge rst0 l1
              | GREATER => s1::smerge l0 rst1
              | EQUAL   => s0::smerge rst0 rst1
in
fun merge (TAG(o1,ax1)) (TAG(o2,ax2)) = TAG(smerge o1 o2, Lib.union ax1 ax2)
fun read_disk_tag [] = disk_only_tag
  | read_disk_tag slist = TAG (smerge ["DISK_THM"] slist, [])
end;


(*---------------------------------------------------------------------------*)
(* In a theory file, the list of oracles gets dumped out as a list of        *)
(* strings. The axioms are not currently dumped, since they are being used   *)
(* only for ensuring that no out-of-date objects in the current theory       *)
(* become persistent.                                                        *)
(*---------------------------------------------------------------------------*)

fun pp_to_disk ppstrm (TAG (olist,_)) =
 let open Portable
   val {add_string,add_break,begin_block,end_block,...} = with_ppstream ppstrm
   val olist' = map Lib.mlquote olist
 in
    begin_block CONSISTENT 0;
    add_string "[";
      begin_block INCONSISTENT 1;
      pr_list add_string (fn () => add_string ",")
                         (fn () => add_break(1,0)) olist';
      end_block();
      add_string "]";
      end_block()
 end

(*---------------------------------------------------------------------------
     Prettyprint a tag (for interactive work).
 ---------------------------------------------------------------------------*)

local open Portable
      fun repl ch alist =
           String.implode (itlist (fn _ => fn chs => (ch::chs)) alist [])
in
fun pp_tag ppstrm (TAG (olist,axlist)) =
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
