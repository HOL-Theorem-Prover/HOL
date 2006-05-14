(* ===================================================================== *)
(* FILE          : Tag.sml                                               *)
(* DESCRIPTION   : Theorem tagging (for oracles and other stuff)         *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : 1998                                                  *)
(* MODIFIED      : July 2000, Konrad Slind                               *)
(* ===================================================================== *)

structure Tag : RawTag =
struct

open Lib Feedback KernelTypes

val ERR = mk_HOL_ERR "Tag";

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
 in if isEmpty(dropl Char.isGraph (all s))
     then TAG ([s],[])
     else raise ERR "read" 
           (Lib.quote s^" has embedded spaces or unprintable characters")
 end;

(*---------------------------------------------------------------------------
      Merge two tags
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
fun read_disk_tag s  = 
     if s = "" then disk_only_tag
               else TAG (smerge ["DISK_THM"] (Lib.words2 " " s), [])
end;


(*---------------------------------------------------------------------------*
 * In a theory file, the list of oracles gets dumped out as a string with    *
 * spaces between the constituents. The axioms are not currently dumped,     *
 * since they are being used only for ensuring that no out-of-date objects   *
 * become persistent.                                                        *
 *---------------------------------------------------------------------------*)

local fun spaces [] = ["\""]
        | spaces [x] = [x,"\""]
        | spaces (x::rst) = x::" "::spaces rst
      open Portable
in
fun pp_to_disk ppstrm (TAG (olist,_)) = 
    add_string ppstrm (String.concat ("\""::spaces olist))
end;
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
        then pr_list (add_string o !)
             (fn () => add_string ",") (fn () => add_break(1,0)) axlist
        else add_string(repl #"#" axlist); end_block();
      add_string "]"; 
     end_block()
   end
end;

end;
