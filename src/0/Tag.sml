(*---------------------------------------------------------------------------*
 * Oracles as ordered lists of strings, and axioms as lists of string refs.  *
 *---------------------------------------------------------------------------*)

structure Tag :> Tag =
struct

open Lib;

fun TAG_ERR f s = 
 Exception.HOL_ERR{origin_structure = "Tag",
                   origin_function = f, message = s};


datatype tag = TAG of string list * string ref list

fun axioms_of (TAG(_,axlist)) = axlist;

fun is_std (TAG ([],[])) = true 
  | is_std (TAG ([],_)) = not(!Globals.show_axioms)
  | is_std _ = false;

(*---------------------------------------------------------------------------*
 * Create a tag. The input string should be a contiguous sequence of         *
 * printable non-white-space characters.  Right now, we are lax at enforcing *
 * such restrictions.                                                        *
 *---------------------------------------------------------------------------*)

local fun reserved_oracle ""        = true
  | reserved_oracle "MK_THM"        = true
  | reserved_oracle "ValidityCheck" = true
  | reserved_oracle _               = false
in
fun read s = 
   if (reserved_oracle s) 
    then raise TAG_ERR "read" (Lib.quote s^" is reserved")
    else case (Lib.words2 " " s)
           of [s1] => TAG ([s1],[])
            |  _  => raise TAG_ERR "read" "too many spaces"
end;


 fun smerge t1 [] = t1
   | smerge [] t2 = t2 
   | smerge (l0 as s0::rst0) (l1 as s1::rst1) = 
       case String.compare (s0,s1)
         of LESS    => s0::smerge rst0 l1
          | GREATER => s1::smerge l0 rst1
          | EQUAL   => s0::smerge rst0 rst1;


 fun merge (TAG(o1,ax1)) (TAG(o2,ax2)) = TAG(smerge o1 o2, Lib.union ax1 ax2);


open Portable;

 local fun repl ch alist = String.implode 
                (itlist (fn _ => fn chs => (ch::chs)) alist [])
 in
 fun pp ppstrm (TAG (olist,axlist)) = 
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


(*---------------------------------------------------------------------------*
 * In a theory file, the list of oracles gets dumped out as a string with    *
 * spaces between the constituents. The axioms are not currently dumped,     *
 * since they are being used only for ensuring that no out-of-date objects   *
 * become persistent.                                                        *
 *---------------------------------------------------------------------------*)

 fun spaces [] = ["\""]
   | spaces [x] = [x,"\""]
   | spaces (x::rst) = x::" "::spaces rst;

 fun pp_to_disk ppstrm (TAG (olist,_)) = 
    add_string ppstrm (String.concat ("\""::spaces olist));


fun read_disk_tag "" = TAG([],[])
  | read_disk_tag s  = TAG (Lib.words2 " " s, [])

(*---------------------------------------------------------------------------*
 * Information hiding in lieu of a real module system.                       *
 *---------------------------------------------------------------------------*)
local val std       = TAG ([],[])
      val mk_thm    = TAG (["MK_THM"],[])
      val valid_tac = TAG (["ValidityCheck"],[])
      fun mk_ax r   = TAG ([],[r])
      val used = ref false
in
  fun init r1 r2 r3 r4 r5 =
    if !used then ()
    else (r1 := std; r2 := mk_thm; r3 := valid_tac; 
          r4 := read_disk_tag; r5 := mk_ax; used := true)
end;


end;
