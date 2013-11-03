structure Hol_pp :> Hol_pp =
struct

open HolKernel Parse;

datatype theory
    = THEORY of string *
                {types       : (string * int) list,
                 consts      : (string * hol_type) list,
                 parents     : string list,
                 axioms      : (string * thm) list,
                 definitions : (string * thm) list,
                 theorems    : (string * thm) list}


(*--------------------------------------------------------------------------*
 * Prettyprint a theory for the user                                        *
 *--------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun pp_theory ppstrm (THEORY(name, {parents, types, consts,
                                    axioms,definitions,theorems})) =
let val {add_string,add_break,begin_block,end_block, add_newline,
         flush_ppstream,...} = Portable.with_ppstream ppstrm
  val pp_thm = pp_thm ppstrm
  val pp_type = pp_type ppstrm
  fun nl2() = (add_newline();add_newline());
  fun vspace l = if null l then () else nl2();
  fun vblock(header, ob_pr, obs) =
    if null obs then ()
    else
      (begin_block CONSISTENT 4;
       add_string (header^":");
       add_newline();
       Portable.pr_list
         ob_pr
         (fn () => ())
         add_newline
         obs;
       end_block())
  fun pr_thm (heading, ths) =
    vblock(heading,
      (fn (s,th) => (begin_block CONSISTENT 0;
                     add_string s; add_newline();
                     add_string "  ";
                     pp_thm th; end_block())),
      Listsort.sort (inv_img_cmp #1 String.compare) ths)
  val longest_const_size =
      List.foldl (fn ((s,_),i) => Int.max(size s, i)) 0
                 consts
in
    begin_block CONSISTENT 0;
    add_string ("Theory: "^name); nl2();
    vblock ("Parents", add_string, Listsort.sort String.compare parents); nl2();
    vblock ("Type constants",
     (fn (name,arity) =>
         (add_string name; add_string (" "^Lib.int_to_string arity))),
     types)
      ;
    vspace types;
    vblock ("Term constants",
      (fn (name,htype)
        => (begin_block CONSISTENT 0;
            add_string name;
            add_string (CharVector.tabulate(longest_const_size + 3 - size name,
                                            K #" "));
            pp_type htype;
            end_block())),
      consts)
      ;
    vspace consts;
    pr_thm ("Axioms", axioms); vspace axioms;
    pr_thm ("Definitions", definitions); vspace definitions;
    pr_thm ("Theorems", theorems);
    end_block()
 end;

end
