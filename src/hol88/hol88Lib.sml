(* ===================================================================== *)
(* FILE          : hol88Lib.sml                                          *)
(* DESCRIPTION   : Routines that provide compatibility with hol88.       *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)

structure hol88Lib :> hol88Lib =
struct

  type thm      = Thm.thm
  type term     = Term.term
  type hol_type = Type.hol_type
  type tactic   = Abbrev.tactic
  type conv     = Abbrev.conv

fun COMPAT_ERR{function,message} =
 Exception.HOL_ERR{origin_structure = "Compat",
               origin_function = function,
               message = message};

val setify = Lib.mk_set;
val find = Lib.first;
val match = Psyntax.match_term;
val prove_thm = Tactical.store_thm;
val string_of_int = Lib.int_to_string
val int_of_string = Lib.string_to_int;
fun save s = (Portable.output(Portable.std_out,
              "\n!! Not able to export images in MoscowML!!\n");   false);

fun assoc i alist =
   case (Lib.assoc1 i alist)
     of NONE => raise COMPAT_ERR{function = "assoc",
                                 message = ""}
      | (SOME x) => x;
fun rev_assoc i alist =
   case (Lib.assoc2 i alist)
     of NONE => raise COMPAT_ERR{function = "rev_assoc",
                                 message = ""}
      | (SOME x) => x;


val inst_type = Psyntax.type_subst;

val frees = rev o Term.free_vars;
val freesl = rev o Term.free_varsl;
val tyvars = rev o Term.type_vars_in_term
fun tyvarsl tm_list = Lib.itlist (Lib.union o tyvars) tm_list [];

fun GEN_ALL th =
   Lib.itlist Thm.GEN
              (Lib.set_diff (frees(Thm.concl th))
                            (freesl(Thm.hyp th)))
              th;

fun new_axiom(s,tm) = Theory.new_axiom(s,Dsyntax.gen_all tm);

val conjuncts = Dsyntax.strip_conj
val disjuncts = Dsyntax.strip_disj


fun new_prim_rec_definition (name,tm) =
  Psyntax.new_recursive_definition prim_recTheory.num_Axiom name tm

fun new_infix_prim_rec_definition(name,tm,prec) = let
in
  Psyntax.new_recursive_definition prim_recTheory.num_Axiom name tm before
  Lib.mesg true "Term not defined as infix - use set_fixity to do this"
end


val PROVE = Tactical.prove;
val prove_thm = Tactical.store_thm
val flat = Lib.flatten
val forall = Lib.all;


(*---------------------------------------------------------------------------
 * hol88 ancestry has different type than hol90 ancestry.
 * Plus, they return different answers: hol88 includes the current theory,
 * hol90 doesn't.
 *---------------------------------------------------------------------------*)
fun ancestry() = Theory.current_theory()::Theory.ancestry"-";

fun butlast L = Lib.fst (Lib.front_last L);

fun CB f g x = g(f x);
fun KI x y = Lib.K Lib.I x y;
infix 4 oo;
val op oo = fn (f,(g,h)) => fn x => f(g x, h x);
fun Co (f,g) x y = f (g y) x;    (* permutation-composition                *)

fun replicate x =
   let fun repl 0 = []
         | repl n = x::repl (n-1)
   in repl
   end;

fun GEN_REWRITE_RULE F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_RULE F
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2;

fun GEN_REWRITE_TAC F thlist1 thlist2 =
    Rewrite.GEN_REWRITE_TAC F
        (Rewrite.add_rewrites Rewrite.empty_rewrites thlist1) thlist2;

fun variant L tm =
   if Term.is_var tm
   then Term.variant L tm
   else if Term.is_const tm
        then Term.variant L (Term.mk_var (Term.dest_const tm))
        else raise COMPAT_ERR{function = "variant",
                              message = "not a variable or a constant"};

end;
