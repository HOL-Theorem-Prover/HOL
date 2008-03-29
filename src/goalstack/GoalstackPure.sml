structure GoalstackPure :> GoalstackPure =
struct

open Feedback Lib History Abbrev;

val ERR = mk_HOL_ERR "GoalstackPure";

fun rotl (a::rst) = rst@[a]
  | rotl [] = raise ERR "rotl" "empty list"

(*---------------------------------------------------------------------------
 *  Add a notion of "undo" to the bare type of gstks.
 *---------------------------------------------------------------------------*)

datatype goalstack = GOALSTACK of Bwd.gstk history;

fun prim_set_goal g f = 
     GOALSTACK(new_history{obj=Bwd.new_goal g f, limit=15});

fun set_goal g = prim_set_goal g Lib.I;

fun backup (GOALSTACK s) = GOALSTACK(undo s);
fun set_backup i (GOALSTACK s) = GOALSTACK(set_limit s i);
fun expandf tac (GOALSTACK s) = GOALSTACK (apply (C Bwd.expandf tac) s);
fun expand tac (GOALSTACK s) = GOALSTACK (apply (C Bwd.expand tac) s);

fun top_thm (GOALSTACK s) = project Bwd.extract_thm s;
fun initial_goal (GOALSTACK s) = project Bwd.initial_goal s;
fun finalizer (GOALSTACK s) = project Bwd.finalizer s;
fun top_goal (GOALSTACK s) = project Bwd.top_goal s;
fun top_goals (GOALSTACK s) = project Bwd.top_goals s;
fun rotate i (GOALSTACK s) = GOALSTACK(apply (C Bwd.rotate i) s);

fun restart x = prim_set_goal (initial_goal x) (finalizer x);



(*---------------------------------------------------------------------------
 * Prettyprinting of goalstacks.
 *---------------------------------------------------------------------------*)

fun pp_goalstack ppstrm (GOALSTACK g) = project (Bwd.pp_gstk ppstrm) g;
val set_goal_pp = Bwd.set_goal_pp;
val std_goal_pp = Bwd.std_pp_goal;

(*---------------------------------------------------------------------------
 * A type that collects groups of goalstacks into one place.
 *---------------------------------------------------------------------------*)

datatype proofs = PRFS of goalstack list;

exception NO_PROOFS;
fun initial_proofs() = PRFS[];

fun add gstk (PRFS L) = PRFS (gstk::L);

fun drop (PRFS (h::rst)) = PRFS rst
  | drop (PRFS []) = raise NO_PROOFS;

fun current_goalstack (PRFS (h::_)) = h
  | current_goalstack (PRFS []) = raise NO_PROOFS;

fun rotate_proofs i (PRFS []) = PRFS []
  | rotate_proofs i (PRFS L) =
      if i<0 then raise ERR "rotate_proofs" "negative rotation"
      else if i > length L
           then raise ERR "rotate_proofs" "more rotations than proofs"
           else PRFS(funpow i rotl L);

(*---------------------------------------------------------------------------
 * Operations on PRFS.
 *---------------------------------------------------------------------------*)

fun hd_opr f (PRFS (h::rst)) = PRFS(f h::rst)
  | hd_opr f (PRFS[]) = raise NO_PROOFS;

fun hd_proj f (PRFS (h::_)) = f h
  | hd_proj f (PRFS[]) = raise NO_PROOFS;


(*---------------------------------------------------------------------------
 * Prettyprinting of proofs.
 *---------------------------------------------------------------------------*)

fun enumerate L = snd(rev_itlist (fn x => fn (n,A) => (n+1, (n,x)::A))
                                 L (1,[]));
val inactive = can Bwd.extract_thm

fun pp_proofs ppstrm =
   let val pr_goal = Bwd.pp_goal ppstrm
       val pr_thm = Parse.pp_thm ppstrm
       val {add_string, add_break, begin_block, end_block, add_newline, ...} =
                     Portable.with_ppstream ppstrm
       fun pr1 (GOALSTACK x) =
            if (project inactive x)
            then (begin_block Portable.CONSISTENT 2;
                  add_string"Completed:";  add_break(1,0);
                  pr_thm (project Bwd.extract_thm x);
                  end_block())
            else (begin_block Portable.CONSISTENT 2;
                  add_string"Incomplete:";   add_break(1,0);
                  add_string"Initial goal:"; add_break(1,0);
                  pr_goal (project Bwd.initial_goal x);
                  if (project Bwd.is_initial x)
                  then ()
                  else (add_newline(); add_string"Current goal:";
                        add_break(1,0);
                        pr_goal (project Bwd.top_goal x));
                  end_block())
       fun pr (PRFS extants) =
          let val len = length extants
          in if (len = 0)
             then add_string"There are currently no proofs."
             else ( begin_block Portable.CONSISTENT 2;
                    add_string("Proof manager status:");  add_break(1,0);
                    (case len of 1 => add_string "1 proof."
                          | n => add_string(int_to_string n^" proofs."));
                    end_block(); add_newline();
                    map (fn (i,x) =>
                          (begin_block Portable.CONSISTENT 0;
                           add_string(int_to_string i^". ");
                           pr1 x;
                          end_block(); add_newline()))
                        (enumerate extants);
                    ())
          end
   in fn pl => (begin_block Portable.CONSISTENT 0;
                pr pl; end_block())
   end;

end (* GoalstackPure *)
