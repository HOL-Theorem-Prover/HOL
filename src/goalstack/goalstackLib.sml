(*----------------------------------------------------------------------
 * The "functions" here maintain a reference to an element of the 
 * proofs type. For example, "set_goal" silently modifies the 
 * current proofs to have the new goalstack as the focus of
 * subsequent operations. For purely functional operations, i.e., 
 * where no hidden state is being maintained, use the "Functional" 
 * structure above.
 *-----------------------------------------------------------------------*)

structure goalstackLib :> goalstackLib = 
struct


open HolKernel;

type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic
type goal = Abbrev.goal
type goalstack = GoalstackPure.goalstack
type proofs = GoalstackPure.proofs
type 'a quotation = 'a frag list

val the_proofs = ref (GoalstackPure.initial_proofs());

fun proofs() = (!the_proofs);

fun set_goal g = 
   (the_proofs := GoalstackPure.add (GoalstackPure.set_goal g) (proofs());
    proofs());

fun g flist = set_goal([],Parse.Term flist);

fun add g = (say"Adding new proof..\n";
             the_proofs := GoalstackPure.add g (proofs());
             proofs());

fun backup () = 
   (the_proofs := GoalstackPure.hd_opr GoalstackPure.backup (proofs());
    GoalstackPure.current_goalstack(proofs()));

val b = backup;
fun set_backup i = 
  (the_proofs := GoalstackPure.hd_opr (GoalstackPure.set_backup i) (proofs()));

fun restart() = 
   (the_proofs := GoalstackPure.hd_opr GoalstackPure.restart (proofs());
    GoalstackPure.current_goalstack(proofs()));

local fun primdrop() = (the_proofs := GoalstackPure.drop (proofs()));
in 
fun drop() = (primdrop(); say"OK..\n"; proofs())
        handle GoalstackPure.NO_PROOFS => proofs()
fun dropn i =
   if (i<1) then (say"OK..\n"; proofs()) else (primdrop(); dropn (i-1)) 
   handle GoalstackPure.NO_PROOFS => proofs()
end;

fun expandf tac = 
   (say "OK..\n";
    the_proofs := GoalstackPure.hd_opr (GoalstackPure.expandf tac) (proofs());
    GoalstackPure.current_goalstack(proofs()))
  handle e => Exception.Raise e;

fun expand tac = 
   (say "OK..\n";
    the_proofs := GoalstackPure.hd_opr (GoalstackPure.expand tac) (proofs());
    GoalstackPure.current_goalstack(proofs()))
  handle e => Exception.Raise e;

val e = expand;

val top_thm      = GoalstackPure.hd_proj GoalstackPure.top_thm o proofs;
val initial_goal = GoalstackPure.hd_proj GoalstackPure.initial_goal o proofs;
val top_goal     = GoalstackPure.hd_proj GoalstackPure.top_goal o proofs;
val top_goals    = GoalstackPure.hd_proj GoalstackPure.top_goals o proofs;

fun p () = GoalstackPure.hd_proj I (proofs())
        handle GoalstackPure.NO_PROOFS => 
         (say "No goalstack is currently being managed.\n"; 
          raise HOL_ERR{origin_structure = "goalstackLib",
                        origin_function = "p", message = ""});
val status = proofs;

fun rotate i = 
  (the_proofs := GoalstackPure.hd_opr (GoalstackPure.rotate i) (proofs());
   GoalstackPure.current_goalstack(proofs()));
val r = rotate;

fun rotate_proofs i = 
   (the_proofs := GoalstackPure.rotate_proofs i (proofs()); 
    proofs());
val R = rotate_proofs;

val set_goal_pp  = GoalstackPure.set_goal_pp
val std_goal_pp  = GoalstackPure.std_goal_pp

val pp_goalstack = GoalstackPure.pp_goalstack
val pp_proofs = GoalstackPure.pp_proofs

end; (* Goalstack *)
