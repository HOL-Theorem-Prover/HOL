(*---------------------------------------------------------------------------*)
(* The programs here maintain a reference to an element of the proofs type.  *)
(* For purely functional operations, i.e., where no hidden state is being    *)
(* maintained, see the Manager structure.                                    *)
(*---------------------------------------------------------------------------*)

structure proofManagerLib :> proofManagerLib =
struct

open HolKernel Abbrev;

type proof = Manager.proof
type proofs = Manager.proofs

val chatting = goalStack.chatting;
fun say s = if !chatting then Lib.say s else ();

val the_proofs = ref (Manager.initial_proofs());

fun proofs() = !the_proofs;
fun top_proof() = Manager.current_proof(proofs());


fun new_goalstack g f =
   (the_proofs := Manager.add (Manager.new_goalstack g f) (proofs());
    proofs());

fun new_goaltree g =
   (the_proofs := Manager.add (Manager.new_goaltree g) (proofs());
    proofs());

fun set_goal g = new_goalstack g Lib.I;
fun set_goaltree g = new_goaltree g;

fun g q = set_goal([],Parse.Term q);
fun gt q = set_goaltree([],Parse.Term q);

fun add g = (say"Adding new proof..\n";
             the_proofs := Manager.add g (proofs());
             proofs());

fun backup () =
   (the_proofs := Manager.hd_opr Manager.backup (proofs());
    top_proof());

fun restore () =
   (the_proofs := Manager.hd_opr Manager.restore (proofs());
    top_proof());

fun save () =
   (the_proofs := Manager.hd_opr Manager.save (proofs());
    top_proof());

val b = backup;

fun set_backup i =
  (the_proofs := Manager.hd_opr (Manager.set_backup i) (proofs()));

fun forget_history () =
  (the_proofs := Manager.hd_opr (Manager.forget_history) (proofs()));

fun restart() =
   (the_proofs := Manager.hd_opr Manager.restart (proofs());
    top_proof());

local fun primdrop() = (the_proofs := Manager.drop (proofs()));
in
fun drop() = (primdrop(); say"OK..\n"; proofs())
        handle Manager.NO_PROOFS => proofs()
fun dropn i =
   if i<1 then (say"OK..\n"; proofs()) else (primdrop(); dropn (i-1))
   handle Manager.NO_PROOFS => proofs()
end;

fun expandf tac =
   (say "OK..\n";
    the_proofs := Manager.hd_opr (Manager.expandf tac) (proofs());
    top_proof())
  handle e => Raise e;

fun expand tac =
   (say "OK..\n";
    the_proofs := Manager.hd_opr (Manager.expand tac) (proofs());
    top_proof())
  handle e => Raise e;

fun expandv (s,tac) =
   (say "OK..\n";
    the_proofs := Manager.hd_opr (Manager.expandv (s,tac)) (proofs());
    top_proof())
  handle e => Raise e;

val e = expand;
val et = expandv;

val top_thm      = Manager.hd_proj Manager.top_thm o proofs;
val initial_goal = Manager.hd_proj Manager.initial_goal o proofs;
val top_goal     = Manager.hd_proj Manager.top_goal o proofs;
val top_goals    = Manager.hd_proj Manager.top_goals o proofs;

fun p () = Manager.hd_proj I (proofs())
        handle Manager.NO_PROOFS =>
         (say "No goalstack is currently being managed.\n";
          raise mk_HOL_ERR "proofManagerLib" "p" "")

val status = proofs;

fun rotate i =
  (the_proofs := Manager.hd_opr (Manager.rotate i) (proofs());
   top_proof());

val r = rotate;

fun rotate_proofs i =
   (the_proofs := Manager.rotate_proofs i (proofs());
    proofs());

val R = rotate_proofs;

val set_goal_pp  = Manager.set_goal_pp
val std_goal_pp  = Manager.std_goal_pp

val pp_proof = Manager.pp_proof
val pp_proofs = Manager.pp_proofs

end (* proofManagerLib *)
