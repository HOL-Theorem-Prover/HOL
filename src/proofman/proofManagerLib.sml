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
type tacmodifier = Manager.tacmodifier

val chatting = goalStack.chatting;
fun say s = if !chatting then Lib.say s else ();

local
  val proofs_slot : Manager.proofs Context.Data.slot =
      Context.Data.new
        {name = "proofmanager.proofs",
         empty = Manager.initial_proofs(),
         pp = fn _ => "<proofs>"}
in
  fun proofs () = Context.Data.get proofs_slot (Context.snapshot())
  val put_proofs = Context.Data.write proofs_slot
  val upd_proofs = Context.Data.modify proofs_slot
end
fun top_proof() = Manager.current_proof(proofs());


fun new_goalstack g tm f =
   (upd_proofs (Manager.add (Manager.new_goalstack g tm f));
    proofs());

fun new_goaltree g tm =
   (upd_proofs (Manager.add (Manager.new_goaltree g tm));
    proofs());

fun new_goalfrag g tm =
   (upd_proofs (Manager.add (Manager.new_goalfrag g tm));
    proofs());

fun set_goal g = new_goalstack g Manager.id_tacm Lib.I;
fun set_goaltree g = new_goaltree g Manager.id_tacm;
fun set_goalfrag g = new_goalfrag g Manager.id_tacm;

fun g q = set_goal([],Parse.Term q);
fun gt q = set_goaltree([],Parse.Term q);
fun gf q = set_goalfrag([],Parse.Term q);

fun add g = (say"Adding new proof..\n";
             upd_proofs (Manager.add g);
             proofs());

fun backup () =
   (upd_proofs (Manager.hd_opr Manager.backup);
    top_proof());

fun redo () =
   (upd_proofs (Manager.hd_opr Manager.redo);
    top_proof());

fun restore () =
   (upd_proofs (Manager.hd_opr Manager.restore);
    top_proof());

fun save () =
   (upd_proofs (Manager.hd_opr Manager.save);
    top_proof());

val b = backup;
val rd = redo;

fun set_backup i =
  upd_proofs (Manager.hd_opr (Manager.set_backup i));

fun forget_history () =
  upd_proofs (Manager.hd_opr Manager.forget_history);

fun restart() =
   (upd_proofs (Manager.hd_opr Manager.restart);
    top_proof());

local fun primdrop() = upd_proofs Manager.drop;
in
fun drop() = (primdrop(); say"OK..\n"; proofs())
        handle Manager.NO_PROOFS => proofs()
fun dropn i =
   if i<1 then (say"OK..\n"; proofs()) else (primdrop(); dropn (i-1))
   handle Manager.NO_PROOFS => proofs()
end;

fun drop_all () =
    let val v = Manager.initial_proofs()
    in put_proofs v; v
    end

fun expandf tac =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expandf tac));
    top_proof())
  handle e => Feedback.display_uncaught e;

fun expand tac =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expand tac));
    top_proof())
  handle e => Feedback.display_uncaught e;

fun expand_listf ltac =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expand_listf ltac));
    top_proof())
  handle e => Feedback.display_uncaught e;

fun expand_list ltac =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expand_list ltac));
    top_proof())
  handle e => Feedback.display_uncaught e;

fun expand_frag ftac =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expand_frag ftac));
    top_proof())
  handle e => Feedback.display_uncaught e;

fun expandv (s,tac) =
   (say "OK..\n";
    upd_proofs (Manager.hd_opr (Manager.expandv (s,tac)));
    top_proof())
  handle e => Feedback.display_uncaught e;

val elt = expand_list ;
fun eall tac = expand_list (Tactical.ALLGOALS tac) ;
fun eta tac = expand_list (Tactical.TRYALL tac) ;
fun enth tac i = expand_list (Tactical.NTH_GOAL tac i) ;
val e = expand;
val et = expandv;
val ef = expand_frag;

val top_thm      = Manager.hd_proj Manager.top_thm o proofs;
val initial_goal = Manager.hd_proj Manager.initial_goal o proofs;
val top_goal     = Manager.hd_proj Manager.top_goal o proofs;
val top_goals    = Manager.hd_proj Manager.top_goals o proofs;

fun p () = Manager.hd_proj I (proofs())
        handle Manager.NO_PROOFS =>
         (say "No goalstack is currently being managed.\n";
          raise mk_HOL_ERR "proofManagerLib" "p" "")

val status = proofs;

fun flatn i =
  (upd_proofs (Manager.hd_opr (Manager.flatn i));
   top_proof());

fun rotate i =
  (upd_proofs (Manager.hd_opr (Manager.rotate i));
   top_proof());

val r = rotate;

fun rotate_proofs i =
   (upd_proofs (Manager.rotate_proofs i);
    proofs());

val R = rotate_proofs;

val set_goal_pp  = Manager.set_goal_pp
val std_goal_pp  = Manager.std_goal_pp

val pp_proof = Manager.pp_proof
val pp_proofs = Manager.pp_proofs

(* Install the dump-on-failure hook used by boolLib.store_thm_at /
   holmakebuild.basic_prover: seed the proof manager with the failing
   goal so the dumped heap, when reloaded, presents that goal ready
   for interactive exploration. *)
val _ = boolLib.dump_setup_hook := (fn g => ignore (set_goal g))

end (* proofManagerLib *)
