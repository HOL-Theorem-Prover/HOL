structure Manager :> Manager =
struct

open Feedback Lib History Abbrev;

val ERR = mk_HOL_ERR "Manager";

(*---------------------------------------------------------------------------*)
(*  Add a notion of undo to the two kinds of proof manager                   *)
(*---------------------------------------------------------------------------*)

datatype proof0
       = GOALSTACK of goalStack.gstk History.history
       | GOALTREE of goalTree.gtree History.history
type tacmodifier = {tacm: tactic -> tactic,
                    ltacm : list_tactic -> list_tactic}

val id_tacm = {tacm = (fn t => t), ltacm = (fn lt => lt)}

datatype proof = PF of proof0 * tacmodifier

fun is_goalstack (GOALSTACK _) = true
  | is_goalstack otherwise = false;

fun is_goaltree (GOALTREE _) = true
  | is_goaltree otherwise = false;

(*---------------------------------------------------------------------------*)
(* Lists of proof attempts.                                                  *)
(*---------------------------------------------------------------------------*)

datatype proofs = PRFS of proof list;

exception NO_PROOFS;

fun initial_proofs() = PRFS[];

fun add p (PRFS L) = PRFS (p::L);

fun drop (PRFS (_::rst)) = PRFS rst
  | drop (PRFS []) = raise NO_PROOFS;

fun current_proof (PRFS (p::_)) = p
  | current_proof (PRFS []) = raise NO_PROOFS;

fun rotl (a::rst) = rst@[a]
  | rotl [] = raise ERR "rotl" "empty list"

fun rotate_proofs i (PRFS []) = PRFS []
  | rotate_proofs i (PRFS L) =
      if i<0 then raise ERR "rotate_proofs" "negative rotation"
      else if i > length L
           then raise ERR "rotate_proofs" "more rotations than proofs"
           else PRFS(funpow i rotl L);

(*---------------------------------------------------------------------------*)
(* Operations on PRFS.                                                       *)
(*---------------------------------------------------------------------------*)

fun hd_opr f (PRFS (p::t)) = PRFS(f p::t)
  | hd_opr f otherwise = raise NO_PROOFS;

fun hd_proj f (PRFS (p::_)) = f p
  | hd_proj f otherwise = raise NO_PROOFS;


(*---------------------------------------------------------------------------*)
(* Common operations on managers.                                            *)
(*---------------------------------------------------------------------------*)

fun apfst f (PF (x,y)) = PF (f x, y)
fun new_history_default obj = new_history{obj=obj, limit=15}
fun new_goalstack g tm f =
    PF (GOALSTACK(new_history_default (goalStack.new_goal g f)), tm);
fun new_goaltree g tm =
    PF (GOALTREE(new_history_default (goalTree.new_gtree g)), tm);
fun set_goal g tm = new_goalstack g tm Lib.I;  (* historical *)

fun backup (GOALSTACK s) = GOALSTACK(undo s)
  | backup (GOALTREE t) = GOALTREE(undo t);
val backup = apfst backup

fun set_backup i (PF(GOALSTACK s, tm)) = PF(GOALSTACK(set_limit s i),tm)
  | set_backup i (PF(GOALTREE t, tm)) = PF(GOALTREE (set_limit t i), tm)

fun redo (GOALSTACK s) = GOALSTACK(History.redo s)
  | redo (GOALTREE  t) = GOALTREE (History.redo t);
val redo = apfst redo

fun restore (GOALSTACK s) = GOALSTACK(History.restore s)
  | restore (GOALTREE  t) = GOALTREE (History.restore t);
val restore = apfst restore

fun save (GOALSTACK s) = GOALSTACK(History.save s)
  | save (GOALTREE t) = GOALTREE(History.save t)
val save = apfst save

fun forget_history (GOALSTACK s) = GOALSTACK(remove_past s)
  | forget_history (GOALTREE t) = GOALTREE (remove_past t)
val forget_history = apfst forget_history

fun expandf tac (PF(GOALSTACK s, tm)) =
    PF (GOALSTACK (apply(goalStack.expandf(#tacm tm tac)) s), tm)
  | expandf _ _ = raise ERR "expandf" "not implemented for goal trees";

fun expand tac (PF(GOALSTACK s, tm)) =
      PF (GOALSTACK (apply (goalStack.expand (#tacm tm tac)) s), tm)
  | expand tac (PF(GOALTREE t, tm)) =
      PF (GOALTREE (apply (goalTree.expand("",#tacm tm tac)) t), tm)

fun expand_listf ltac (PF(GOALSTACK s, tm)) =
    PF (GOALSTACK (apply (goalStack.expand_listf (#ltacm tm ltac)) s), tm)
  | expand_listf _ _ =
    raise ERR "expand_listf" "not implemented for goal trees";

fun expand_list ltac (PF(GOALSTACK s, tm)) =
    PF (GOALSTACK (apply (goalStack.expand_list (#ltacm tm ltac)) s), tm)
  | expand_list _ _ =
    raise ERR "expand_list" "not implemented for goal trees";

fun expandv (s,tac) (PF(GOALTREE t, tm)) =
     PF (GOALTREE (apply (goalTree.expand (s,#tacm tm tac)) t), tm)
   | expandv _ _ = raise ERR "expandv" "not implemented for goal stacks";

fun top_thm (PF(GOALSTACK s, _)) = project goalStack.extract_thm s
  | top_thm (PF(GOALTREE _, _)) = raise ERR "top_thm" "not implemented for goal trees";

fun initial_goal (PF(GOALSTACK s, _)) = project goalStack.initial_goal s
  | initial_goal (PF(GOALTREE t, _)) =
    goalTree.first_goal (History.initialValue t);

fun finalizer (PF(GOALSTACK s, _)) = project goalStack.finalizer s
  | finalizer gtree = raise ERR "finalizer" "not implemented for goal trees";

fun top_goal (PF(GOALSTACK s, _)) = project goalStack.top_goal s
  | top_goal (PF(GOALTREE t, _)) = project goalTree.first_goal t;

fun top_goals (PF(GOALSTACK s, _)) = project goalStack.top_goals s
  | top_goals (PF(GOALTREE t, _)) = project goalTree.all_goals t;

fun rotate i (PF(GOALSTACK s, tm)) =
      PF(GOALSTACK(apply (C goalStack.rotate i) s), tm)
  | rotate i (PF(GOALTREE t, _)) =
    raise ERR "rotate" "not implemented for goal trees";

fun flatn i (PF(GOALSTACK s, tm)) =
      PF(GOALSTACK(apply (C goalStack.flatn i) s), tm)
  | flatn i _ = raise ERR "flatn" "not implemented for goal trees";

fun restart (GOALSTACK s) = GOALSTACK (new_history_default (initialValue s))
  | restart (GOALTREE t) = GOALTREE (new_history_default (initialValue t));
val restart = apfst restart

(*---------------------------------------------------------------------------*)
(* Prettyprinting of goalstacks and goaltrees.                               *)
(*---------------------------------------------------------------------------*)

fun pp_proof (PF(GOALSTACK s, _)) = project goalStack.pp_gstk s
  | pp_proof (PF(GOALTREE t, _)) = project goalTree.pp_gtree t

val set_goal_pp = goalStack.set_goal_pp;
val std_goal_pp = goalStack.std_pp_goal;


(*---------------------------------------------------------------------------
 * Prettyprinting of proofs.
 *---------------------------------------------------------------------------*)

val enum = List.rev o Lib.enumerate 1;

val inactive_stack = Lib.can goalStack.extract_thm
val inactive_tree = null o goalTree.all_goals;

val pp_proofs =
   let open smpp
       val pr_goal = lift goalStack.pp_goal
       val pr_gtree = lift goalTree.pp_gtree
       val pr_thm = lift Parse.pp_thm
       fun pr1 ind (PF(GOALSTACK x, _)) =
            if (project inactive_stack x)
            then block Portable.CONSISTENT (2 + ind) (
                   add_string"Completed goalstack:" >> add_break(1,0) >>
                   pr_thm (project goalStack.extract_thm x)
                 )
            else
              block Portable.CONSISTENT (2 + ind) (
                   add_string"Incomplete goalstack:" >> add_break(1,0) >>
                   block Portable.CONSISTENT 0 (
                     add_string"Initial goal:" >> add_newline >>
                     pr_goal (project goalStack.initial_goal x)
                   ) >>
                   (if (project goalStack.is_initial x) then nothing
                    else
                      add_newline >> add_newline >>
                      add_string "Current goal:" >> add_break(1,0) >>
                      pr_goal (project goalStack.top_goal x))
              )
         | pr1 ind (PF(GOALTREE t, _)) =
            if (project inactive_tree t)
            then
              block Portable.CONSISTENT 2 (
                   add_string"Completed goaltree:" >> add_break(1,0) >>
                   project pr_gtree t
              )
            else
              block Portable.CONSISTENT 2 (
                  add_string"Incomplete goaltree:" >> add_break(1,0) >>
                  add_string"Initial goal:" >> add_newline >>
                  pr_gtree (History.initialValue t) >>
                  add_newline >>
                  add_string "Current goaltree:" >>
                  add_break(1,0) >>
                  project pr_gtree t
              )

       fun pr (PRFS extants) =
          let
            val len = length extants
          in
             if len = 0 then add_string"There are currently no proofs."
             else
               block Portable.CONSISTENT 2 (
                 add_string("Proof manager status:") >> add_break(1,0) >>
                 (case len of 1 => add_string "1 proof."
                            | n => add_string(int_to_string n^" proofs."))
               ) >> add_newline >>
               pr_list
                 (fn (i,x) =>
                     let val num_s = Int.toString i ^ ". "
                     in
                       block Portable.CONSISTENT 0 (
                         add_string num_s >> pr1 (size num_s) x
                       )
                     end
                 ) (add_newline >> add_newline)
                 (enum extants) >>
               add_newline
          end
   in
     fn pl => (block Portable.CONSISTENT 0 (pr pl))
   end;

val pp_proofs = Parse.mlower o pp_proofs

end (* Manager *)
