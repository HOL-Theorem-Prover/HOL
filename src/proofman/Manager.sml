structure Manager :> Manager =
struct

open Feedback Lib History Abbrev;

val ERR = mk_HOL_ERR "Manager";

(*---------------------------------------------------------------------------*)
(*  Add a notion of undo to the two kinds of proof manager                   *)
(*---------------------------------------------------------------------------*)

datatype proof = GOALSTACK of goalStack.gstk history
               | GOALTREE of goalTree.gtree history;

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

fun new_history_default obj = new_history{obj=obj, limit=15}
fun new_goalstack g f = GOALSTACK(new_history_default (goalStack.new_goal g f));
fun new_goaltree g  = GOALTREE(new_history_default (goalTree.new_gtree g));
fun set_goal g = new_goalstack g Lib.I;  (* historical *)

fun backup (GOALSTACK s) = GOALSTACK(undo s)
  | backup (GOALTREE t) = GOALTREE(undo t);

fun set_backup i (GOALSTACK s) = GOALSTACK(set_limit s i)
  | set_backup i (GOALTREE t) = GOALTREE (set_limit t i);

fun restore (GOALSTACK s) = GOALSTACK(History.restore s)
  | restore (GOALTREE  t) = GOALTREE (History.restore t);

fun save (GOALSTACK s) = GOALSTACK(History.save s)
  | save (GOALTREE t) = GOALTREE(History.save t);

fun forget_history (GOALSTACK s) = GOALSTACK(remove_past s)
  | forget_history (GOALTREE t) = GOALTREE (remove_past t);

fun expandf tac (GOALSTACK s) = GOALSTACK (apply (goalStack.expandf tac) s)
  | expandf _ _ = raise ERR "expandf" "not implemented for goal trees";

fun expand tac (GOALSTACK s) = GOALSTACK (apply (goalStack.expand tac) s)
  | expand tac (GOALTREE t) = GOALTREE (apply (goalTree.expand("",tac)) t);

fun expand_listf ltac (GOALSTACK s) =
    GOALSTACK (apply (goalStack.expand_listf ltac) s)
  | expand_listf _ _ =
    raise ERR "expand_listf" "not implemented for goal trees";

fun expand_list ltac (GOALSTACK s) =
    GOALSTACK (apply (goalStack.expand_list ltac) s)
  | expand_list _ _ =
    raise ERR "expand_list" "not implemented for goal trees";

fun expandv (s,tac) (GOALTREE t) =
     GOALTREE (apply (goalTree.expand (s,tac)) t)
   | expandv _ _ = raise ERR "expandv" "not implemented for goal stacks";

fun top_thm (GOALSTACK s) = project goalStack.extract_thm s
  | top_thm (GOALTREE _) = raise ERR "top_thm" "not implemented for goal trees";

fun initial_goal (GOALSTACK s) = project goalStack.initial_goal s
  | initial_goal (GOALTREE t) = goalTree.first_goal (History.initialValue t);

fun finalizer (GOALSTACK s) = project goalStack.finalizer s
  | finalizer gtree = raise ERR "finalizer" "not implemented for goal trees";

fun top_goal (GOALSTACK s) = project goalStack.top_goal s
  | top_goal (GOALTREE t) = project goalTree.first_goal t;

fun top_goals (GOALSTACK s) = project goalStack.top_goals s
  | top_goals (GOALTREE t) = project goalTree.all_goals t;

fun rotate i (GOALSTACK s) = GOALSTACK(apply (C goalStack.rotate i) s)
  | rotate i (GOALTREE t) = raise ERR "rotate"
                               "not implemented for goal trees";

fun flatn i (GOALSTACK s) = GOALSTACK(apply (C goalStack.flatn i) s)
  | flatn i (GOALTREE t) = raise ERR "flatn"
                               "not implemented for goal trees";

fun restart (GOALSTACK s) = GOALSTACK (new_history_default (initialValue s))
  | restart (GOALTREE t) = GOALTREE (new_history_default (initialValue t));

(*---------------------------------------------------------------------------*)
(* Prettyprinting of goalstacks and goaltrees.                               *)
(*---------------------------------------------------------------------------*)

fun pp_proof (GOALSTACK s) = project goalStack.pp_gstk s
  | pp_proof (GOALTREE t) = project goalTree.pp_gtree t

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
       fun pr1 ind (GOALSTACK x) =
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
         | pr1 ind (GOALTREE t) =
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
