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

fun new_goalstack g f 
  = GOALSTACK(new_history{obj=goalStack.new_goal g f, limit=15});

fun new_goaltree g 
  = GOALTREE(new_history{obj=goalTree.new_gtree g, limit=15});

fun set_goal g = new_goalstack g Lib.I;  (* historical *)

fun backup (GOALSTACK s) = GOALSTACK(undo s)
  | backup (GOALTREE t) = GOALTREE(undo t);

fun set_backup i (GOALSTACK s) = GOALSTACK(set_limit s i)
  | set_backup i (GOALTREE t) = GOALTREE (set_limit t i);

fun expandf tac (GOALSTACK s) = GOALSTACK (apply (goalStack.expandf tac) s)
  | expandf _ _ = raise ERR "expandf" "not implemented for goal trees";

fun expand tac (GOALSTACK s) = GOALSTACK (apply (goalStack.expand tac) s)
  | expand tac (GOALTREE t) = GOALTREE (apply (goalTree.expand("",tac)) t);

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

fun restart (x as GOALSTACK _) = new_goalstack (initial_goal x) (finalizer x)
  | restart (x as GOALTREE _) = new_goaltree (initial_goal x);


(*---------------------------------------------------------------------------*)
(* Prettyprinting of goalstacks and goaltrees.                               *)
(*---------------------------------------------------------------------------*)

fun pp_proof ppstrm (GOALSTACK s) = project (goalStack.pp_gstk ppstrm) s
  | pp_proof ppstrm (GOALTREE t) = project(goalTree.pp_gtree ppstrm) t

val set_goal_pp = goalStack.set_goal_pp;
val std_goal_pp = goalStack.std_pp_goal;


(*---------------------------------------------------------------------------
 * Prettyprinting of proofs.
 *---------------------------------------------------------------------------*)

val enum = List.rev o Lib.enumerate 1;

val inactive_stack = Lib.can goalStack.extract_thm
val inactive_tree = null o goalTree.all_goals;

fun pp_proofs ppstrm =
   let val pr_goal = goalStack.pp_goal ppstrm
       val pr_gtree = goalTree.pp_gtree ppstrm
       val pr_thm = Parse.pp_thm ppstrm
       val {add_string, add_break, begin_block, end_block, add_newline, ...} =
                     Portable.with_ppstream ppstrm
       fun pr1 (GOALSTACK x) =
            if (project inactive_stack x)
            then (begin_block Portable.CONSISTENT 2;
                  add_string"Completed goalstack:"; add_break(1,0);
                  pr_thm (project goalStack.extract_thm x);
                  end_block())
            else (begin_block Portable.CONSISTENT 2;
                  add_string"Incomplete goalstack:"; add_break(1,0);
                  add_string"Initial goal:"; add_break(1,0);
                  pr_goal (project goalStack.initial_goal x);
                  if (project goalStack.is_initial x)
                  then ()
                  else (add_newline(); add_string "Current goal:";
                        add_break(1,0);
                        pr_goal (project goalStack.top_goal x));
                  end_block())
         | pr1 (GOALTREE t) = 
            if (project inactive_tree t)
            then (begin_block Portable.CONSISTENT 2;
                  add_string"Completed goaltree:"; add_break(1,0);
                  project pr_gtree t;
                  end_block())
            else (begin_block Portable.CONSISTENT 2;
                  add_string"Incomplete goaltree:"; add_break(1,0);
                  add_string"Initial goal:"; add_break(1,0);
                  pr_gtree (History.initialValue t);
                  add_newline(); 
                  add_string "Current goaltree:";
                  add_break(1,0);
                  project pr_gtree t;
                  end_block())

       fun pr (PRFS extants) =
          let val len = length extants
          in if len = 0
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
                        (enum extants);
                    ())
          end
   in fn pl => (begin_block Portable.CONSISTENT 0;
                pr pl; end_block())
   end;

end (* Manager *)
