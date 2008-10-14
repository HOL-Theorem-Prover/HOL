structure goalTree :> goalTree =
struct

open HolKernel Abbrev Tactical

val ERR = mk_HOL_ERR "goalTree" ;

datatype gtree = vGoal of goal
               | vAtom of string * tactic
               | vThen of gtree * gtree
               | vThenl of gtree * gtree list;

fun new_gtree g = vGoal g;

fun is_vGoal (vGoal _) = true
  | is_vGoal otherwise = false;

(*---------------------------------------------------------------------------*)
(* Apply a function to the elements in a list until it succeeds.             *)
(*---------------------------------------------------------------------------*)

fun apply_once f [] acc = NONE
  | apply_once f (h::t) acc =
     case f h 
      of NONE => apply_once f t (h::acc)
       | SOME h' => SOME (rev acc @ (h'::t));

(*---------------------------------------------------------------------------*)
(* Apply tactic only at first goal in tree.                                  *)
(*---------------------------------------------------------------------------*)

fun expand_opt (s,t) (vGoal g) = 
      SOME (case Tactical.VALID t g
            of ([],f)  => vAtom(s,t)
             | ([x],f) => vThen(vAtom(s,t),vGoal x)
             | (gl,f)  => vThenl(vAtom(s,t),map vGoal gl))
  | expand_opt p (vAtom _) = NONE
  | expand_opt p (vThen(t1,t2)) = 
     (case expand_opt p t1
        of SOME t1' => SOME (vThen(t1',t2))
         | NONE => case expand_opt p t2 
                    of NONE => NONE 
                     | SOME t2' => SOME(vThen(t1,t2')))
  | expand_opt p (vThenl(t1,tlist)) =
     case expand_opt p t1
      of SOME t1' => SOME (vThenl(t1',tlist))
       | NONE => case apply_once (expand_opt p) tlist []
                  of NONE => NONE
                   | SOME tlist' => SOME (vThenl(t1,tlist'));

fun expand p gtree =
  case expand_opt p gtree
   of NONE => raise ERR "expand" "no goals left"
    | SOME gtree' => gtree';

(*---------------------------------------------------------------------------*)
(* Find first goal in tree.                                                  *)
(*---------------------------------------------------------------------------*)

fun first_opt f [] = NONE
  | first_opt f (h::t) = case f h of NONE => first_opt f t | x => x;

fun first_goal_opt (vGoal g) = SOME g
  | first_goal_opt (vAtom _) = NONE
  | first_goal_opt (vThen(t1,t2)) = 
     (case first_goal_opt t1 of NONE => first_goal_opt t2 | x => x)
  | first_goal_opt (vThenl(t1,tlist)) =
     case first_goal_opt t1
      of NONE => first_opt first_goal_opt tlist
       | x => x

fun first_goal gtree = 
  case first_goal_opt gtree
   of NONE => raise ERR "first_goal" "no goals left"
    | SOME g => g;

(*---------------------------------------------------------------------------*)
(* List all remaining goals in tree                                          *)
(*---------------------------------------------------------------------------*)

fun all_goals (vGoal g) = [g]
  | all_goals (vAtom _) = []
  | all_goals (vThen(t1,t2)) = all_goals t1 @ all_goals t2
  | all_goals (vThenl(t1,tlist)) = all_goals t1 @ flatten (map all_goals tlist)


fun tactic_of (vGoal _) = ALL_TAC
  | tactic_of (vAtom(_,t)) = t
  | tactic_of (vThen(vt1,vt2)) = tactic_of vt1 THEN tactic_of vt2
  | tactic_of (vThenl(vt1,vtl)) = tactic_of vt1 THENL map tactic_of vtl;

fun pp_gtree ppstrm =
 let open Portable
     val {add_break,add_newline,add_string,begin_block,end_block,...} 
       = Portable.with_ppstream ppstrm
     val pp_goal = goalStack.pp_goal ppstrm
     val pp_slist = pr_list add_string (fn () => ())
                            (fn () => add_break(1,0))
     fun pp (vAtom (s,t)) = 
        if s="" then add_string "<anonymous>" 
        else
        (begin_block INCONSISTENT 0;
         pp_slist (String.tokens Char.isSpace s);
         end_block())
       | pp (vGoal g) = pp_goal g
       | pp (vThen(vt1,vt2)) = 
          let in 
             begin_block CONSISTENT 1;
             pp vt1; add_string " THEN"; add_break (1,0);
             pp vt2;
             end_block()
          end
       | pp (vThenl(vt,tlist)) = 
          let in 
             begin_block CONSISTENT 1;
             pp vt; add_string " THENL"; add_break (1,0);
             add_string "[";
             begin_block CONSISTENT 0;
             pr_list pp (fn () => add_string",")
                        (fn () => add_break(1,0))
                     tlist;
             end_block();
             add_string "]";
             end_block()
          end
 in pp
 end;

end
