(*---------------------------------------------------------------------------*)
(* Goalstacks, with no idea of undo.                                         *)
(*---------------------------------------------------------------------------*)

structure goalStack :> goalStack =
struct

open HolKernel Abbrev;

infix 0 before;

val ERR = mk_HOL_ERR "goalStack";

val show_nsubgoals = ref 10;
val chatting = ref true;

val _ = Feedback.register_trace ("Subgoal number", show_nsubgoals, 10000);
val _ = Feedback.register_btrace("goalstack chatting", chatting);

fun say s = if !chatting then Lib.say s else ();

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")

fun printthm th = if !chatting then Parse.print_thm th else ()

fun rotl (a::rst) = rst@[a]
  | rotl [] = raise ERR "rotl" "empty list"

fun rotr lst =
  let val (front,back) = Lib.front_last lst
  in (back::front)
  end
  handle HOL_ERR _ => raise ERR "rotr" "empty list"


(* GOALSTACKS *)
(*---------------------------------------------------------------------------
 * A goalstack is a stack of (goal list, validation_function) records. Each
 * goal in the goal list is a (term list, term) pair. The validation
 * function is a function from a list of theorems to a theorem. It must be
 * that the number of goals in the goal list is equal to the number of
 * formal parameters in the validation function. Unfortunately, the type
 * system of ML is not strong enough to check that.
 ---------------------------------------------------------------------------*)

type tac_result = {goals      : goal list,
                   validation : thm list -> thm}

(*---------------------------------------------------------------------------
   Need both initial goal and final theorem in PROVED case, because
   finalizer can take a theorem achieving the original goal and
   transform it into a second theorem. Destructing that second theorem
   wouldn't deliver the original goal.
 ---------------------------------------------------------------------------*)

datatype proposition = POSED of goal
                     | PROVED of thm * goal;

datatype gstk = GSTK of {prop  : proposition,
                         final : thm -> thm,
                         stack : tac_result list}


fun depth(GSTK{stack,...}) = length stack;

fun is_initial(GSTK{prop=POSED g, stack=[], ...}) = true
  | is_initial _ = false;

fun top_goals(GSTK{prop=POSED g, stack=[], ...}) = [g]
  | top_goals(GSTK{prop=POSED _, stack = ({goals,...}::_),...}) = goals
  | top_goals(GSTK{prop=PROVED _, ...}) = raise ERR "top_goals" "no goals";

val top_goal = hd o top_goals;

fun new_goal (g as (asl,w)) f =
   if all (fn tm => type_of tm = bool) (w::asl)
    then GSTK{prop=POSED g, stack=[], final=f}
    else raise ERR "set_goal" "not a proposition; new goal not added";

fun finalizer(GSTK{final,...}) = final;

fun initial_goal(GSTK{prop = POSED g,...}) = g
  | initial_goal(GSTK{prop = PROVED (th,g),...}) = g;

fun rotate(GSTK{prop=PROVED _, ...}) _ =
        raise ERR "rotate" "goal has already been proved"
  | rotate(GSTK{prop, stack, final}) n =
     if n<0 then raise ERR"rotate" "negative rotations not allowed"
     else
      case stack
       of [] => raise ERR"rotate" "No goals to rotate"
        | {goals,validation}::rst =>
           if n > length goals
           then raise ERR "rotate"
                 "More rotations than goals -- no rotation done"
           else GSTK{prop=prop, final=final,
                     stack={goals=funpow n rotl goals,
                            validation=validation o funpow n rotr} :: rst};


local
  fun imp_err s = raise ERR "expandf" ("implementation error: "^s)
  fun return(GSTK{stack={goals=[],validation}::rst, prop as POSED g,final}) =
      let val th = validation []
      in case rst
         of [] =>
           (let val thm = final th
            in GSTK{prop=PROVED (thm,g), stack=[], final=final}
            end
            handle e as HOL_ERR _
              => (cr_add_string_cr "finalization failed"; raise e))
          | {goals = _::rst_o_goals, validation}::rst' =>
             ( cr_add_string_cr "Goal proved.";
               printthm th; say "\n";
               return(GSTK{prop=prop, final=final,
                           stack={goals=rst_o_goals,
                              validation=fn thl => validation(th::thl)}::rst'})
             )
          | otherwise => imp_err (quote "return")
      end
    | return gstk = gstk
in
fun expandf _ (GSTK{prop=PROVED _, ...}) =
       raise ERR "expandf" "goal has already been proved"
  | expandf tac (GSTK{prop as POSED g, stack,final}) =
     let val arg = (case stack of [] => g | tr::_ => hd (#goals tr))
         val (glist,vf) = tac arg
         val dpth = length stack
         val gs = return(GSTK{prop=prop,final=final,
                              stack={goals=glist, validation=vf} :: stack})
     in case gs
        of GSTK{prop = PROVED _, ...} => ()
         | GSTK{prop, final, stack as {goals, ...}::_} =>
             let val dpth' = length stack
             in if dpth' > dpth
                then if (dpth+1 = dpth')
                     then add_string_cr
                           (case (length goals)
                             of 0 => imp_err "1"
                              | 1 => "1 subgoal:"
                              | n => (int_to_string n)^" subgoals:")
                     else imp_err "2"
                else cr_add_string_cr "Remaining subgoals:"
             end
         | _ => imp_err "3"
         ;
         gs
     end
end;

fun expand tac gs = expandf (Tactical.VALID tac) gs;

fun extract_thm (GSTK{prop=PROVED(th,_), ...}) = th
  | extract_thm _ = raise ERR "extract_thm" "no theorem proved";

(* Prettyprinting *)

local
val print_fvs = ref false
val _ = register_btrace ("goalstack fvs", print_fvs)

val print_goal_at_top = ref true;
val _ = register_btrace ("goalstack print goal at top", print_goal_at_top)

val print_number_assums = ref 1000000;
val _ = register_trace ("goalstack number of assums", print_number_assums, 1000000)


fun ppgoal ppstrm (asl,w) =
   let open Portable
       val {add_string, add_break,
            begin_block, end_block, add_newline, ...} = with_ppstream ppstrm
       val pr = Parse.pp_term ppstrm
       val length_asl = length asl;
       fun pr_index (i,tm) = if ((!print_number_assums) >= length_asl - i) then
            (begin_block CONSISTENT 0;
             add_string (Int.toString i^".  ");
             pr tm; (if (i = length_asl - 1) then () else add_newline()); end_block()) else ()
       fun pr_indexes [] = raise ERR "pr_indexes" ""
         | pr_indexes [x] = pr x
         | pr_indexes L = pr_list pr_index (fn () => ()) (fn () => ())
                                  (Lib.enumerate 0 (rev asl));

       fun pr_hidden_indexes L = ((if (((!print_number_assums) < length_asl)) then
                                    (begin_block CONSISTENT 0;
                                       add_string ("...");
	                               if (!print_number_assums > 0) then add_newline() else ();
                                     end_block()) else ());pr_indexes L);
   in
     begin_block CONSISTENT 0;
     if (not (!print_goal_at_top)) then () else (
        pr w;
        add_newline ();
        (case asl
           of [] => ()
           | _  => ( begin_block CONSISTENT 2;
                     add_string (!Globals.goal_line);
                     add_newline ();
                     pr_hidden_indexes asl; end_block ()));
        add_newline ());
     if !print_fvs then let
         val fvs = Listsort.sort Term.compare (free_varsl (w::asl))
         fun pr_v v = let
           val (n, ty) = dest_var v
         in
           begin_block INCONSISTENT 2;
           add_string n; add_break(1,0);
           Parse.pp_type ppstrm ty;
           end_block()
         end
       in
         if not (null fvs) then
           (if not (null asl) then add_newline() else ();
            add_string "Free variables"; add_newline();
            add_string "  ";
            begin_block CONSISTENT 0;
            pr_list pr_v (fn () => ()) (fn () => add_break(5,0)) fvs;
            end_block ();
            add_newline(); add_newline())
         else ()
       end
     else ();
     if (!print_goal_at_top) then () else (
        (case asl
           of [] => ()
           | _  => ( begin_block CONSISTENT 2;
                     add_string "  ";
                     pr_hidden_indexes asl;
                     end_block ();
                     add_newline ();
                     add_string (!Globals.goal_line)));
        add_newline ();
        pr w;
        add_newline ());
     end_block ()
   end
   handle e => (Lib.say "\nError in attempting to print a goal!\n";  raise e);

   val goal_printer = ref ppgoal
in
 val std_pp_goal = ppgoal
 fun pp_goal ppstrm = !goal_printer ppstrm
 fun set_goal_pp pp = !goal_printer before (goal_printer := pp)
end;

fun pp_gstk ppstrm  =
 let val pr_goal = pp_goal ppstrm
     val {add_string, add_break, begin_block, end_block, add_newline, ...} =
                   Portable.with_ppstream ppstrm
     fun pr (GSTK{prop = POSED g, stack = [], ...}) =
           let in
             begin_block Portable.CONSISTENT 0;
             add_string"Initial goal:";
             add_newline(); add_newline();
             pr_goal g;
             end_block()
           end
       | pr (GSTK{prop = POSED _, stack = ({goals,...}::_), ...}) =
           let val (ellipsis_action, goals_to_print) =
               if length goals > !show_nsubgoals then
               let val num_elided = length goals - !show_nsubgoals
               in
                 ((fn () =>
                   (add_string ("..."^Int.toString num_elided ^ " subgoal"^
                                (if num_elided = 1 then "" else "s") ^
                                " elided...");
                    add_newline(); add_newline())),
                  rev (List.take (goals, !show_nsubgoals)))
               end
               else
                 ((fn () => ()), rev goals)
           in
             begin_block Portable.CONSISTENT 0;
             ellipsis_action();
             Portable.pr_list
               pr_goal (fn () => ()) add_newline goals_to_print;
             end_block()
           end
       | pr (GSTK{prop = PROVED (th,_), ...}) =
           let in
              begin_block Portable.CONSISTENT 0;
              add_string "Initial goal proved.";
              add_newline();
              Parse.pp_thm ppstrm th;
              end_block()
           end
 in pr
 end

end (* goalStack *)
