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
val show_stack_subgoal_count = ref true
val print_fvs = ref false
val print_goal_at_top = ref false;
val reverse_assums = ref false;
val print_number_assums = ref 1000000;
val other_subgoals_pretty_limit = ref 100;

val _ = register_trace ("Goalstack.howmany_printed_subgoals", show_nsubgoals,
                        10000);
val _ = register_btrace("Goalstack.show_proved_subtheorems", chatting);
val _ = register_btrace("Goalstack.show_stack_subgoal_count",
                        show_stack_subgoal_count);
val _ = register_btrace("Goalstack.print_goal_fvs", print_fvs)
val _ = register_btrace("Goalstack.print_goal_at_top", print_goal_at_top)
val _ = register_btrace("Goalstack.print_assums_reversed", reverse_assums)
val _ = register_trace ("Goalstack.howmany_printed_assums",
                        print_number_assums, 1000000)
val _ = register_trace("Goalstack.other_subgoals_pretty_limit",
                       other_subgoals_pretty_limit, 100000)


fun say s = if !chatting then Lib.say s else ();

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")

fun printthm th = if !chatting then say (Parse.thm_to_string th) else ()

fun rotl (a::rst) = rst@[a]
  | rotl [] = raise ERR "rotl" "empty list"

fun rotr lst =
  let val (front,back) = Lib.front_last lst
  in (back::front)
  end
  handle HOL_ERR _ => raise ERR "rotr" "empty list"

fun goal_size (asl,t) =
  List.foldl (fn (a,acc) => term_size a + acc) (term_size t) asl


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

fun tac_result_size (tr : tac_result, acc) =
  List.foldl (fn (g,acc) => goal_size g + acc) acc (#goals tr)

fun gstk_size (GSTK{prop,stack,...}) =
  case prop of
      PROVED _ => 0
    | POSED _ => List.foldl tac_result_size 0 stack

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
  fun imp_err s =
    raise ERR "expandf or expand_listf" ("implementation error: "^s)

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

  fun expand_msg dpth (GSTK{prop = PROVED _, ...}) = ()
    | expand_msg dpth (GSTK{prop, final, stack as {goals, ...}::_}) =
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
    | expand_msg _ _ = imp_err "3" ;
in
fun expandf _ (GSTK{prop=PROVED _, ...}) =
       raise ERR "expandf" "goal has already been proved"
  | expandf tac (GSTK{prop as POSED g, stack,final}) =
     let val arg = (case stack of [] => g | tr::_ => hd (#goals tr))
         val (glist,vf) = tac arg
         val dpth = length stack
         val gs = return(GSTK{prop=prop,final=final,
                              stack={goals=glist, validation=vf} :: stack})
     in expand_msg dpth gs ; gs end

(* note - expand_listf, unlike expandf, replaces the top member of the stack *)
fun expand_listf ltac (GSTK{prop=PROVED _, ...}) =
        raise ERR "expand_listf" "goal has already been proved"
  | expand_listf ltac (GSTK{prop as POSED g, stack = [], final}) =
    expand_listf ltac (GSTK{prop = POSED g,
      stack = [{goals = [g], validation = hd}], final = final})
  | expand_listf ltac (GSTK{prop, stack as {goals,validation}::rst, final}) =
    let val (new_goals, new_vf) = ltac goals
      val dpth = length stack - 1 (* because we don't augment the stack *)
      val new_gs = return (GSTK{prop=prop, final=final,
        stack={goals=new_goals, validation=validation o new_vf} :: rst})
    in expand_msg dpth new_gs ; new_gs end ;
end ;

fun expand tac gs = expandf (Tactical.VALID tac) gs;
fun expand_list ltac gs = expand_listf (Tactical.VALID_LT ltac) gs;

fun flat gstk =
    case gstk of
        GSTK{prop,
             stack as {goals,validation} ::
                      {goals = g2 :: goals2, validation = validation2} ::
                      rst,
             final} =>
        let
          fun v thl = let
            val (thl1, thl2) = Lib.split_after (length goals) thl
          in
            validation2 (validation thl1 :: thl2)
          end
          val newgv = {goals = goals @ goals2, validation = v}
        in
          GSTK {prop = prop, stack = newgv :: rst, final = final}
        end
    | _ => raise ERR "flat" "goalstack in wrong shape"

fun flatn (GSTK{prop=PROVED _, ...}) n =
        raise ERR "flatn" "goal has already been proved"
  | flatn gstk 0 = gstk
  | flatn (gstk as GSTK{prop, stack = [], final}) n = gstk
  | flatn (gstk as GSTK{prop, stack as [_], final}) n = gstk
  | flatn (gstk as GSTK{prop, stack, final}) n = flatn (flat gstk) (n-1) ;

fun extract_thm (GSTK{prop=PROVED(th,_), ...}) = th
  | extract_thm _ = raise ERR "extract_thm" "no theorem proved";

(* Prettyprinting *)

local

open Portable smpp
fun ty2s ty = String.extract(Parse.type_to_string ty, 1, NONE)

fun check_vars (g as (asl,w)) =
    let
      val fvs = FVL (w::asl) empty_tmset
      fun foldthis (v,acc) =
          let
            val (nm,ty_s) = (I ## ty2s) (dest_var v)
          in
            case Binarymap.peek(acc, nm) of
                NONE => Binarymap.insert(acc, nm, [ty_s])
              | SOME vs => Binarymap.insert(acc, nm, ty_s::vs)
          end
      val m = HOLset.foldl foldthis (Binarymap.mkDict String.compare) fvs
      fun foldthis (nm,vtys,msg) =
          if length vtys > 1 then
            ("  " ^ nm ^ " : " ^ String.concatWith ", " vtys) :: msg
          else msg
      val msg = Binarymap.foldl foldthis [] m
    in
      if null msg then nothing
      else (
        add_newline >> add_newline >>
        add_string ("WARNING: goal contains variables of same name \
                    \but different types") >>
        add_newline >>
        List.foldl (fn (s,m) => m >> add_string s >> add_newline)
                   nothing
                   msg
      )
    end
val pr = lift Parse.pp_term
fun min (a,b) = if a < b then a else b
fun pr_numbered_assum (i,tm) =
    let
      val istr = StringCvt.padLeft #" " 2 (Int.toString i)^".  "
    in
      block CONSISTENT 0 (
        add_string istr >>
        block CONSISTENT (size istr) (pr tm)
      )
    end
fun pr_maybe_hidden_assum (SOME a) = pr_numbered_assum a
  | pr_maybe_hidden_assum NONE = add_string "..."

fun pr_assums asl =
    let
      val length_asl = length asl
      val length_assums = min (length_asl, !print_number_assums)
      val assums = List.rev (List.take (asl, length_assums))
      val l = Lib.enumerate (length_asl - length_assums) assums
      val l = if !reverse_assums then List.rev l else l
      val has = if !print_number_assums < length_asl then NONE :: map SOME l
                else map SOME l
    in
      pr_list pr_maybe_hidden_assum add_newline has
    end

fun pr_v v = let
  val (n, ty) = dest_var v
in
  block INCONSISTENT 2 (
    add_string n >> add_break(1,0) >> lift Parse.pp_type ty
  )
end

fun print_fvs0 fvs =
    block CONSISTENT 0 (
      add_string "Free variables:" >> add_break(1,2) >>
      block INCONSISTENT 0 (pr_list pr_v (add_break(3,0)) fvs)
    )
fun print_goalfvs (asl,w) =
    let
      val fvs = free_varsl (w::asl) |> Listsort.sort Term.compare
    in
      if !print_fvs andalso not (null fvs) then
        add_newline >> add_newline >> print_fvs0 fvs
      else nothing
    end

val pr_goal = pr
fun indent n p = add_string (CharVector.tabulate(n, fn _ => #" ")) >>
                 block CONSISTENT n p


fun ppgoal_assums_first (g as (asl,w)) =
      block CONSISTENT 0 (
        block CONSISTENT 0 (pr_assums asl) >> add_newline >>
        add_string (!Globals.goal_line) >> add_newline >>
        indent 5 (pr_goal w) >>
        print_goalfvs g >> check_vars g
      )

fun ppgoal_assums_last (g as (asl,w)) =
    block CONSISTENT 0 (
      indent 5 (pr_goal w) >> add_newline >>
      add_string (!Globals.goal_line) >> add_newline >>
      block CONSISTENT 0 (pr_assums asl) >>
      print_goalfvs g >> check_vars g
    )

fun ppgoal (g as (asl,w)) =
    if null asl then pr_goal w >> print_goalfvs g >> check_vars g
    else
      if !print_goal_at_top then ppgoal_assums_last g
      else ppgoal_assums_first g
   handle e => (Lib.say "\nError in attempting to print a goal!\n";  raise e);

   val goal_printer = ref (Parse.mlower o ppgoal)
in
 val mppgoal = ppgoal
 val std_pp_goal = Parse.mlower o ppgoal
 val pp_goal = !goal_printer
 fun set_goal_pp pp = !goal_printer before (goal_printer := pp)
end;

(* not clear that this function is used; certainly, default interactive system
   uses Manager.sml's printer instead. *)
fun pp_gstk gstk =
 let open smpp
     val pr_goal = mppgoal
     fun pr (GSTK{prop = POSED g, stack = [], ...}) =
             block Portable.CONSISTENT 0 (
               add_string"Initial goal:" >> add_newline >> add_newline >>
               pr_goal g
             )
       | pr (GSTK{prop = POSED _, stack = ({goals,...}::_), ...}) =
           let val (ellipsis_action, goals_to_print) =
                 if length goals > !show_nsubgoals then
                   let val num_elided = length goals - !show_nsubgoals
                   in
                     (add_string ("..."^Int.toString num_elided ^ " subgoal"^
                                  (if num_elided = 1 then "" else "s") ^
                                  " elided...") >>
                      add_newline >> add_newline,
                      rev (List.take (goals, !show_nsubgoals)))
                   end
                 else
                   (add_newline, rev goals)
               val (pfx,lastg) = front_last goals_to_print
               fun start() =
                 (ellipsis_action >>
                  pr_list pr_goal (add_newline >> add_newline) pfx)
               val size = List.foldl (fn (g,acc) => goal_size g + acc) 0 pfx
           in
             block Portable.CONSISTENT 0 (
               (if size > current_trace "Goalstack.other_subgoals_pretty_limit"
                then
                  with_flag(Parse.current_backend, PPBackEnd.raw_terminal)
                           start()
                else start()) >>
               (if not (null pfx) then add_newline >> add_newline
                else nothing) >>
               pr_goal lastg >>
              (if length goals > 1 andalso !show_stack_subgoal_count then
                 add_string ("\n\n" ^ Int.toString (length goals) ^
                             " subgoals")>>
                 add_newline
               else add_newline >> add_newline)
             )
           end
       | pr (GSTK{prop = PROVED (th,_), ...}) =
              block Portable.CONSISTENT 0 (
                add_string "Initial goal proved." >>
                add_newline >>
                lift Parse.pp_thm th
              )
 in
   pr gstk
 end

val pp_gstk = Parse.mlower o pp_gstk

fun print_tac pfx g = let
in
  print pfx;
  HOLPP.prettyPrint(print,!Globals.linewidth) (pp_goal g);
  Tactical.ALL_TAC g
end

end (* goalStack *)
