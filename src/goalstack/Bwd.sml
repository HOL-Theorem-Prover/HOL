(* Backward proofs, with no idea of undo *)
structure Bwd :> Bwd =
struct


open HolKernel Abbrev;
infix 0 before;

fun BWD_ERR{func,mesg} =
    HOL_ERR{origin_structure = "Bwd",
            origin_function = func,
            message = mesg}

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")

fun rotl (a::rst) = rst@[a]
  | rotl [] = raise BWD_ERR{func = "rotl", mesg =  "empty list"}

fun rotr lst = 
   let val (front,back) = Lib.front_last lst
   in (back::front)
   end 
   handle _ => raise BWD_ERR{func = "rotr",mesg =  "empty list"}



(* GOALSTACKS *)
(*---------------------------------------------------------------------------
 * A goalstack is a stack of (goal list, validation_function) records. Each 
 * goal in the goal list is a (term list, term) pair. The validation 
 * function is a function from a list of theorems to a theorem. It must be 
 * that the number of goals in the goal list is equal to the number of 
 * formal parameters in the validation function. Unfortunately, the type
 * system of ML is not strong enough to check that.
 ---------------------------------------------------------------------------*)

type tac_result = {goals : goal list,
                   validation : Thm.thm list -> Thm.thm}

datatype proposition = POSED of goal
                     | PROVED of Thm.thm;

datatype gstk = GSTK of {prop: proposition,
                         stack : tac_result list}

fun depth(GSTK{stack,...}) = length stack;

fun is_initial(GSTK{prop = POSED g, stack = []}) = true
  | is_initial _ = false;

fun top_goals(GSTK{prop = POSED g, stack = []}) = [g]
  | top_goals(GSTK{prop = POSED _, stack = {goals,...}::_}) = goals
  | top_goals(GSTK{prop = PROVED _, ...}) = raise BWD_ERR{func = "top_goals", 
                                                          mesg = "no goals"};

val top_goal = hd o top_goals;

fun new_goal (g as (asl,w)) = 
   let val bool = Type.mk_type{Tyop = "bool", Args = []}
       fun is_bool tm = (Term.type_of tm = bool)
   in if (all is_bool (w::asl))
      then GSTK{prop = POSED g, stack = []}
      else raise BWD_ERR{func = "set_goal",
                         mesg = "not a proposition; new goal not added"}
   end;

fun initial_goal(GSTK{prop = POSED g,...}) = g
  | initial_goal(GSTK{prop = PROVED th,...}) = Thm.dest_thm th;


fun rotate(GSTK{prop = PROVED _, ...}) _ = 
        raise BWD_ERR{func = "rotate", mesg = "goal has already been proved"}
  | rotate(GSTK{prop, stack}) n = 
      if (n<0)
      then raise BWD_ERR{func="rotate", mesg="negative rotations not allowed"}
      else 
      case stack
      of [] => raise BWD_ERR{func = "rotate",mesg = "No goals to rotate"}
       | ({goals,validation}::rst) =>
          if (n > length goals)
          then raise BWD_ERR{func = "rotate",
                        mesg = "More rotations than goals -- no rotation done"}
          else GSTK{prop = prop,
                    stack = {goals = funpow n rotl goals,
                             validation=validation o funpow n rotr}
                            :: rst};


local
fun imp_err s = raise BWD_ERR{func = "expandf",
                              mesg = "implementation error: "^s}
fun return(GSTK{stack = {goals = [],validation}::rst, prop}) = 
    let val th = validation []
    in case rst 
       of [] => GSTK{prop = PROVED th, stack = []}
       | ({goals = _::rst_o_goals, validation}::rst') =>
           ( cr_add_string_cr "Goal proved.";
             add_string_cr (Thm.thm_to_string th);
             return(GSTK{prop = prop,
                         stack = {goals = rst_o_goals,
                                  validation=fn thl => validation(th::thl)}
                                 :: rst'}))
       | _ => imp_err (quote "return")
    end
  | return gstk = gstk
in
fun expandf(GSTK{prop = PROVED _, ...}) _ = 
           raise BWD_ERR{func = "expandf", mesg="goal has already been proved"}
  | expandf(GSTK{prop as POSED g, stack}) tac =
     let val (glist,vf) = tac (case stack of   []    => g 
                                           | (tr::_) => hd (#goals tr))
         val dpth = length stack
         val gs = return(GSTK{prop = prop,
                              stack = {goals = glist, validation = vf}
                                      :: stack})
     in case gs
        of GSTK{prop = PROVED _, stack} => ()
         | GSTK{prop, stack as {goals, ...}::_} =>
             let val dpth' = length stack
             in if (dpth' > dpth)
                then if (dpth+1 = dpth') 
                     then add_string_cr(case (length goals)
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

fun expand gs = expandf gs o Tactical.VALID;

fun extract_thm (GSTK{prop = PROVED th, ...}) = th
  | extract_thm _ = raise BWD_ERR{func = "extract_thm", 
                                  mesg = "no theorem proved"};

(* Prettyprinting *)
fun enum i [] = []
  | enum i (h::t) = 
     (i,h)::enum (i+1) t;
fun enumerate l = enum 0 l;

local
fun ppgoal ppstrm (asl,w) =
   let open Portable_PrettyPrint
       val {add_string, add_break, 
            begin_block, end_block, add_newline, ...} = with_ppstream ppstrm
       val pr = Hol_pp.pp_term ppstrm
       fun pr_index (i,tm) = 
            (begin_block CONSISTENT 0;
             add_string (Int.toString i^".  ");
             pr tm; end_block())
       fun pr_indexes [] = raise BWD_ERR{func="pr_indexes", mesg=""}
         | pr_indexes [x] = pr x
         | pr_indexes L = pr_list pr_index (fn () => ()) add_newline 
                                  (enumerate (rev asl));
   in
     begin_block CONSISTENT 0;
     pr w; 
     add_newline ();
     (case asl
        of [] => ()
         | _  => ( begin_block CONSISTENT 2;
                   add_string (!Globals.goal_line);
                   add_newline ();
                   pr_indexes asl;
                   end_block ()));
     add_newline ();
     end_block ()
   end
   handle e => (say "\nError in attempting to print a goal!\n";  raise e);

   val goal_printer = ref ppgoal
in
 val std_pp_goal = ppgoal
 fun pp_goal ppstrm = !goal_printer ppstrm
 fun set_goal_pp pp = !goal_printer before (goal_printer := pp)
end;

fun pp_gstk ppstrm  =
   let val pr_goal = pp_goal ppstrm
       val {add_string, add_break, begin_block, end_block, add_newline, ...} =
                     Portable_PrettyPrint.with_ppstream ppstrm
       fun pr (GSTK{prop = POSED g, stack = []}) = 
              (begin_block Portable_PrettyPrint.CONSISTENT 0;
               add_string"Initial goal:";
               add_newline(); add_newline();
               pr_goal g;
               end_block())
         | pr (GSTK{prop = POSED _, stack = {goals,...}::_}) = 
             (begin_block Portable_PrettyPrint.CONSISTENT 0;
              Portable_PrettyPrint.pr_list 
                   pr_goal (fn () => ()) add_newline (rev goals);
              end_block())
         | pr (GSTK{prop = PROVED th, ...}) = 
             (begin_block Portable_PrettyPrint.CONSISTENT 0;
              add_string "Initial goal proved.";
              add_newline();
              Thm.pp_thm ppstrm th;
              end_block())
   in pr
   end;

end; (* Bwd *)
