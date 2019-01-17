(* ========================================================================= *)
(* FILE          : rlGameRewrite.sml                                         *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameRewrite :> rlGameRewrite =
struct

open HolKernel boolLib Abbrev aiLib rlLib

val ERR = mk_HOL_ERR "rlGameRewrite"
val debugdir = HOLDIR ^ "/src/AI/reinforcement_learning/debug"
fun debug s = debug_in_dir debugdir "rlGameRewrite" s


(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

(* position *)
datatype board =
  StopBoard of (term * int list) |
  LrBoard of (term * int list) |
  SubBoard of (term * int list) |
  FailBoard 

type situation = bool * board

fun startpos target = (true, LrBoard (target,[]))

val failsit = (true, FailBoard)

(* axioms *)
val ax1 = ``x + 0 = x``;
val ax2 = ``x * 0 = 0``;
val ax3 = ``x + SUC y = SUC (x + y)``;
val ax4 = ``x * SUC y = x * y + x``;
val ax5 = sym_tac ax3;
val ax6 = sym_tac ax4;
val ax7 = sym_tac ax1;

fun nntm_of_sit sit = case sit of
    (true, StopBoard (tm,pos)) =>
    if null pos then tm else tag_position (tm,pos)
  | (true, LrBoard (tm,pos)) =>
    if null pos then tm else tag_position (tm,pos)
  | (true, SubBoard (tm,pos)) =>
    if null pos then tm else tag_position (tm,pos)
  | _ => raise ERR "nntm_of_sit" ""

(* -------------------------------------------------------------------------
   Position move
   ------------------------------------------------------------------------- *)

datatype stopchoice = Stop | Cont
val all_stopchoice = [Stop,Cont]
fun string_of_stopchoice stop = case stop of
    Stop => "Stop" | Cont => "Cont"

fun move_stop stop sit = case sit of (p, StopBoard (tm,pos)) =>
    (
    case stop of
      Stop => (p, SubBoard (tm,pos))
    | Cont =>
      let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
        case argl of
          []    => failsit
        | [a]   => (p, StopBoard (tm, pos @ [0]))
        | [a,b] => (p, LrBoard (tm,pos))
        | _     => raise ERR "descend_pos" " "
      end
    )
  | _ => raise ERR "move_stop" ""

datatype lrchoice = Left | Right
val all_lrchoice = [Left,Right]
fun string_of_lrchoice lr = case lr of
    Left  => "Left"
  | Right => "Right"

fun move_lr lr sit = case sit of (p, LrBoard (tm,pos)) =>
   (
   case lr of
     Left  => (p, StopBoard (tm, pos @ [0]))
   | Right => (p, StopBoard (tm, pos @ [1]))
   )
 | _ => raise ERR "move_lr" ""

(* -------------------------------------------------------------------------
   Sub Move
   ------------------------------------------------------------------------- *)

datatype subchoice =
  AddZero | MultZero | AddReduce | MultReduce | AddExpand | MultExpand |
  AddZeroExpand

val all_subchoice =
  [AddZero, MultZero, AddReduce, MultReduce, AddExpand, MultExpand,
   AddZeroExpand]

fun string_of_subchoice sub = case sub of
    AddZero => "AddZero"
  | MultZero => "MultZero"
  | AddReduce => "AddReduce"
  | MultReduce => "MultReduce"
  | AddExpand => "AddExpand"
  | MultExpand => "MultExpand"
  | AddZeroExpand => "AddZeroExpand"

fun move_sub sub sit = case sit of (p, SubBoard (tm,pos)) =>
  let fun f ax = (p, LrBoard (sub_tac (tm,pos) ax,[]))
    handle HOL_ERR _ => failsit
  in
    case sub of
      AddZero => f ax1
    | MultZero => f ax2
    | AddReduce => f ax3
    | MultReduce => f ax4
    | AddExpand => f ax5
    | MultExpand => f ax6
    | AddZeroExpand => f ax7
  end
  | _ => raise ERR "move_sub" ""

(* -------------------------------------------------------------------------
   All moves
   ------------------------------------------------------------------------- *)

datatype move =
  StopMove of stopchoice |
  LrMove of lrchoice |
  SubMove of subchoice

fun apply_move move sit = case move of
    StopMove stop => move_stop stop sit
  | LrMove lr => move_lr lr sit
  | SubMove imit => move_sub imit sit

fun string_of_move move = case move of
    StopMove stop => string_of_stopchoice stop
  | LrMove lr => string_of_lrchoice lr
  | SubMove imit => string_of_subchoice imit

end (* struct *)
