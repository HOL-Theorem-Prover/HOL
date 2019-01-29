(* ========================================================================= *)
(* FILE          : rlGameRewrite.sml                                         *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameRewrite :> rlGameRewrite =
struct

open HolKernel boolLib Abbrev aiLib rlLib psMCTS psTermGen

val ERR = mk_HOL_ERR "rlGameRewrite"
val debugdir = HOLDIR ^ "/src/AI/reinforcement_learning/debug"
fun debug s = debug_in_dir debugdir "rlGameRewrite" s

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

datatype board = Board of (term * pos) | FailBoard

fun mk_startsit target = (true, Board (target,[]))

fun status_of sit = case snd sit of
    Board (tm,[]) => if is_refl tm then Win else Undecided
  | Board (tm,_) => Undecided
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   State representation
   ------------------------------------------------------------------------- *)

val operl = (numtag_var,1) :: operl_of_term ``SUC 0 + 0 = 0 * 0``;
val dim = 10;

fun nntm_of_sit sit = case snd sit of
    Board (tm,pos) => tag_position (tm,pos)
  | FailBoard => F

(* -------------------------------------------------------------------------
   Action
   ------------------------------------------------------------------------- *)

datatype move =
  Down | Left | Right |
  AddZero | MultZero | AddReduce | MultReduce | AddExpand | MultExpand |
  AddZeroExpand

val movel =
  [Down, Left, Right,
   AddZero, MultZero, AddReduce, MultReduce, AddExpand, MultExpand,
   AddZeroExpand]

fun n_arg n (tm,pos) =
  let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
    length argl = n
  end

val ax1 = ``x + 0 = x``;
val ax2 = ``x * 0 = 0``;
val ax3 = ``x + SUC y = SUC (x + y)``;
val ax4 = ``x * SUC y = x * y + x``;
val ax5 = sym_tac ax3;
val ax6 = sym_tac ax4;
val ax7 = sym_tac ax1;

fun action_sub sub (tm,pos) =
  let fun f ax =
    let val tm' = sub_tac (tm,pos) ax in
      if tm' <> tm then Board (tm',[]) else FailBoard
    end
    handle HOL_ERR _ => FailBoard
  in
    case sub of
      AddZero => f ax1
    | MultZero => f ax2
    | AddReduce => f ax3
    | MultReduce => f ax4
    | AddExpand => f ax5
    | MultExpand => f ax6
    | AddZeroExpand => f ax7
    | _ => FailBoard
  end

fun apply_move move sit = (true,
  case snd sit of Board (tm,pos) =>
    (
    case move of
      Down => if n_arg 1 (tm,pos) then Board (tm, pos @ [0]) else FailBoard
    | Left => if n_arg 2 (tm,pos) then Board (tm, pos @ [0]) else FailBoard
    | Right => if n_arg 2 (tm,pos) then Board (tm, pos @ [1]) else FailBoard
    | _ => action_sub move (tm,pos)
    )
  | _ => raise ERR "move_sub" ""
  )

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

type gamespec =
  {
  mk_startsit: term -> board sit,
  movel: move list,
  status_of : (board psMCTS.sit -> psMCTS.status),
  apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
  operl : (term * int) list,
  dim : int,
  nntm_of_sit: board sit -> term
  }

val gamespec : gamespec =
  {
  mk_startsit = mk_startsit,
  movel = movel,
  status_of = status_of,
  apply_move = apply_move,
  operl = operl,
  dim = dim,
  nntm_of_sit = nntm_of_sit
  }

(* -------------------------------------------------------------------------
   Target generator
   ------------------------------------------------------------------------- *)

fun eval_ground tm = (rhs o concl o EVAL) tm

fun mk_targetl maxsize n =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size maxsize (``:num``,cset)
    val tml1 = filter (fn x => eval_ground x = ``0``) tml0
    fun f () = mk_eq (random_elem tml1, random_elem tml1)
  in
    mk_startsit (List.tabulate (n, fn _ => f ()))
  end


end (* struct *)
