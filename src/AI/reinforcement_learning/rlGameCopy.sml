(* ========================================================================= *)
(* FILE          : rlConj.sml                                                *)
(* DESCRIPTION   : Specification of a Term Copying                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameCopy :> rlGameCopy =
struct

open HolKernel Abbrev boolLib aiLib rlLib psMCTS mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlGameCopy"

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

datatype board = Board of (term * (term * pos)) | FailBoard

fun mk_startsit target = (true, Board (target,(zero,[])))

fun status_of sit = case snd sit of
    Board (tm1,(tm2,[])) =>
    (
    if tm1 = tm2 then Win
    else if term_size tm2 > term_size tm1 + 2 then Lose
    else Undecided
    )
  | Board _ => Undecided
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   State representation
   ------------------------------------------------------------------------- *)

val operl = (numtag_var,1) :: operl_of_term ``SUC 0 + 0 = 0``
val dim = 10

fun nntm_of_sit sit = case snd sit of
    Board (ctm,(tm,pos))=> mk_eq (ctm, tag_position (tm,pos))
  | FailBoard  => F

(* -------------------------------------------------------------------------
   Action
   ------------------------------------------------------------------------- *)

datatype move =
  Down | Left | Right |
  Sz | Sal | Sar | Sss |
  Asa | Asl | Asr | Aac | Aasl | Aasr

val movel =
  [Down,Left,Right,Sz, Sal, Sar, Sss,Asa, Asl, Asr, Aac, Aasl, Aasr]

fun is_zero (tm,pos) = subtm_at_pos pos tm = zero
fun is_suc (tm,pos) = can dest_suc (subtm_at_pos pos tm)
fun is_add (tm,pos) = can dest_add (subtm_at_pos pos tm)

fun replace_by (ctm,(tm,pos)) x =
   Board (ctm,(sub_at_pos tm (pos,x), []))

fun action_zero move (ctm,(tm,pos)) = case move of
    Down => replace_by (ctm,(tm,pos)) (mk_suc zero)
  | _ => FailBoard

fun action_suc move (ctm,(tm,pos)) =
  let
    val subtm1 = subtm_at_pos pos tm
    val subtm2 = dest_suc subtm1
    fun f x = replace_by (ctm,(tm,pos)) x
  in
    case move of
      Down => if is_zero (tm,pos @ [0])
              then replace_by (ctm,(tm,pos @ [0])) ``SUC 0``
              else Board (ctm,(tm,pos @ [0]))
    | Sz   => f zero
    | Sal  => f (mk_add (subtm2,zero))
    | Sar  => f (mk_add (zero,subtm2))
    | Sss  => f (mk_suc (mk_suc subtm2))
    | _    => FailBoard
  end

fun action_add move (ctm,(tm,pos)) =
  let
    val subtm1 = subtm_at_pos pos tm
    val (l,r) = dest_add subtm1
    fun f x = replace_by (ctm,(tm,pos)) x
  in
    case move of
      Left => if is_zero (tm,pos @ [0])
              then replace_by (ctm,(tm,pos @ [0])) ``SUC 0``
              else Board (ctm,(tm,pos @ [0]))
    | Right => if is_zero (tm,pos @ [1])
              then replace_by (ctm,(tm,pos @ [1])) ``SUC 0``
              else Board (ctm,(tm,pos @ [1]))
    | Asa  => f (mk_suc (mk_add (l,r)))
    | Asl  => f (mk_suc l)
    | Asr  => f (mk_suc r)
    | Aac  => f (mk_add (r,l))
    | Aasl => f (mk_add (mk_suc l, r))
    | Aasr => f (mk_add (l, mk_suc r))
    | _ => FailBoard
  end

fun apply_move move sit = (true,
  case snd sit of
    Board (ctm,(tm,pos)) =>
      if is_add (tm,pos) then action_add move (ctm,(tm,pos))
      else if is_suc (tm,pos) then action_suc move (ctm,(tm,pos))
      else action_zero move (ctm,(tm,pos))
  | FailBoard => raise ERR "apply_move" ""
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



end (* struct *)
