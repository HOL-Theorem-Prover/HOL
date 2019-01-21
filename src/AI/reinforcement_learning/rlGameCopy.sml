(* ========================================================================= *)
(* FILE          : rlConj.sml                                                *)
(* DESCRIPTION   : Specification of a Term Copying                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameCopy :> rlGameCopy =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib rlLib psMCTS mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlGameCopy"

datatype board =
  Board of (term * (term * pos)) | FailBoard

datatype sitclass = Class

fun class_of_sit sit = case snd sit of
    Board _  => Class
  | _ => raise ERR "class_of_sit" ""

fun nntm_of (ctm,(tm,pos)) = mk_eq (ctm, tag_position (tm,pos))

fun nntm_of_sit sit = case snd sit of
    Board x  => nntm_of x
  | FailBoard  => F

fun status_of sit = case snd sit of
    Board (tm1,(tm2,[])) =>
    (
    if tm1 = tm2 then Win
    else if term_size tm2 > term_size tm1 + 2 then Lose
    else Undecided
    )
  | Board _ => Undecided
  | FailBoard => Lose

fun mk_startsit target = (true, Board (target,(zero,[])))

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move =
  Down | Left | Right |
  Sz | Sal | Sar | Sss |
  Asa | Asl | Asr | Aac | Aasl | Aasr

fun string_of_move move = case move of
    Down => "Down"
  | Left  => "Left"
  | Right => "Right"
  | Sz  => "Sz"
  | Sal => "Sal"
  | Sar => "Sar"
  | Sss => "Sss"
  | Asa => "Asa"
  | Asl => "Asl"
  | Asr => "Asr"
  | Aac => "Aac"
  | Aasl => "Aasl"
  | Aasr => "Aasr"

val all_choice =
  [Down,Left,Right,Sz, Sal, Sar, Sss,Asa, Asl, Asr, Aac, Aasl, Aasr]

val all_class = [(Class,all_choice)]

fun movel_in_sit sitclass = assoc sitclass all_class

(* -------------------------------------------------------------------------
   Effect of moves
   ------------------------------------------------------------------------- *)

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

fun apply_move move sit = (true, case snd sit of
    Board (ctm,(tm,pos)) =>
      if is_add (tm,pos) then action_add move (ctm,(tm,pos))
      else if is_suc (tm,pos) then action_suc move (ctm,(tm,pos))
      else action_zero move (ctm,(tm,pos))
  | FailBoard => raise ERR "apply_move" ""
  )

(* -------------------------------------------------------------------------
   Build random treenn
   ------------------------------------------------------------------------- *)

(*
val operl = (numtag_var,1) :: operl_of_term ``SUC 0 + 0 = 0``;
val dim = 8;
val tnnspec = (operl,dim);

random_eptnn (#movel_in_sit sittools) tnnspec

fun random_eptnn movel_in_sit (operl,dim) sitclass =
  let val polin = length (movel_in_sit sitclass) in
    (random_treenn (dim,1) operl, random_treenn (dim,polin) operl)
  end
*)

(* -------------------------------------------------------------------------
   Regroup all situation tools under one record
   ------------------------------------------------------------------------- *)

type sittools =
  {
  class_of_sit: board sit -> sitclass,
  mk_startsit: term -> board sit,
  movel_in_sit: sitclass -> move list,
  nntm_of_sit: board sit -> term,
  sitclassl: sitclass list
  }

val sittools : sittools =
  {
  class_of_sit = class_of_sit,
  mk_startsit = mk_startsit,
  movel_in_sit = movel_in_sit,
  nntm_of_sit = nntm_of_sit,
  sitclassl = (map fst all_class)
  }

val rulespec = (status_of, apply_move)



end (* struct *)
