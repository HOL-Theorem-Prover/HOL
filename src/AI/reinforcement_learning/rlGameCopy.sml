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
  ScBoard of (term * (term * pos)) |
  LrBoard of (term * (term * pos)) |
  SucBoard of (term * (term * pos)) |
  AddBoard of (term * (term * pos)) |
  FailBoard

datatype sitclass = ScClass | LrClass | SucClass | AddClass

fun class_of_sit sit = case snd sit of
    ScBoard _  => ScClass
  | LrBoard _  => LrClass
  | SucBoard _ => SucClass
  | AddBoard _ => AddClass
  | _ => raise ERR "class_of_sit" ""

fun nntm_of (ctm,(tm,pos)) = mk_eq (ctm, tag_position (tm,pos))

fun nntm_of_sit sit = case snd sit of
    ScBoard x  => nntm_of x
  | LrBoard x  => nntm_of x
  | AddBoard x => nntm_of x
  | SucBoard x => nntm_of x
  | FailBoard  => F

fun status_of sit = case snd sit of
    ScBoard (tm1,(tm2,[])) =>
    (
    if tm1 = tm2 then Win
    else if term_size tm2 > term_size tm1 + 2 then Lose
    else Undecided
    )
  | FailBoard => Lose
  | _ => Undecided

fun mk_startsit target = (true, ScBoard (target,(zero,[])))

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move =
  Stop | Cont |
  Left | Right |
  Sz | Sal | Sar | Sss |
  Asa | Asl | Asr | Aac | Aasl | Aasr

fun string_of_move move = case move of
    Stop  => "Stop"
  | Cont  => "Cont"
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

val all_scchoice = [Stop,Cont]
val all_lrchoice = [Left,Right]
val all_succhoice = [Sz, Sal, Sar, Sss]
val all_addchoice = [Asa, Asl, Asr, Aac, Aasl, Aasr]

val all_class = 
  [(ScClass,all_scchoice),(LrClass,all_lrchoice), 
   (SucClass,all_succhoice),(AddClass,all_addchoice)]

fun movel_in_sit sitclass = assoc sitclass all_class

(* -------------------------------------------------------------------------
   Effect of moves
   ------------------------------------------------------------------------- *)

fun action_stop (ctm,(tm,pos)) =
  let val subtm = subtm_at_pos pos tm in
      if can dest_suc subtm then SucBoard (ctm,(tm,pos))
      else if can dest_add subtm then AddBoard (ctm,(tm,pos))
      else ScBoard (ctm, (sub_at_pos tm (pos, mk_suc zero),[]))
    end

fun action_cont (ctm,(tm,pos)) =
  let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
    case argl of
      []    => FailBoard
    | [a]   => ScBoard (ctm,(tm,pos @ [0]))
    | [a,b] => LrBoard (ctm,(tm,pos))
    | _     => raise ERR "descend_pos" " "
  end

fun action_sc move (ctm,(tm,pos)) = case move of
    Stop => action_stop (ctm,(tm,pos))
  | Cont => action_cont (ctm,(tm,pos))
  | _ => raise ERR "action_sc" ""

fun action_lr move (ctm,(tm,pos)) = case move of
    Left => ScBoard (ctm,(tm, pos @ [0]))
  | Right => ScBoard (ctm,(tm, pos @ [1]))
  | _ => raise ERR "action_lr" ""

fun action_suc move (ctm,(tm,pos)) =
  let
    val subtm1 = subtm_at_pos pos tm
    val subtm2 = dest_suc subtm1
    fun f x = sub_at_pos tm (pos,x)
    val newtm = case move of
        Sz  => f zero
      | Sal => f (mk_add (subtm2,zero))
      | Sar => f (mk_add (zero,subtm2))
      | Sss => f (mk_suc (mk_suc subtm2))
      | _   => raise ERR "action_suc" ""
  in
    ScBoard (ctm,(newtm,[]))
  end

fun action_add move (ctm,(tm,pos)) =
  let
    val subtm1 = subtm_at_pos pos tm
    val (l,r) = dest_add subtm1
    fun f x = sub_at_pos tm (pos,x)
    val newtm = case move of
        Asa  => f (mk_suc (mk_add (l,r)))
      | Asl  => f (mk_suc l)
      | Asr  => f (mk_suc r)
      | Aac  => mk_add (r,l)
      | Aasl => mk_add (mk_suc l, r)
      | Aasr => mk_add (l, mk_suc r)
      | _ => raise ERR "action_add" ""
  in
    ScBoard (ctm,(newtm,[]))
  end

fun apply_move move sit = (true, case snd sit of
    ScBoard x => action_sc move x
  | LrBoard x => action_lr move x
  | SucBoard x => action_suc move x
  | AddBoard x => action_add move x
  | FailBoard => raise ERR "apply_move" ""
  )

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
