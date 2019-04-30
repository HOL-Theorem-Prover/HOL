(* ========================================================================= *)
(* FILE          : rlGameCopy.sml                                            *)
(* DESCRIPTION   : Specification of a term copying game                      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure rlGameCopy :> rlGameCopy =
struct

open HolKernel Abbrev boolLib aiLib rlLib psMCTS psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlGameCopy"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (term * term)

val active_var = ``active_var:num``;
val pending_var = ``pending_var:num``;

fun mk_startsit target = (true,(target,active_var))
fun is_ground tm = not (tmem active_var (free_vars_lr tm))

val operl = [(active_var,0),(pending_var,0)] @ operl_of ``SUC 0 + 0 = 0``
fun nntm_of_sit (_,(ctm,tm)) = mk_eq (ctm,tm)

fun status_of (_,(ctm,tm)) = 
  if term_eq ctm tm then Win
  else if term_size tm > term_size ctm orelse is_ground tm then Lose
  else Undecided
 
(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0 + 0``

fun action_oper (oper,n) tm =
  let
    val res = if n = 0 then tm else 
      list_mk_comb (oper, active_var :: 
        List.tabulate (n - 1,fn _ => pending_var)) 
    val sub = [{redex = active_var, residue = res}]
  in
    subst sub tm
  end

fun apply_move move (_,(ctm,tm)) = (true, (ctm, action_oper move tm))

fun mk_targetl level ntarget = 
  let 
    val range = List.tabulate (level, fn x => x + 1)
    fun gen () = random_term_uni (map fst movel) (range,``:num``)
    val d = ref (dempty Term.compare)
    fun loop n = 
      if n > 10 * ntarget then raise ERR "not enough different terms" "" else
      if dlength (!d) >= ntarget then () else
      let val tm = gen () in
        if dmem tm (!d) then () else d := dadd tm () (!d);
        loop (n + 1)
      end
  in
    loop 0; dkeys (!d)
  end


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
  nntm_of_sit: board sit -> term,
  mk_targetl: int -> int -> term list
  }

val gamespec =
  {
  mk_startsit = mk_startsit,
  movel = movel,
  status_of = status_of,
  apply_move = apply_move,
  operl = operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl
  }

end (* struct *)
