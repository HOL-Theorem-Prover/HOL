(* ========================================================================= *)
(* FILE          : mleSynthesize.sml                                         *)
(* DESCRIPTION   : Specification of a term copying game                      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure rlGameCopy :> rlGameCopy =
struct

open HolKernel Abbrev boolLib aiLib rlLib psMCTS psTermGen 
  mlTreeNeuralNetwork mlTacticData smlParallel

val ERR = mk_HOL_ERR "rlGameCopy"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (term * term)

val active_var = ``active_var:num``;

fun mk_startsit target = (true,(target,active_var))
fun is_ground tm = not (tmem active_var (free_vars_lr tm))

val operl = [(active_var,0)] @ operl_of ``SUC 0 + 0 = 0``
fun nntm_of_sit (_,(ctm,tm)) = mk_eq (ctm,tm)

fun status_of (_,(ctm,tm)) = 
  if term_eq ctm tm then Win
  else if term_size tm > term_size ctm orelse is_ground tm then Lose
  else Undecided
 
fun write_targetl targetl = 
  let val tml = map (fst o snd) targetl in 
    export_terml (!parallel_dir ^ "/targetl") tml
  end

fun read_targetl () =
  let val tml = import_terml (!parallel_dir ^ "/targetl") in
    map mk_startsit tml
  end  

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0 + 0``

fun action_oper (oper,n) tm =
  let
    val res = list_mk_comb (oper, List.tabulate (n, fn _ => active_var)) 
    val sub = [{redex = active_var, residue = res}]
  in
    subst_occs [[1]] sub tm
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
    loop 0; map mk_startsit (dkeys (!d))
  end

fun filter_sit sit = (fn l => l) (* filter moves *)

fun string_of_move (tm,_) = tts tm

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

type gamespec =
  {
  movel: move list,
  status_of : (board psMCTS.sit -> psMCTS.status),
  filter_sit : board psMCTS.sit -> ((move * real) list -> (move * real) list),
  apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
  operl : (term * int) list,
  nntm_of_sit: board psMCTS.sit -> term,
  mk_targetl: int -> int -> board psMCTS.sit list,
  write_targetl: board psMCTS.sit list -> unit,
  read_targetl: unit -> board psMCTS.sit list,
  string_of_move : move -> string
  }

val gamespec =
  {
  movel = movel,
  status_of = status_of,
  filter_sit = filter_sit,
  apply_move = apply_move,
  operl = operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  string_of_move = string_of_move
  }

end (* struct *)
