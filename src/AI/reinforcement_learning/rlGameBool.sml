(* ========================================================================= *)
(* FILE          : rlGameRewrite.sml                                         *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameBool :> rlGameBool =
struct

open HolKernel boolLib Abbrev aiLib rlLib psMCTS

val ERR = mk_HOL_ERR "rlGameBool"
val debugdir = HOLDIR ^ "/src/AI/reinforcement_learning/debug"
fun debug s = debug_in_dir debugdir "rlGameBool" s

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

type pb = ((term * bool) list) list

datatype board = Board of pb | FailBoard

val clause_compare = list_compare (cpl_compare Term.compare bool_compare)

fun simplify_cl cl =
  let val d = dregroup Term.compare cl in
    if exists (fn (_,l) => length l > 1) (dlist d)
    then NONE
    else SOME (mk_sameorder_set (cpl_compare Term.compare bool_compare) cl)
  end

fun simplify_pb pb =
  mk_sameorder_set clause_compare (List.mapPartial simplify_cl pb)

fun mk_startsit pb = (true, Board pb)

fun status_of sit = case snd sit of
    Board pb =>
      if null pb then Lose else
      (if exists null pb then Win else Undecided)
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   State representation
   ------------------------------------------------------------------------- *)

val varl =
  let fun f i = mk_var ("x" ^ int_to_string i, bool) in
    List.tabulate (3,f)
  end

val operl =
  mk_fast_set (cpl_compare Term.compare Int.compare)
    (map (fn x => (x,0)) varl @ operl_of_term ``(~x0 \/ x0 /\ x0)``);

val dim = 10;

fun mk_lit (v,b) = if b then v else mk_neg v
fun nntm_of_cl cl = list_mk_disj (map mk_lit cl)

fun nntm_of_pb pb = list_mk_conj (map nntm_of_cl pb)

fun nntm_of_sit sit = case snd sit of
    Board pb => if null pb then T else
                if exists null pb then F else nntm_of_pb pb
  | FailBoard => T

(* -------------------------------------------------------------------------
   Moves
   ------------------------------------------------------------------------- *)

datatype move = Rotate | Swap | RotateCl | Resolve | Delete

val movel = [Rotate, Swap, RotateCl, Resolve, Delete]

fun rotate_pb pb = case pb of
    a :: m => if null m then NONE else SOME (m @ [a])
  | _ => NONE

fun swap_pb pb = case pb of
    a :: b :: m => SOME (b :: a :: m)
  | _ => NONE

fun rotate_cl pb = case pb of
    (a' :: m') :: m => if null m' then NONE else SOME ((m' @ [a']) :: m)
  | _ => NONE

fun resolve_pb pb = case pb of
    ((a1,true) :: m1) :: ((a2,false) :: m2) :: m =>
     if a1 = a2
     then SOME (simplify_pb ((m1 @ m2) :: pb))
     else NONE
  | _ => NONE

fun delete_pb pb = if null pb then NONE else SOME (tl pb)

fun apply_move move sit = ((true,
  case snd sit of Board pb =>
    (Board (
    case move of
      Rotate => valOf (rotate_pb pb)
    | Swap => valOf (swap_pb pb)
    | RotateCl => valOf (rotate_cl pb)
    | Resolve => valOf (resolve_pb pb)
    | Delete => valOf (delete_pb pb)
    ))
  | FailBoard => raise ERR "move_sub" "")
  )
  handle Option => (true, FailBoard)

(* -------------------------------------------------------------------------
   Target generation
   ------------------------------------------------------------------------- *)

fun random_lit () =
  let val x = random_elem varl in
    random_elem [(x,true), (x,false)]
  end

fun random_clause () =
  map random_lit (List.tabulate (random_int (1,2), fn _ => ()))

fun random_problem () =
  map random_clause (List.tabulate (random_int (2,5), fn _ => ()))

fun mk_targetl n =
  let
    val l = ref []
    fun f () =
      let
        val pb =
          let fun loop () =
            let val pb' = simplify_pb (random_problem ()) in
              if (null pb' orelse exists null pb') then loop () else pb'
            end
          in loop () end
        val tm = mk_imp (nntm_of_pb pb, F)
      in
        if can (BasicProvers.PROVE []) tm
        then l := pb :: !l
        else ()
      end
  in
    while length (!l) < n do f ();
    !l
  end

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

type gamespec =
  {
  mk_startsit: pb -> board sit,
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
