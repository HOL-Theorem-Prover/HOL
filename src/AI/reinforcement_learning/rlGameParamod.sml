(* ========================================================================= *)
(* FILE          : rlGameParamod.sml                                         *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameParamod :> rlGameParamod =
struct

open HolKernel boolLib Abbrev aiLib rlLib psMCTS psTermGen

val ERR = mk_HOL_ERR "rlGameParamod"
val debugdir = HOLDIR ^ "/src/AI/reinforcement_learning/debug"
fun debug s = debug_in_dir debugdir "rlGameParamod" s

(* -------------------------------------------------------------------------
   Tools
   ------------------------------------------------------------------------- *)

fun rename_varl f tm =
  snd (strip_abs (rename_bvarl f (list_mk_abs (free_vars_lr tm,tm))))

fun basic_rename tm = rename_varl (fn x => "") tm

fun sym tm = mk_eq (swap (dest_eq tm))

(* -------------------------------------------------------------------------
   State
   ------------------------------------------------------------------------- *)

type pos = int list
type pb = ((term * bool) * pos) list
datatype board = Board of pb | FailBoard

fun mk_startsit pb = (true, Board pb)

fun is_proven ((tm,b),_) =
  let val (t1,t2) = dest_eq tm in (t1 = t2 andalso not b) end

fun status_of sit = case snd sit of
    Board pb =>
      if null pb then Lose else
      (if exists is_proven pb then Win else Undecided)
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   Neural network interface
   ------------------------------------------------------------------------- *)

val operl1 = (numtag_var,1) :: operl_of_term ``SUC 0 + 0 = 0 * 0``;
val dim = 10;
val max_var = 5;

val ax1 = ``x + 0 = x``
val ax2 = ``x * 0 = 0``
val ax3 = ``x + SUC y = SUC (x + y)``
val ax4 = ``x * SUC y = x * y + x``
val axl = map basic_rename [ax1,ax2,ax3,ax4]

val varl2 =
  let fun f i = mk_var ("V" ^ int_to_string i, ``:num``) in
    List.tabulate (max_var,f)
  end

val varl3 =
  let fun f i = mk_var ("Ax" ^ int_to_string i, bool) in
    List.tabulate (length axl,f)
  end

val axvl = combine (axl,varl3)

val operl2 = (map (fn x => (x,0)) (varl2 @ varl3) @ operl_of_term ``~ (V0:num = V0) /\ (V0:num = V0)``);

val operl = 
  mk_fast_set (cpl_compare Term.compare Int.compare) (operl1 @ operl2);

fun nntm_of_cl ((tm,b),pos) =
  let val tm' = tag_position (tm, pos) in
    if b then tm' else mk_neg tm'
  end

fun nntm_of_ax ((ax,_),_) = assoc ax axvl 

fun nntm_of_pb pb = case pb of 
    [] => T
  | a :: m => list_mk_conj (nntm_of_cl a :: map nntm_of_ax m)

fun nntm_of_sit sit = case snd sit of
    Board pb => nntm_of_pb pb
  | FailBoard => T

(* -------------------------------------------------------------------------
   Action
   ------------------------------------------------------------------------- *)

(*  app has alwasy arity 2 so no need for Down *)
datatype move = Down | Left | Right | Rotate | ParamodR | ParamodL

val movel = [Down, Left, Right, Rotate, ParamodR, ParamodL]

fun n_arg n (tm,pos) =
  let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
    length argl = n
  end

(* simp unify terms may be slow *)
fun paramod eq (tm,pos) =
  if null pos then NONE else
  let
    val eqrenamed = rename_varl (fn x => "_eq") eq
    val tmrenamed = rename_varl (fn x => "_tm") tm
    val (s,t) = dest_eq eqrenamed
    val u = subtm_at_pos pos tmrenamed
    val sigma = Unify.simp_unify_terms [] s u
    val tsigma = subst sigma t
    val tmsigma = subst sigma tmrenamed
    val r = sub_at_pos tmsigma (pos,tsigma)
  in
    if r = tmrenamed orelse length (free_vars_lr r) > max_var 
    then NONE 
    else SOME (basic_rename r)
  end
  handle HOL_ERR _ => NONE

fun down_pb pb = case pb of
    ((tm,b),pos) :: m => if not (n_arg 1 (tm,pos)) then NONE else
    SOME ( ((tm,b),pos @ [0]) :: m )
  | _ => NONE

fun left_pb pb = case pb of
    ((tm,b),pos) :: m => if not (n_arg 2 (tm,pos)) then NONE else
    SOME ( ((tm,b),pos @ [0]) :: m )
  | _ => NONE

fun right_pb pb = case pb of
    ((tm,b),pos) :: m => if not (n_arg 2 (tm,pos)) then NONE else
    SOME ( ((tm,b),pos @ [1]) :: m )
  | _ => NONE

fun rotate_pb pb = case pb of
    a :: b :: m => if null m then NONE else SOME (a :: (m @ [b]))
  | _ => NONE

fun swap_pb pb = NONE (* case pb of
    a :: b :: m => SOME (b :: a :: m)
  | _ => NONE *)

fun paramodl_pb pb = case pb of
    ((tm,b),postm) :: ((eq,true),poseq) :: m =>
    let val tmo = paramod eq (tm,postm) in
      SOME (((valOf tmo,b),[]) (* :: ((tm,b),postm) *) 
        :: ((eq,true),poseq) :: m)
      handle Option => NONE
    end
  | _ => NONE

fun paramodr_pb pb = case pb of
    ((tm,b),postm) :: ((eq,true),poseq) :: m =>
    let val tmo = paramod (sym eq) (tm,postm) in
      SOME (((valOf tmo,b),[]) (* :: ((tm,b),postm) *) 
        :: ((eq,true),poseq) :: m)
      handle Option => NONE
    end
  | _ => NONE


fun sym_pb pb = case pb of
    a :: ((tm,b),_) :: m => (SOME (a :: ((sym tm,b),[]) :: m) 
                             handle HOL_ERR _ => NONE)
  | _ => NONE

fun apply_move move sit = (true, case snd sit of Board pb =>
    Board (valOf (
    case move of
      Down => down_pb pb
    | Left => left_pb pb
    | Right => right_pb pb
    | Rotate => rotate_pb pb
    | ParamodL => paramodl_pb pb
    | ParamodR => paramodr_pb pb
    ))
  | FailBoard => raise ERR "move_sub" ""
  )
  handle Option => (true, FailBoard)

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

(* -------------------------------------------------------------------------
   Target generator
   ------------------------------------------------------------------------- *)

fun eval_ground tm = (rhs o concl o EVAL) tm

fun mk_targetl maxsize n =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size maxsize (``:num``,cset)
    val tml1 = filter (fn x => eval_ground x = ``0``) tml0
    fun init_ax ax = ((ax,true),[]: int list)
    fun random_eq () = mk_eq (random_elem tml1, random_elem tml1)
    fun random_pb () = ((random_eq (), false), []) :: map init_ax axl
  in
    map mk_startsit (List.tabulate (n, fn _ => random_pb ()))
  end


end (* struct *)
