(* ========================================================================= *)
(* FILE          : rlGameArithGround.sml                                     *)
(* DESCRIPTION   :                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameArithGround :> rlGameArithGround =
struct

open HolKernel boolLib Abbrev aiLib rlLib rlTruth psMCTS psTermGen

val ERR = mk_HOL_ERR "rlGameArithGround"
val debugdir = HOLDIR ^ "/src/AI/reinforcement_learning/debug"
fun debug s = debug_in_dir debugdir "rlGameArithGround" s

(* -------------------------------------------------------------------------
   Tools
   ------------------------------------------------------------------------- *)

fun rename_varl f tm =
  snd (strip_abs (rename_bvarl f (list_mk_abs (free_vars_lr tm,tm))))
fun sym tm = mk_eq (swap (dest_eq tm))
fun unify a b = Unify.simp_unify_terms [] a b

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type pos = int list
type pb = (term * pos)
datatype board = Board of pb | FailBoard

fun mk_startsit tm = (true, Board (tm,[]))

fun is_proven (tm,pos) =
  null pos andalso let val (t1,t2) = dest_eq tm in term_eq t1 t2 end

fun status_of sit = case snd sit of
    Board pb => if is_proven pb then Win else Undecided
  | FailBoard => Lose

(* -------------------------------------------------------------------------
   Constants and variables
   ------------------------------------------------------------------------- *)

val numtag = mk_var ("numtag", ``:num -> num``)

fun tag_pos (tm,pos) =
  if null pos then (if is_eq tm then tm else mk_comb (numtag,tm)) else
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = if i = hd pos then tag_pos (arg,tl pos) else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

(* -------------------------------------------------------------------------
   Axioms and theorems
   ------------------------------------------------------------------------- *)

val ax1 = ``x + 0 = x``;
val ax2 = ``x * 0 = 0``
val ax3 = ``x + SUC y = SUC (x + y)``
val ax4 = ``x * SUC y = x * y + x``
val axl = map (rename_varl (fn x => "")) [ax1,ax3]
val ax_vect = Vector.fromList axl

(* -------------------------------------------------------------------------
   Neural network units and inputs
   ------------------------------------------------------------------------- *)

val dimin = 8;

val operl =
  let val operl' = (numtag,1) :: operl_of (``0 * SUC 0 + 0 = 0``) in
    mk_fast_set oper_compare operl'
  end

fun nntm_of_sit sit = case snd sit of
    Board (tm,pos) => tag_pos (tm,pos)
  | FailBoard => T

(* -------------------------------------------------------------------------
   Paramodulation (used as a rewrite tool here since targets are ground)
   ------------------------------------------------------------------------- *)

fun paramod eq (tm,pos) =
  if null pos then NONE else
  let
    val (eql,eqr) = dest_eq eq
    val subtm = find_subtm (tm,pos)
    val sigma = unify eql subtm
    val eqrsig = subst sigma eqr
    val tmsig = subst sigma tm
    val result = subst_pos (tmsig,pos) eqrsig
  in
    if term_eq result tm orelse length (free_vars_lr result) > 0
    then NONE
    else SOME result
  end
  handle HOL_ERR _ => NONE

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Arg of int | Paramod of (int * bool)

val movel =
  let fun f i = [Paramod (i,true),Paramod (i,false)] in 
    map Arg [0,1] @ List.concat (List.tabulate (length axl, f))
  end

fun bts b = if b then "t" else "f"

fun string_of_move move = case move of
    Arg n => ("A" ^ its n)
  | Paramod (i,b) => ("P" ^ its i ^ bts b)

fun narg tm = length (snd (strip_comb tm))

fun argn_pb n (tm,pos) = SOME (tm,pos @ [n])

fun paramod_pb (i,b) (tm,pos) =
  let
    val ax = Vector.sub (ax_vect,i)
    val tmo = paramod (if b then ax else sym ax) (tm,pos)
  in
    SOME (valOf tmo,[]) handle Option => NONE
  end

fun available subtm (move,r:real) = case move of
    Arg i => (narg subtm >= i + 1)
  | Paramod (i,b) => if is_eq subtm then false else
    let val ax = Vector.sub (ax_vect,i) in
      if b
      then can (unify (lhs ax)) subtm
      else can (unify (rhs ax)) subtm
    end

fun filter_sit sit = case snd sit of
    Board (tm,pos) =>
      let val subtm = find_subtm (tm,pos) in List.filter (available subtm) end
  | FailBoard => (fn l => [])

fun apply_move move sit =
  (true, case snd sit of Board pb =>
    Board (valOf (
      case move of
        Arg n => argn_pb n pb
      | Paramod (i,b) => paramod_pb (i,b) pb
    ))
  | FailBoard => raise ERR "move_sub" ""
  )
  handle Option => (true, FailBoard)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

type gamespec =
  {
  filter_sit : board sit -> ((move * real) list -> (move * real) list),
  movel : move list,
  string_of_move : move -> string,
  status_of : (board psMCTS.sit -> psMCTS.status),
  apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
  operl : (term * int) list,
  dim : int,
  nntm_of_sit: board sit -> term
  }

val gamespec : gamespec =
  {
  filter_sit = filter_sit,
  string_of_move = string_of_move,
  movel = movel,
  status_of = status_of,
  apply_move = apply_move,
  operl = operl,
  dim = dimin,
  nntm_of_sit = nntm_of_sit
  }

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

fun total_cost_target target = case target of
    (true, Board (tm,[])) => total_cost tm
  | _ => raise ERR "total_cost_target" ""


fun mk_targetl maxsize = 
  let 
    fun cmp (a,b) = Int.compare (snd a,snd b)
    val tml1 = mk_term_set (mk_addsuceq 10) 
    val tml2 = map_assoc total_cost tml1
    val tml3 = map fst (dict_sort cmp tml2)
  in
    map mk_startsit (first_n (maxsize * 100) tml3) 
  end





end (* struct *)
