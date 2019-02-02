(* ========================================================================= *)
(* FILE          : rlGameAim.sml                                             *)
(* DESCRIPTION   : Problems from the AIM conjecture                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlGameAim :> rlGameAim =
struct

open HolKernel Abbrev boolLib aiLib rlLib smlLexer 
  mlTreeNeuralNetwork psMCTS

val ERR = mk_HOL_ERR "rlGameAim"

(* -------------------------------------------------------------------------
   Renaming
   ------------------------------------------------------------------------- *)

fun rename_evarl_aux f tm =
  let
    val vi = ref 0
    fun rename_aux tm = case dest_term tm of
      VAR(Name,Ty)       => tm
    | CONST{Name,Thy,Ty} => tm
    | COMB(Rator,Rand)   => mk_comb (rename_aux Rator, rename_aux Rand)
    | LAMB(Var,Bod)      =>
      let
        val vs = f (fst (dest_var Var))
        val new_tm = rename_bvar ("v" ^ int_to_string (!vi) ^ vs) tm
        val (v,bod) = dest_abs new_tm
        val _ = incr vi
      in
        mk_abs (v, rename_aux bod)
      end
  in
    rename_aux tm
  end

val max_evar = 5;
val evarl =
  let fun f i = mk_var ("v" ^ int_to_string i, alpha) in
    List.tabulate (max_evar,f)
  end;

val evarltm =
  let fun f i = mk_var ("v" ^ int_to_string i ^ "_tm", alpha) in
    List.tabulate (max_evar,f)
  end; 

val evarleq =
  let fun f i = mk_var ("v" ^ int_to_string i ^ "_eq", alpha) in
    List.tabulate (max_evar,f)
  end; 

val evarlinter = evarltm @ evarleq

fun rename_evarl f tm =
  let val vl = filter (fn x => mem x evarl) (free_vars_lr tm) in 
    snd (strip_abs (rename_evarl_aux f (list_mk_abs (vl,tm))))
  end

fun renameb_evarl f tm =
  let val vl = filter (fn x => mem x evarlinter) (free_vars_lr tm) in 
    snd (strip_abs (rename_evarl_aux f (list_mk_abs (vl,tm))))
  end

fun rename_skolem toptm =
  let 
    val dref = ref (dempty Term.compare)
    fun loop tm = case dest_term tm of
      VAR(Name,Ty) => 
      if String.sub (Name,0) = #"v" then 
        if dmem tm (!dref) then dfind tm (!dref) else 
          let val newvar = mk_var ("c" ^ its (dlength (!dref)), Ty) in 
            dref := dadd tm newvar (!dref); newvar
          end
      else tm
    | COMB(Rator,Rand) => mk_comb (loop Rator, loop Rand)
    | _ => tm
  in
    loop toptm
  end

(* -------------------------------------------------------------------------
   Reading functions
   ------------------------------------------------------------------------- *)

val aim_eq = mk_var ("=",``:'a -> 'a -> 'a``)
fun aim_mk_eq (a,b) = list_mk_comb (aim_eq, [a,b])
fun aim_dest_eq tm = case strip_comb tm of
    (aim_eq, [a,b]) => (a,b)
  | _ => raise ERR "aim_dest_eq" "" 

val aim_conj = mk_var ("aim_conj",``:'a -> 'a -> 'a``)
fun aim_mk_conj (a,b) = list_mk_comb (aim_conj, [a,b])

fun thm_of_ivy l = case l of 
    [Lterm (Lstring "TOP" :: _ :: Lstring _ :: t1 :: t2 :: m)] => 
    SOME (aim_mk_eq (term_of_lisp t1, term_of_lisp t2))
 (* | [Lterm (Lstring "TOP" :: _ :: Lstring _ :: t1 :: t2 :: m)] => 
    NONE *)
  | [Lterm (Lstring "INTERM" :: m)] => NONE
  | _ => raise ERR "thm_of_ivy" ""

fun ax_of_ivy l = case l of 
    [Lterm (Lstring "IVYKNOWN" :: _ :: t :: m)] => term_of_lisp t
  | _ => raise ERR "ax_of_ivy" ""

fun read_thm line = (thm_of_ivy o lisp_of o partial_sml_lexer) line
fun read_thml file = map rename_skolem (List.mapPartial read_thm (readl file))

fun read_ax line = (ax_of_ivy o lisp_of o partial_sml_lexer) line
fun read_axl file = map read_ax (readl file)

fun is_cvar tm = is_var tm andalso String.sub (fst (dest_var tm),0) = #"c";

(* -------------------------------------------------------------------------
   Reading AIM problems
   ------------------------------------------------------------------------- *)

val axfile = "/home/thibault/big/forthibault2.lisp";
val axl = read_axl axfile;
val ax_vect = Vector.fromList axl;

val dir = "/home/thibault/big/aimleapinfoJan292019";
val filel = 
  let fun f i = dir ^ "/trainingdatapart" ^ its i ^ ".lisp" in
    List.tabulate (10,f)
  end;
val thml = List.concat (map read_thml filel);

val axvarl =
  let fun f i = mk_var ("A" ^ int_to_string i, alpha) in
    List.tabulate (Vector.length ax_vect,f)
  end

val aim_tag = mk_var ("aim_tag",``:'a->'a``)

val operl = 
  let val operl_aux = List.concat (map operl_of_term (thml @ axl)) in
    (aim_tag,1) :: (aim_conj,2) :: map (fn x => (x,0)) (axvarl @ evarl) @
    mk_fast_set oper_compare operl_aux
  end

val constl = list_diff (map fst operl) evarl;

fun aim_unify a b = Unify.simp_unify_terms constl a b

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type pos = int list
type pb = ((term * pos) * int option)
datatype board = Board of pb | FailBoard

fun mk_startsit pb = (true, Board pb)

fun is_proven ((tm,_),_) = 
  let val (t1,t2) = aim_dest_eq tm in can (aim_unify t1) t2 end

fun status_of sit = case snd sit of
    Board pb => if is_proven pb then Win else Undecided
  | FailBoard => Lose

fun pb_of_thm thm = ((thm,[]),NONE)

val targetl = map (mk_startsit o pb_of_thm) thml

(* -------------------------------------------------------------------------
   Neural network interface
   ------------------------------------------------------------------------- *)

fun aim_tag_pos (tm,pos) =
  if null pos then mk_comb (aim_tag,tm) else
  let
    val (oper,argl) = strip_comb tm
    fun f i arg =
      if i = hd pos then aim_tag_pos (arg,tl pos) else arg
  in
    list_mk_comb (oper, mapi f argl)
  end

fun nntm_of_pb pb = case pb of 
    ((tm,pos), SOME i) => 
    aim_mk_conj (aim_tag_pos (tm,pos), mk_var ("A" ^ int_to_string i, alpha))
  | ((tm,_), NONE) => tm

fun nntm_of_sit sit = case snd sit of
    Board pb => nntm_of_pb pb
  | FailBoard => T

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = ChooseAx of int | Arg0 | Arg1 | Arg2 | ParamodL | ParamodR

val movel = List.tabulate (length axl, ChooseAx) @ 
  [Arg0, Arg1, Arg2, ParamodL, ParamodR]

fun filter_sit sit = case snd sit of
    Board ((tm,pos),NONE) => (fn l => first_n (length axl) l)
  | Board ((tm,pos),SOME i) => (fn l => (rev o (first_n 5) o rev) l)
  | FailBoard => (fn l => [])

(* simp unify terms may be slow *)
fun paramod eq (tm,pos) =
  if null pos then NONE else
  let
    val eqrenamed = rename_evarl (fn x => "_eq") eq
    val tmrenamed = rename_evarl (fn x => "_tm") tm
    val (s,t) = aim_dest_eq eqrenamed
    val u = subtm_at_pos pos tmrenamed
    val sigma = aim_unify s u
    val tsigma = subst sigma t
    val tmsigma = subst sigma tmrenamed
    val r = sub_at_pos tmsigma (pos,tsigma)
    val vl = filter (fn x => mem x evarlinter) (free_vars_lr r)
  in
    if r = tmrenamed orelse length vl >= max_evar 
    then NONE 
    else SOME (renameb_evarl (fn x => "") r)
  end
  handle HOL_ERR _ => NONE

fun argn_pb n pb = case pb of
    ((tm,pos), SOME i) => if not (more_arg (n+1) (tm,pos)) then NONE else 
    SOME ((tm,pos @ [n]), SOME i)
  | _ => NONE

fun sym tm = aim_mk_eq (swap (aim_dest_eq tm))

fun paramod_pb direction pb = case pb of
    ((tm,pos), SOME i) =>
    let 
      val eq  = Vector.sub (ax_vect,i)
      val eq' = if direction then eq else sym eq
      val tmo = paramod eq' (tm,pos) 
    in
      SOME ((valOf tmo, []), NONE) handle Option => NONE
    end
  | _ => NONE

fun chooseax_pb i pb = 
  case pb of (x, NONE) => SOME (x, SOME i) | _ => NONE

fun apply_move move sit = (true, case snd sit of Board pb =>
    Board (valOf (
    case move of
      ChooseAx i => chooseax_pb i pb
    | Arg0 => argn_pb 0 pb
    | Arg1 => argn_pb 1 pb
    | Arg2 => argn_pb 2 pb
    | ParamodL => paramod_pb true pb
    | ParamodR => paramod_pb false pb
    ))
  | FailBoard => raise ERR "move_sub" ""
  )
  handle Option => (true, FailBoard)

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val dimin = 10

type gamespec =
  {
  mk_startsit : pb -> board sit,
  filter_sit : board sit -> ((move * real) list -> (move * real) list),
  movel : move list,
  status_of : (board psMCTS.sit -> psMCTS.status),
  apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
  operl : (term * int) list,
  dim : int,
  nntm_of_sit: board sit -> term
  }

val gamespec : gamespec =
  {
  mk_startsit = mk_startsit,
  filter_sit = filter_sit,
  movel = movel,
  status_of = status_of,
  apply_move = apply_move,
  operl = operl,
  dim = dimin,
  nntm_of_sit = nntm_of_sit
  }



end (* struct *)

(*
app load ["rlAim", "aiLib", "rlLib", "smlLexer", "mlTreeNeuralNetwork"]; 
open rlAim aiLib rlLib smlLexer mlTreeNeuralNetwork;

val dim = 10;
val randtnn = random_treenn (dim,1) operl;
val tnn = train_tnn_eval dim randtnn (trainset,testset);
*)


