(* ========================================================================= *)
(* FILE          : rlRules.sml                                               *)
(* DESCRIPTION   : Theorem prover based on cut introduction                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlRules :> rlRules =
struct

open HolKernel boolLib Abbrev aiLib rlLib

val ERR = mk_HOL_ERR "rlRules"
val debugdir = HOLDIR ^ "/src/AI/work_in_progress/debug"
fun debug s = debug_in_dir debugdir "rlRules" s

(* -------------------------------------------------------------------------
   Rules of the games
   ------------------------------------------------------------------------- *)

datatype axiom = Refl | Inst of term

fun is_refl tm =
  let val (a,b) = dest_eq tm in a = b end handle HOL_ERR _ => false

fun is_inst a b = can (match_term a) b

val axl_glob =
   [``x + 0 = x``,``0 + x = x``,``x + SUC y = SUC (x + y)``,
    ``0 <> SUC x``,``SUC y + x  = SUC (x + y)``];

fun match_axiom tm =
  let val instl = filter (fn x => is_inst x tm) axl_glob in
    if is_refl tm then [Refl] else [] @ map Inst instl
  end

datatype proofstep =
  Sym of term |
  NegSym of term |
  Ap of term |
  Inj of term |
  Sub of ((int list * term) * term)

fun dest_stepsub step = case step of Sub y => y | _ => raise ERR "" "";

fun ap_tac tm = (snd o only_hd o fst o AP_TERM_TAC) ([],tm);

fun negsym_tac tm =
  let val (a,b) = dest_eq (dest_neg tm) in
    mk_neg (mk_eq (b,a))
  end

fun sym_tac tm =
  let val (a,b) = dest_eq tm in mk_eq (b,a) end

fun inj_tac tm =
  let
    val (a,b) = dest_eq (dest_neg tm)
    val (a',b') = (dest_suc a, dest_suc b)
  in
    mk_neg (mk_eq (a',b'))
  end

(* -------------------------------------------------------------------------
   Board position
   ------------------------------------------------------------------------- *)

datatype board =
  TacBoard of term |
  StopBoard of (term * int list) |
  LrBoard of (term * int list) |
  ImitBoard of ((term * int list) * term) |
  ConjunctBoard of (term * term)

type situation = bool * board

fun nntm_of_sit sit = case sit of
    (true, TacBoard tm) => tm
  | (true, StopBoard (tm,pos)) => tag_position (tm,pos)
  | (true, LrBoard (tm,pos)) => tag_position (tm,pos)
  | (true, ImitBoard ((tm,pos),res)) =>
    let
      val tm1 = hole_position (tm,pos)
      val tm2 = recover_cut tm (pos,res)
    in
      mk_conj (tm1,tm2)
    end
  | (false, ConjunctBoard (tm1,tm2)) => mk_conj (tm1,tm2)
  | _ => raise ERR "fevalpoli" ""

(* -------------------------------------------------------------------------
   Tactic move
   ------------------------------------------------------------------------- *)

datatype tacchoice = SymTac | NegSymTac | ApTac | InjTac | SubTac
val all_tacchoice = [SymTac,NegSymTac,ApTac,InjTac,SubTac]
fun string_of_tacchoice tac = case tac of
    SymTac    => "SymTac"
  | NegSymTac => "NegSymTac"
  | ApTac     => "ApTac"
  | InjTac    => "InjTac"
  | SubTac    => "SubTac"

fun move_tac tac sit = case sit of (p, TacBoard tm) =>
    ((
    case tac of
      SymTac    => (p, TacBoard (sym_tac tm))
    | NegSymTac => (p, TacBoard (negsym_tac tm))
    | ApTac     => (p, TacBoard (ap_tac tm))
    | InjTac    => (p, TacBoard (inj_tac tm))
    | SubTac    => (p, LrBoard (tm,[])) (* do not stop at equality *)
    ) handle HOL_ERR _ => (p, TacBoard F))
  | _ => raise ERR "move_tac" ""

(* -------------------------------------------------------------------------
   Position move
   ------------------------------------------------------------------------- *)

datatype stopchoice = Stop | Continue
val all_stopchoice = [Stop,Continue]
fun string_of_stopchoice stop = case stop of
    Stop     => "Stop"
  | Continue => "Continue"

fun move_stop stop sit = case sit of (p, StopBoard (tm,pos)) =>
    (
    case stop of
      Stop     => (p, ImitBoard ((tm,pos), active_var))
    | Continue =>
      let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
        case argl of
          []    => (p, ImitBoard ((tm,pos), active_var))
        | [a]   => (p, StopBoard (tm, pos @ [0]))
        | [a,b] => (p, LrBoard (tm,pos))
        | _     => raise ERR "descend_pos" " "
      end
    )
  | _ => raise ERR "move_stop" ""

datatype lrchoice = Left | Right
val all_lrchoice = [Left,Right]
fun string_of_lrchoice lr = case lr of
    Left  => "Left"
  | Right => "Right"

fun move_lr lr sit = case sit of (p, LrBoard (tm,pos)) =>
   (
   case lr of
     Left  => (p, StopBoard (tm, pos @ [0]))
   | Right => (p, StopBoard (tm, pos @ [1]))
   )
 | _ => raise ERR "move_lr" ""

(* -------------------------------------------------------------------------
   Residue move
   ------------------------------------------------------------------------- *)

datatype imitchoice = ImitZero | ImitSuc | ImitAdd
val all_imitchoice = [ImitZero,ImitSuc,ImitAdd]
fun string_of_imitchoice imit = case imit of
    ImitZero => "ImitZero"
  | ImitAdd  => "ImitAdd"
  | ImitSuc  => "ImitSuc"

val subzero = [{redex = active_var, residue = zero},
               {redex = pending_var, residue = active_var}];
val subsuc = [{redex = active_var, residue = mk_suc active_var}];
val subadd = [{redex = active_var, residue = mk_add (active_var,pending_var)}];

fun apply_imit imit tm = case imit of
    ImitZero => subst_occs [[1],[1]] subzero tm
  | ImitSuc  => subst_occs [[1]] subsuc tm
  | ImitAdd  => subst_occs [[1]] subadd tm

fun move_imit imit sit = case sit of (p, ImitBoard ((tm,pos),res)) =>
    let val newres = apply_imit imit res in
      if is_subtm active_var newres
      then (p, ImitBoard ((tm,pos),newres))
      else (not p,
        ConjunctBoard (sub_at_pos tm (pos,newres),
                       recover_cut tm (pos,newres)))
    end
  | _ => raise ERR "move_imit" ""

(* -------------------------------------------------------------------------
   Conjunct move
   ------------------------------------------------------------------------- *)

datatype conjunctchoice = ConjunctLeft | ConjunctRight
val all_conjunctchoice = [ConjunctLeft,ConjunctRight]
fun string_of_conjunctchoice conjunct = case conjunct of
    ConjunctLeft => "ConjunctLeft"
  | ConjunctRight => "ConjunctRight"

fun move_conjunct conjunct sit = case sit of (p, ConjunctBoard (tm1,tm2)) =>
    (case conjunct of
      ConjunctLeft => (not p, TacBoard tm1)
    | ConjunctRight => (not p, TacBoard tm2))
  | _ => raise ERR "move_conjunct" ""

(* -------------------------------------------------------------------------
   All moves
   ------------------------------------------------------------------------- *)

datatype move =
  TacMove of tacchoice |
  StopMove of stopchoice |
  LrMove of lrchoice |
  ImitMove of imitchoice |
  ConjunctMove of conjunctchoice

fun apply_move move sit = case move of
    TacMove tac           => move_tac tac sit
  | StopMove stop         => move_stop stop sit
  | LrMove lr             => move_lr lr sit
  | ImitMove imit         => move_imit imit sit
  | ConjunctMove conjunct => move_conjunct conjunct sit

fun string_of_move move = case move of
    TacMove tac           => string_of_tacchoice tac
  | StopMove stop         => string_of_stopchoice stop
  | LrMove lr             => string_of_lrchoice lr
  | ImitMove imit         => string_of_imitchoice imit
  | ConjunctMove conjunct => string_of_conjunctchoice conjunct


end (* struct *)
