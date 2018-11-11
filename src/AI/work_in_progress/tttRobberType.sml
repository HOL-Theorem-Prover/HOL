(* ========================================================================= *)
(* FILE          : tttRobberType.sml                                         *)
(* DESCRIPTION   : Datatypes for the robber theorem prover                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttRobberType :> tttRobberType =
struct

open HolKernel boolLib Abbrev

val ERR = mk_HOL_ERR "tttRobberType"

(* -------------------------------------------------------------------------
   Term tools
   ------------------------------------------------------------------------- *)

fun negate x = if is_neg x then dest_neg x else mk_neg x

fun is_subtm a b = can (find_term (fn x => x = a)) b

(* -------------------------------------------------------------------------
   Arithmetic tools
   ------------------------------------------------------------------------- *)

fun mk_suc x = mk_comb (``SUC``,x);
fun mk_add (a,b) = list_mk_comb (``$+``,[a,b]);
val zero = ``0``;

fun dest_suc x =
  let val (a,b) = dest_comb x in
    if a <> ``SUC`` then raise ERR "" "" else b
  end

fun dest_add tm =
  let val (oper,argl) = strip_comb tm in
    if oper <> ``$+`` then raise ERR "" "" else pair_of_list argl
  end

(* -------------------------------------------------------------------------
   Position tools
   ------------------------------------------------------------------------- *)

fun sub_at_pos tm (pos,res) =
  if null pos then res else
  let
    val (oper,argl) = strip_comb tm
    fun f i x =
      if i = hd pos then sub_at_pos x (tl pos,res) else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

fun subtm_at_pos pos tm =
  if null pos then tm else
  let val (oper,argl) = strip_comb tm in
    subtm_at_pos (tl pos) (List.nth (argl,hd pos))
  end

fun recover_cut tm (pos,res) =
  let val red = subtm_at_pos pos tm in mk_eq (red,res) end

(* -------------------------------------------------------------------------
   Tactic tools
   ------------------------------------------------------------------------- *)

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
   Proof state
   ------------------------------------------------------------------------- *)

datatype board =
  ConjChoice of (term * term) |
  TacChoice of term |
  StopChoice of (term * int list) |
  LrChoice of (term * int list) |
  ImitChoice of ((term * int list) * term)

(* -------------------------------------------------------------------------
   Choice of a conjunct
   ------------------------------------------------------------------------- *)

datatype conjchoice = First | Second

fun move_conj conj sit = case sit of (p, ConjChoice (tm1,tm2)) =>
    (
    case altern of
      First     => (not p, TacChoice tm1)
    | Second    => (not p, TacChoice tm2)
    )
  | _ => raise ERR "move_altern" ""

(* -------------------------------------------------------------------------
   Choice and application of a tactic
   ------------------------------------------------------------------------- *)

datatype tacchoice = SymTac | NegSymTac | ApTac | InjTac | SubTac | AlternTac

fun move_tac tac sit = case sit of (p, TacChoice tm) =>
    (
    case tac of
      SymTac    => (p, TacChoice (sym_tac tm))
    | NegSymTac => (p, TacChoice (negsym_tac tm))
    | ApTac     => (p, TacChoice (ap_tac tm))
    | InjTac    => (p, TacChoice (inj_tac tm))
    | SubTac    => (p, StopChoice (tm,[]))
    | AlternTac => (not p, TacChoice (negate tm))
    )
  | _ => raise ERR "move_tac" ""

(* -------------------------------------------------------------------------
   Choice of a position in a term
   ------------------------------------------------------------------------- *)

datatype stopchoice = Stop | Continue

val active_var = ``active_var : num``

fun move_stop stop sit = case sit of (p, StopChoice (tm,pos)) =>
    (
    case stop of
      Stop     => (p, ResChoice ((tm,pos), active_var))
    | Continue =>
      let val (_,argl) = strip_comb (subtm_at_pos pos tm) in
        case argl of
          []    => (p, ResChoice ((tm,pos), active_var))
        | [a]   => (p, StopChoice (tm, pos @ [0]))
        | [a,b] => (p, LrChoice (tm,pos))
        | _     => raise ERR "descend_pos" " "
      end
    )
  | _ => raise ERR "move_stop" ""

datatype lrchoice = Left | Right

fun move_lr lr sit = case sit of (p, LrChoice (tm,pos)) =>
   (
   case lr of
     Left  => (p, StopChoice (tm, pos @ [0]))
   | Right => (p, StopChoice (tm, pos @ [1]))
   )
 | _ => raise ERR "move_lr" ""

(* -------------------------------------------------------------------------
   Choice of a residue to insert at a selected position.
   ------------------------------------------------------------------------- *)

datatype imitchoice = ImitZero | ImitSuc | ImitAdd

val pending_var = ``pending_var : num``

val subzero = [{redex = active_var, residue = zero},
               {redex = pending_var, residue = active_var}];
val subsuc = [{redex = active_var, residue = mk_suc active_var}];
val subadd = [{redex = active_var, residue = mk_add (active_var,pending_var)}];

fun apply_imit imit tm = case imit of
    ImitZero => subst_occs [[1],[1]] subzero tm
  | ImitSuc  => subst_occs [[1]] subsuc tm
  | ImitAdd  => subst_occs [[1]] subadd tm

fun move_imit imit sit = case sit of (p, ResChoice ((tm,pos),res)) =>
    let val newres = apply_imit imit res in
      if is_subtm active_var newres
      then (p, ResChoice ((tm,pos),newres))
      else (not p,
            TermChoice (sub_at_pos tm (pos,res), recover_cut tm (pos,res))
    end
  | _ => raise ERR "move_imit" ""



end (* struct *)
