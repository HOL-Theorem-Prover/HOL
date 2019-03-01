(* ========================================================================= *)
(* FILE          : rlLib.sml                                                 *)
(* DESCRIPTION   : Reinforcement learning library                            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlLib :> rlLib =
struct

open HolKernel Abbrev boolLib aiLib
mlFeature mlNearestNeighbor mlTreeNeuralNetwork numTheory

val ERR = mk_HOL_ERR "rlProve"

type pos = int list

(* -------------------------------------------------------------------------
   Neural network units
   ------------------------------------------------------------------------- *)

val oper_compare = cpl_compare Term.compare Int.compare

fun all_fosubtm tm =
  let val (oper,argl) = strip_comb tm in
    tm :: List.concat (map all_fosubtm argl)
  end

fun operl_of tm =
  let
    val tml = mk_fast_set Term.compare (all_fosubtm tm)
    fun f x = let val (oper,argl) = strip_comb x in (oper, length argl) end
  in
    mk_fast_set oper_compare (map f tml)
  end

(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

fun subst_pos (tm,pos) res =
  if null pos then res else
  let
    val (oper,argl) = strip_comb tm
    fun f i x = if i = hd pos then subst_pos (x,tl pos) res else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

fun find_subtm (tm,pos) =
  if null pos then tm else
  let val (oper,argl) = strip_comb tm in
    find_subtm (List.nth (argl,hd pos), tl pos)
  end

fun narg_ge n (tm,pos) =
  let val (_,argl) = strip_comb (find_subtm (tm,pos)) in length argl >= n end

(* -------------------------------------------------------------------------
   Arithmetic
   ------------------------------------------------------------------------- *)

fun mk_suc x = mk_comb (``SUC``,x);
fun mk_add (a,b) = list_mk_comb (``$+``,[a,b]);
val zero = ``0:num``;
fun mk_sucn n = funpow n mk_suc zero;
fun mk_mult (a,b) = list_mk_comb (``$*``,[a,b]);

fun dest_suc x =
  let val (a,b) = dest_comb x in
    if not (term_eq (a,``SUC``)) then raise ERR "" "" else b
  end

fun dest_add tm =
  let val (oper,argl) = strip_comb tm in
    if not (term_eq (oper,``$+``)) then raise ERR "" "" else pair_of_list argl
  end

(* -------------------------------------------------------------------------
   Equality
   ------------------------------------------------------------------------- *)

fun sym x = mk_eq (swap (dest_eq x))

(* -------------------------------------------------------------------------
   Higher-order
   ------------------------------------------------------------------------- *)

fun LET_CONV_MIN tm =
  let val (rator,rand) = dest_comb tm in SYM (ISPECL [rator,rand] LET_THM) end

fun LET_CONV_AUX tm =
 (TRY_CONV (RATOR_CONV LET_CONV_AUX) THENC LET_CONV_MIN) tm

fun is_let f =
  let val {Name,Thy,Ty} = dest_thy_const f in
    Name = "LET" andalso Thy = "bool"
  end

fun LET_CONV tm =
  if not (is_comb tm) then NO_CONV tm else
    let val f = fst (strip_comb tm) in
      if is_let f then NO_CONV tm else LET_CONV_AUX tm
    end

fun LET_CONV_ALL tm = TOP_SWEEP_CONV LET_CONV tm

fun let_rw tm = rhs (concl (LET_CONV_ALL tm))


end (* struct *)

