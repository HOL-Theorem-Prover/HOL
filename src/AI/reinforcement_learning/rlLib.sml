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

val ERR = mk_HOL_ERR "rlLib"

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

fun all_pos tm = 
  let 
    val (oper,argl) = strip_comb tm 
    fun f i arg = map (fn x => i :: x) (all_pos arg)
  in
    [] :: List.concat (mapi f argl) 
  end


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
    if not (term_eq  a ``SUC``) then raise ERR "" "" else b
  end

fun dest_add tm =
  let val (oper,argl) = strip_comb tm in
    if not (term_eq oper ``$+``) then raise ERR "" "" else pair_of_list argl
  end

fun is_suc_only tm = 
  if term_eq tm zero then true else
  (is_suc_only (dest_suc tm)  handle HOL_ERR _ => false)

val ax1 = ``x + 0 = x``;
val ax2 = ``x + SUC y = SUC (x + y)``
val ax3 = ``x * 0 = 0``;
val ax4 = ``x * SUC y = x * y + x``;

(* -------------------------------------------------------------------------
   Equality
   ------------------------------------------------------------------------- *)

fun sym x = mk_eq (swap (dest_eq x))

fun unify a b = Unify.simp_unify_terms [] a b

fun paramod_ground eq (tm,pos) =
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
  handle _ => NONE

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

