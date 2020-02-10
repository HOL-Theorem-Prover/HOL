(* ========================================================================= *)
(* FILE          : mleCombinLib.sml                                          *)
(* DESCRIPTION   : Tools for term synthesis on combinators                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleCombinLib :> mleCombinLib =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory psTermGen

val ERR = mk_HOL_ERR "mleCombinLib"

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

fun all_pos tm =
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = map_snd (fn x => i :: x) (all_pos arg)
  in
    (tm,[]) :: List.concat (mapi f argl)
  end

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

(* variables *)

val cK = mk_var ("k",alpha)
val cS = mk_var ("s",alpha)
val cX = mk_var ("x",alpha)
val cA = mk_var ("a",``:'a -> 'a -> 'a``)
val cT = mk_var ("t",``:'a -> 'a``)
val cV = mk_var ("v",``:'a -> bool``)
val cL = mk_var ("l",``:'a -> bool``)

val vx = mk_var ("X",alpha)
val vy = mk_var ("Y",alpha)
val vz = mk_var ("Z",alpha)
val vu = mk_var ("U",alpha)
val vv = mk_var ("V",alpha)
val vw = mk_var ("W",alpha)
val v1 = mk_var ("V1",alpha)
val v2 = mk_var ("V2",alpha)
val v3 = mk_var ("V3",alpha)

(* constructors *)
fun mk_cV a = mk_comb (cV,a)
fun mk_cL a = mk_comb (cL,a)

val cEV = mk_var ("ev",``:'a -> 'a -> bool``)
val cRW = mk_var ("rw",``:'a -> 'a -> bool``)
fun mk_cRW (a,b) = list_mk_comb (cRW,[a,b])
fun mk_cEV (a,b) = list_mk_comb (cEV,[a,b])

fun mk_tag x = mk_comb (cT,x)
fun dest_tag tm = 
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cT then () else raise ERR "dest_tag" ""
  in
    singleton_of_list argl
  end

fun tag_pos (tm,pos) =
  if null pos then mk_tag tm else
  let
    val (oper,argl) = strip_comb tm
    fun f i x = if i = hd pos then tag_pos (x,tl pos) else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

infix oo
fun op oo (a,b) = list_mk_comb (cA,[a,b])
fun mk_cA (a,b) = list_mk_comb (cA,[a,b])
fun dest_cA tm = 
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cA then () else raise ERR "dest_cA" ""
  in
    pair_of_list argl
  end

fun list_mk_cA tml = case tml of
    [] => raise ERR "list_mk_cA" ""
  | [tm] => tm
  | a :: b :: m => list_mk_cA (mk_cA (a,b) :: m)
fun strip_cA_aux tm =
  if is_var tm then [tm] else
  let val (oper,argl) = strip_comb tm in
    if term_eq oper cA then 
      let val (a1,a2) = pair_of_list argl in a2 :: strip_cA_aux a1 end 
    else [tm]
  end

fun strip_cA tm = rev (strip_cA_aux tm)

(* theorems *)
fun forall_capital tm =
  let 
    fun test v = (Char.isUpper o hd_string o fst o dest_var) v
    val vl = filter test (free_vars_lr tm)
  in
    list_mk_forall (vl,tm)
  end

val s_thm_bare = mk_eq (cS oo vx oo vy oo vz, (vx oo vz) oo (vy oo vz))
val k_thm_bare = mk_eq (cK oo vx oo vy, vx)

val eq_axl_bare = [s_thm_bare,k_thm_bare]
val eq_axl = map forall_capital eq_axl_bare

fun tag_lhs eq = let val (a,b) = dest_eq eq in mk_eq (mk_tag a, b) end
val left_thm = mk_eq (mk_tag (vx oo vy), mk_tag vx oo vy)
val right_thm = mk_eq (mk_tag (vx oo vy), vx oo mk_tag vy)
val tag_axl_bare = map tag_lhs eq_axl_bare @ [left_thm,right_thm]

fun cterm_size tm = 
  let val (oper,argl) = strip_comb tm in
    (if tmem oper [cA,cT] then 0 else 1) + sum_int (map cterm_size argl)
  end

(* big step semantics *)
val ev_ax1 = mk_cV cK
val ev_ax2 = mk_imp (mk_cV vv, mk_cV (mk_cA (cK,vv)))
val ev_ax3 = mk_cV cS
val ev_ax4 = mk_imp (mk_cV vv, mk_cV (mk_cA (cS,vv)))
val ev_ax5 = mk_imp (mk_cV vv, mk_cV (list_mk_cA [cS,vu,vv]))
val ev_ax6 = mk_imp (mk_cL vv,mk_cV vv)
val ev_ax7 = list_mk_imp ([mk_cL vu, mk_cV vv],mk_cL(mk_cA(vu,vv)))
val ev_ax8 = mk_imp (mk_cV vv, mk_cEV (vv,vv))
val ev_ax9 = mk_imp (mk_cEV (vx,vv), mk_cEV (list_mk_cA [cK,vx,vy],vv))
val ev_ax10 = mk_imp (mk_cEV ((vx oo vz) oo (vy oo vz),vv), 
  mk_cEV (list_mk_cA [cS,vx,vy,vz],vv))
val ev_ax11 = mk_imp (mk_cEV (vx,vv), mk_cEV (cK oo vx, cK oo vv));
val ev_ax12 = mk_imp (mk_cEV (vx,vv), mk_cEV (cS oo vx, cS oo vv));
val ev_ax13 = 
  list_mk_imp ([mk_cEV (vx,vu),mk_cEV (vy,vv)], 
    mk_cEV (cS oo vx oo vy, cS oo vu oo vv));
val ev_ax14 = 
  list_mk_imp ([mk_cEV (vx,vu),mk_cEV (vy,vv),mk_cEV (vu oo vv,vw)], 
    mk_cEV (vx oo vy,vw));
val ev_axl = 
  map forall_capital
    [ev_ax1,ev_ax2,ev_ax3,ev_ax4,ev_ax5,ev_ax6,ev_ax7,ev_ax8,
     ev_ax9,ev_ax10,ev_ax11,ev_ax12,ev_ax13,ev_ax14]

(* small step semantics *)
val rw_ax1 = mk_cRW (vx,vx)
val rw_ax2 = 
  list_mk_imp ([mk_cRW (vu,vv), mk_cRW (vx,vy)], mk_cRW (vu oo vx, vv oo vy));
val rw_ax3 = mk_cRW (list_mk_cA [cS,vx,vy,vz], (vx oo vz) oo (vy oo vz));
val rw_ax4 = mk_cRW (list_mk_cA [cK,vx,vy], vx);
val rw_ax5 = list_mk_imp ([mk_cRW (vx,vy), mk_cRW(vy,vz)], mk_cRW(vx,vz));
val rw_axl = map forall_capital [rw_ax1,rw_ax2,rw_ax3,rw_ax4,rw_ax5]

(* -------------------------------------------------------------------------
   Printing combinators
   ------------------------------------------------------------------------- *)

fun cts tm = 
  if is_var tm then fst (dest_var tm) else
  let val tml = strip_cA tm in
    "(" ^ String.concatWith " " (map cts tml) ^ ")"
  end

(* -------------------------------------------------------------------------
   Rewriting combinators
   ------------------------------------------------------------------------- *)

fun is_capital_var tm = is_var tm andalso 
  Char.isUpper (hd_string (fst (dest_var tm)))

fun is_match eq tm = 
  let val (sub,_) = match_term (lhs eq) tm in
    all is_capital_var (map #redex sub)
  end
  handle HOL_ERR _ => false

fun exists_match eq tm = can (find_term (is_match eq)) tm

fun subst_match eq tm =
  let 
    val subtm = find_term (is_match eq) tm
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun subst_match_first eql tm =
  let 
    val subtm = find_term (fn x => exists (fn eq => is_match eq x) eql) tm
    val eq = valOf (List.find (fn x => is_match x subtm) eql)
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun lo_cnorm n eql tm =
  if not (exists (C exists_match tm) eql) then SOME tm
  else if n <= 0 then NONE else
    let val tm' = subst_match_first eql tm in
      lo_cnorm (n-1) eql tm'
    end

exception Break

fun fast_lo_cnorm n eql maintm =
  let
    val i = ref 0    
    fun fast_lo_cnorm_aux n eql tm = 
      let val eqo = List.find (fn x => is_match x tm) eql in
        case eqo of
          SOME eq => 
          let 
            val sub1 = fst (match_term (lhs eq) tm)
            val newtm = subst sub1 (rhs eq)
            val _ = incr i
            val _ = if !i > n then raise Break else () 
          in
            fast_lo_cnorm_aux n eql newtm
          end   
        | NONE => 
          let val (oper,argl) = strip_comb tm in
            list_mk_comb (oper, map (fast_lo_cnorm_aux n eql) argl)
          end  
      end
    fun loop tm =
      if not (exists (C exists_match tm) eql)
      then SOME tm
      else loop (fast_lo_cnorm_aux n eql tm)
  in
    loop maintm handle Break => NONE
  end

fun is_nf tm = 
  not (exists (C exists_match tm) eq_axl_bare)
fun contain_red tm =
  can (find_term (fn x => exists (C is_match x) eq_axl_bare)) tm

(* -------------------------------------------------------------------------
   Generating combinators
   ------------------------------------------------------------------------- *)

val s2 = mk_var ("s2", ``:'a -> 'a -> 'a``)
val s1 = mk_var ("s1", ``:'a -> 'a``)
val s0 = mk_var ("s0", alpha)
val k1 = mk_var ("k1", ``:'a -> 'a``)
val k0 = mk_var ("k0", alpha)

fun to_apply tm = case strip_comb tm of
    (oper,[c1,c2]) => (
    if term_eq oper s2 then list_mk_cA [cS, to_apply c1, to_apply c2]
    else raise ERR "to_apply" "")
  | (oper,[c1]) => (
    if term_eq oper s1 then mk_cA (cS, to_apply c1)
    else if term_eq oper k1 then mk_cA (cK, to_apply c1)
    else raise ERR "to_apply" "")
  | (oper,_) => (
    if term_eq oper s0 then cS
    else if term_eq oper k0 then cK
    else raise ERR "to_apply" "")

fun random_nf size = 
  to_apply (random_term [s2,s1,s0,k1,k0] (size,alpha))

fun gen_nf_exhaustive size = 
  map to_apply (gen_term [s2,s1,s0,k1,k0] (size,alpha))

(*
load "aiLib"; open aiLib;
load "mleCombinLib"; open mleCombinLib;
load "psTermGen"; open psTermGen;
val tml = gen_nf_exhaustive 10; length tml;
val n = sum_real (List.tabulate (10,fn i => nterm [s2,s1,s0,k1,k0] (i,alpha)));
*)

end (* struct *)

