structure selectUtil :> selectUtil = 
struct

open HolKernel boolLib Parse;

infix THEN THENC |->;

val ERR = mk_HOL_ERR "Support";

fun ANTI_BETA_CONV vars tm =
 let
   val tm' = list_mk_comb (list_mk_abs (vars, tm), vars)
   val c = funpow (length vars) (fn c => RATOR_CONV c THENC BETA_CONV) ALL_CONV
 in
    SYM (c tm')
 end;

fun AVOID_SPEC_TAC (tm, v) =
  W (fn (_, g) => SPEC_TAC (tm, variant (free_vars g) v));

(* ------------------------------------------------------------------------- *)
(* Eliminating Hilbert's epsilon operator.                                   *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*   ((?n. f n = 0) ==> (f n = 0)) ==> 3 < n                                 *)
(*   ---------------------------------------  SELECT_TAC                     *)
(*               3 < @n. f n = 0                                             *)
(* ------------------------------------------------------------------------- *)

local
  fun get vs tm =
    case 
      (case dest_term tm of COMB (x,y) =>
         (case get vs x of s as SOME _ => s | NONE => get vs y)
       | LAMB (v, b) => get (v :: vs) b
       | _ => NONE) of s as SOME _ => s
       | NONE =>
         if is_select (snd (strip_abs tm)) andalso
           null (intersect (free_vars tm) vs) then SOME tm
         else NONE;
in
  val get_vselect = partial (ERR "get_vselect" "not found") (get []);
end;

local
  fun select_norm vars =
    W
    (SUB_CONV o select_norm o (fn LAMB (v,_) => v :: vars | _ => vars) o
     dest_term) THENC
    W
    (fn tm =>
     if is_select tm then ANTI_BETA_CONV (intersect (free_vars tm) vars)
     else ALL_CONV);
in
  val SELECT_NORM_CONV = select_norm [];
end;

local
  val rewr = RATOR_CONV (REWR_CONV boolTheory.EXISTS_DEF)
  fun conv vars =
    rewr THENC BETA_CONV THENC RAND_CONV (ANTI_BETA_CONV vars) THENC BETA_CONV
in
  fun MK_VSELECT_THM vsel =
    let
      val (vars, sel) = strip_abs vsel
      val (v, body) = dest_select sel
      val ex = mk_exists (v, body)
    in
      foldr (uncurry GEN) (DISCH ex (EQ_MP (conv vars ex) (ASSUME ex))) vars
    end;
end;

fun SPEC_VSELECT_TAC vsel =
  let
    val (v, _) = dest_var (fst (dest_select (snd (strip_abs vsel))))
  in
    MP_TAC (MK_VSELECT_THM vsel) THEN
    AVOID_SPEC_TAC (vsel, mk_var (v, type_of vsel)) THEN
    GEN_TAC
  end;

val SPEC_ONE_SELECT_TAC = W (fn (_, tm) => SPEC_VSELECT_TAC (get_vselect tm));

val SELECT_TAC = CONV_TAC SELECT_NORM_CONV THEN REPEAT SPEC_ONE_SELECT_TAC;

end
