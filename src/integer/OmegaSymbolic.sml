structure OmegaSymbolic =
struct

(* This file implements the horrid part of the Omega test, when you have to
   do quantifier elimination symbolically, and without the benefit of being
   able to work outside the logic.

   In particular, this means that this part of the procedure has to work
   using the theorems in OmegaTheory.

   Input is a term of the form
       ?x. r1 /\ r2 /\ .. rn
   where each rn is in "Omega leaf normal form", i.e.
       0 <= c1 * v1 + c2 * v2 + c3 * v3 + c
*)

open HolKernel boolLib intSyntax QConv

open integerTheory OmegaTheory

infix THENC THEN ORELSEC |->
infixr --> ##

val lhand = rand o rator

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV
val TRY_CONV = TRY_QCONV

fun EVERY_CONJ_CONV c t =
    if is_conj t then BINOP_CONV (EVERY_CONJ_CONV c) t
    else c t

fun ERR f msg = HOL_ERR { origin_structure = "OmegaSymbolic",
                          origin_function = f,
                          message = msg}

(* ----------------------------------------------------------------------
    clause_to_evals v t

    where v is a variable, and t is a conjunction of <= leaves.
    Returns a theorem of the form
       t = (evalleft v lefts /\ evalright v rights) /\ extras
    where v is not free in extras.  Extras may be the term T.

   ---------------------------------------------------------------------- *)

val pvar = mk_var("p", bool)
val xvar = mk_var("x", int_ty)
fun clause_to_evals v tm = let
  val step0 = REWRITE_CONV [GSYM CONJ_ASSOC]
  fun step1 tm = INST [pvar |-> tm, xvar |-> v] eval_base
  fun mk_upper cf t = let
    (* cf will be the negative coefficient of v *)
    val poscf_t = mk_mult(term_of_int (Arbint.~ cf), v)
  in
    K (SYM (SPECL [poscf_t, zero_tm, rand t] INT_LE_LADD)) THENC
    FORK_CONV (REWR_CONV INT_ADD_RID, REWR_CONV INT_ADD_COMM) THENC
    RAND_CONV OmegaMath.SORT_AND_GATHER1_CONV
  end t
  fun mk_lower cf t = let
    (* cf will be the positive coefficient of v *)
    val neg_t = mk_negated(mk_mult(term_of_int cf, v))
  in
    K (SYM (SPECL [neg_t, zero_tm, rand t] INT_LE_LADD)) THENC
    FORK_CONV (REWR_CONV INT_ADD_RID, REWR_CONV INT_ADD_COMM) THENC
    RAND_CONV (RAND_CONV (REWR_CONV INT_NEG_LMUL) THENC
               OmegaMath.SORT_AND_GATHER1_CONV THENC
               REWR_CONV (GSYM INT_NEGNEG)) THENC
    REWR_CONV INT_LE_NEG
  end t

  fun normal_step tm = let
    val (c1, c2) = dest_conj tm
    val (evals, ex) = dest_conj c1
    val (ups, lows) = dest_conj evals
    val (ex1, ex2, up, low, cval, get_t) =
        if is_conj c2 then
          (eval_step_extra3, eval_step_extra4, eval_step_upper2,
           eval_step_lower2, RAND_CONV o LAND_CONV, #1 o dest_conj)
        else
          (eval_step_extra1, eval_step_extra2, eval_step_upper1,
           eval_step_lower1, RAND_CONV, I)
    val t = get_t c2
    val cf = CooperMath.sum_var_coeffs v (rand t)
  in
    if cf = Arbint.zero then
      if is_const ex then REWR_CONV ex1
      else REWR_CONV ex2
    else if Arbint.<(cf, Arbint.zero) then
      cval (mk_upper cf) THENC REWR_CONV up
    else
      cval (mk_lower cf) THENC REWR_CONV low
  end tm
in
  step0 THENC step1 THENC REPEATC normal_step
end tm

(* ----------------------------------------------------------------------
    prove_every_fstnzero t

    t is a term of the form ``[ (num, int); (num, int); ... (num, int)]``
    This function attempts to prove |- EVERY fst_nzero ^t
   ---------------------------------------------------------------------- *)

val c_ty = pairSyntax.mk_prod(numSyntax.num, int_ty)
val clist_ty = listSyntax.mk_list_type c_ty
val nil_t = listSyntax.mk_nil c_ty
val every_t = mk_thy_const {Thy = "list", Name = "EVERY",
                            Ty = (c_ty --> bool) --> clist_ty --> bool};
val (every_nil, every_cons) = CONJ_PAIR listTheory.EVERY_DEF

val fst_nzero_t = mk_thy_const {Thy = "Omega", Name = "fst_nzero",
                                Ty = c_ty --> bool};
val every_fst_nzero_nil = EQT_ELIM (ISPEC fst_nzero_t every_nil)
val every_fst_nzero_cons = ISPEC fst_nzero_t every_cons
fun prove_fstnzero t =
    EQT_ELIM ((REWR_CONV fst_nzero_def THENC
               RAND_CONV (REWR_CONV pairTheory.FST) THENC
               CooperMath.REDUCE_CONV) (mk_comb(fst_nzero_t, t)))

fun prove_every_fstnzero list_t =
    case total listSyntax.dest_cons list_t of
      NONE => every_fst_nzero_nil
    | SOME (h,t) => let
        val fnz_th = prove_fstnzero h
        val rest = prove_every_fstnzero t
      in
        EQ_MP (SYM (SPECL [h, t] every_fst_nzero_cons))
              (CONJ fnz_th rest)
      end

(* ----------------------------------------------------------------------
    prove_every_fst1 t

    t is a term of the form ``[ (num, int); (num, int); ... (num, int)]``
    This function attempts to prove |- EVERY fst1 ^t
   ---------------------------------------------------------------------- *)

val fst1_t = ``Omega$fst1 : num # int -> bool``
val every_fst1_nil = EQT_ELIM (ISPEC fst1_t every_nil)
val every_fst1_cons = ISPEC fst1_t every_cons
fun prove_fst1 t =
    EQT_ELIM ((REWR_CONV fst1_def THENC
               LAND_CONV (REWR_CONV pairTheory.FST) THENC
               CooperMath.REDUCE_CONV) (mk_comb(fst1_t, t)))

fun prove_every_fst1 list_t =
    case total listSyntax.dest_cons list_t of
      NONE => every_fst1_nil
    | SOME(h,t) => let
        val h_th = prove_fst1 h
        val t_th = prove_every_fst1 t
      in
        EQ_MP (SYM (SPECL [h,t] every_fst1_cons)) (CONJ h_th t_th)
      end

(* ----------------------------------------------------------------------
    prove_every_fst_lt_m m t

    t is a term of the form ``[ (num, int); (num, int); ... (num, int)]``
    m is a term of type :num, and a numeral.
    This function attempts to prove |- EVERY (\p. FST p <= ^m) ^t
   ---------------------------------------------------------------------- *)

fun abs_t m = let
  val p = mk_var("p", c_ty)
  val body = numSyntax.mk_leq(pairSyntax.mk_fst p, m)
in
  mk_abs(p, body)
end

fun prove_fst_lt_m abs_t t =
    EQT_ELIM ((BETA_CONV THENC LAND_CONV (REWR_CONV pairTheory.FST) THENC
               CooperMath.REDUCE_CONV) (mk_comb(abs_t, t)))

fun prove_every_fst_lt_m m t = let
  val absn = abs_t m
  fun recurse list_t =
      case total listSyntax.dest_cons list_t of
        NONE => EQT_ELIM (ISPEC absn every_nil)
      | SOME(h,t) =>
        EQ_MP (SYM (ISPECL [absn, h, t] every_cons))
              (CONJ (prove_fst_lt_m absn h) (recurse t))
in
  recurse t
end



(* ----------------------------------------------------------------------
    apply_fmve cty t

    t is of the form ?x. c1 /\ c2 /\ c3 .. /\ cn

    Every ci is a valid Omega leaf.  This function converts the body
    into a term involving eval_left and eval_right and an "extra" bit,
    pushes the existential in over the former pair, and then uses an
    appropriate rewrite from OmegaTheory.  The right choice of rewrite
    is specified through the parameter cty.
   ---------------------------------------------------------------------- *)

datatype ctype = VACUOUS_LOW | VACUOUS_UP | EXACT_LOW | EXACT_UP
               | NIGHTMARE of term
(* the nightmare constructor takes a term of type ``:num`` corresponding to
   the maximum coefficient of the variable to be eliminated in an upper
   bound constraint *)

fun apply_fmve ctype = let
  fun initially t = let
    val (v, body) = dest_exists t
  in
    BINDER_CONV (clause_to_evals v) THENC EXISTS_AND_CONV
  end t

  fun finisher t = let
    val (v,body) = dest_exists t
    val (e_ups, e_lows) = dest_conj body
    val ups = rand e_ups
    val lows = rand e_lows
    val ups_nzero = prove_every_fstnzero ups
    val lows_nzero = prove_every_fstnzero lows
  in
    case ctype of
      VACUOUS_LOW => REWRITE_CONV [evalupper_def] THENC
                     K (EQT_INTRO (MATCH_MP onlylowers_satisfiable lows_nzero))
    | VACUOUS_UP =>  REWRITE_CONV [evallower_def] THENC
                     K (EQT_INTRO (MATCH_MP onlyuppers_satisfiable ups_nzero))
    | EXACT_LOW => let
        val low_fst1 = prove_every_fst1 lows
        val disj = DISJ2 (list_mk_comb(every_t, [fst1_t, ups])) low_fst1
      in
        K (MP (MATCH_MP exact_shadow_case (CONJ ups_nzero lows_nzero)) disj)
      end
    | EXACT_UP => let
        val up_fst1 = prove_every_fst1 ups
        val disj = DISJ1 up_fst1 (list_mk_comb(every_t, [fst1_t, lows]))
      in
        K (MP (MATCH_MP exact_shadow_case (CONJ ups_nzero lows_nzero)) disj)
      end
    | NIGHTMARE m => let
        val uppers_lt_m = prove_every_fst_lt_m m ups
      in
        K (MATCH_MP alternative_equivalence
                    (LIST_CONJ [ups_nzero, lows_nzero, uppers_lt_m])) THENC
        RAND_CONV (RAND_CONV (ALPHA_CONV v))
      end
  end t
in
  initially THENC LAND_CONV finisher
end

(* ----------------------------------------------------------------------
    calculate_shadow (sdef, rowdef) t

    sdef is a the "shadow definition", i.e. a couple of theorems
    defining the shadow type (the conjuncts of real_shadow_def or
    dark_shadow_def) and rowdef is the analogous pair of theorems
    defining the corresponding row function (conjuncts of
    rshadow_row_def or dark_shadow_row_def)
   ---------------------------------------------------------------------- *)


fun munge_to_altform varname th = let
  val (nilth, consth0) = CONJ_PAIR th
  val consth = SPEC_ALL consth0
in
  (REWRITE_RULE [nilth] (INST [mk_var(varname, clist_ty) |-> nil_t] consth),
   consth)
end

val alt_dshadow = munge_to_altform "uppers" dark_shadow_def
val alt_drow = munge_to_altform "rs" dark_shadow_row_def
val alt_rshadow = munge_to_altform "ls" real_shadow_def
val alt_rrow = munge_to_altform "rs" rshadow_row_def

fun calculate_shadow (sdef, rowdef) = let
  val (s1, scons) = sdef
  val (r1, rcons) = rowdef
  val mathnorm = OmegaMath.leaf_normalise THENC OmegaMath.gcd_check
  fun calculate_row t =
      ((REWR_CONV r1 THENC mathnorm) ORELSEC
       (REWR_CONV rcons THENC FORK_CONV (mathnorm, calculate_row))) t
  fun main t =
      ((REWR_CONV s1 THENC calculate_row) ORELSEC
       (REWR_CONV scons THENC FORK_CONV (calculate_row, main))) t
in
  main
end

(* ----------------------------------------------------------------------
    calculate_nightmare t

    t is a term of the form nightmare m ups lows tlist.
    This function expands it into an equation of the form
       |- t = (?x. ...) \/ (?x. ...) \/ ... \/ (?x. ...)

   ---------------------------------------------------------------------- *)

val (nightmare1, nightmare_cons) = munge_to_altform "rs" nightmare_def

val calculate_nightmare = let
  val reducer =
      STRIP_QUANT_CONV (LAND_CONV (RAND_CONV
                                     (RAND_CONV CooperMath.REDUCE_CONV)))
  fun recurse t =
      ((REWR_CONV nightmare1 THENC reducer) ORELSEC
       (REWR_CONV nightmare_cons THENC LAND_CONV reducer THENC
        RAND_CONV recurse)) t
in
  recurse
end


end (* struct *)
