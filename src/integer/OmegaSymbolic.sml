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

infix THENC THEN THENL ORELSEC |->
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
val qvar = mk_var("q", bool)
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
    expand_evals tm

    tm is of form p /\ (evalupper x list1 /\ evallower x list2)
    rewrite away the evallower and evalupper terms, keeping everything
    right associated
   ---------------------------------------------------------------------- *)

val (evalhi10, evalhi_cons0) = munge_to_altform "cs" evalupper_def
val (evallo1, evallo_cons) = munge_to_altform "cs" evallower_def

val evalhi1 = AP_THM (AP_TERM conjunction evalhi10) qvar
val evalhi_cons =
    CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM CONJ_ASSOC))))
              (AP_TERM (mk_comb(conjunction, pvar))
                       (AP_THM (AP_TERM conjunction evalhi_cons0) qvar))


val expand_evals = let
  fun reclos tm =
      (REWR_CONV evallo1 ORELSEC
       (REWR_CONV evallo_cons THENC RAND_CONV reclos)) tm
  fun rechis tm =
      ((RAND_CONV (REWR_CONV evalhi1 THENC RAND_CONV reclos)) ORELSEC
       (REWR_CONV evalhi_cons THENC RAND_CONV rechis)) tm
in
  rechis
end


(* ----------------------------------------------------------------------
    calculate_range_disjunct c tm

    tm is of form ?i. (0 <= i /\ i <= u) /\ ...
    transform this into an appropriate number of disjuncts (or possibly
    false, if u < 0), of the form
       P(0) \/ P(1) \/ ... \/ P(u)
    and apply conversion c to each disjunct
   ---------------------------------------------------------------------- *)

val refl_case = prove(
  ``!u P. (?i:int. (u <= i /\ i <= u) /\ P i) = P u``,
  REWRITE_TAC [INT_LE_ANTISYM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `u` THEN
  ASM_REWRITE_TAC []);
val nonrefl_case = prove(
  ``!lo hi P. (?i:int. (lo <= i /\ i <= hi) /\ P i) =
              lo <= hi /\ (P lo \/ ?i. (lo + 1 <= i /\ i <= hi) /\ P i)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.ASM_CASES_TAC `i = lo` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [LEFT_AND_OVER_OR] THEN
      DISJ2_TAC THEN CONJ_TAC THENL [
        IMP_RES_TAC INT_LE_TRANS,
        ALL_TAC
      ] THEN Q.EXISTS_TAC `i` THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [GSYM int_arithTheory.less_to_leq_samer] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_LE_LT]) THEN
      POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (fn th => MP_TAC th THEN REWRITE_TAC [] THEN NO_TAC)
    ],
    Q.EXISTS_TAC `lo` THEN ASM_REWRITE_TAC [INT_LE_REFL],
    Q.EXISTS_TAC `i` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN Q.EXISTS_TAC `lo + 1` THEN
    ASM_REWRITE_TAC [INT_LE_ADDR] THEN CONV_TAC CooperMath.REDUCE_CONV
  ]);


fun calculate_range_disjunct c tm = let
  val (i, body) = dest_exists tm
  fun recurse tm =
      ((REWR_CONV refl_case THENC BETA_CONV THENC c) ORELSEC
       (REWR_CONV nonrefl_case THENC
        LAND_CONV CooperMath.REDUCE_CONV THENC
        (REWR_CONV CooperThms.F_and_l ORELSEC
         (REWR_CONV CooperThms.T_and_l THENC
          FORK_CONV(BETA_CONV THENC c,
                    BINDER_CONV (LAND_CONV
                                   (LAND_CONV CooperMath.REDUCE_CONV)) THENC
                    recurse))))) tm
in
  BINDER_CONV (RAND_CONV (CooperSyntax.mk_abs_CONV i)) THENC recurse
end tm

(* ----------------------------------------------------------------------
    calculate_nightmare t

    t is a term of the form nightmare m ups lows tlist.
    This function expands it into an equation of the form
       |- t = (?x. ...) \/ (?x. ...) \/ ... \/ (?x. ...)

   ---------------------------------------------------------------------- *)

val (cnightmare10, cnightmare_cons0) = munge_to_altform "rs" calc_nightmare_def

val reassoc_internals = LEFT_AND_EXISTS_CONV THENC
                        BINDER_CONV (REWR_CONV (GSYM CONJ_ASSOC))
val cnightmare1 = CONV_RULE (RAND_CONV reassoc_internals)
                            (AP_THM (AP_TERM conjunction cnightmare10) pvar)

val cnightmare_cons =
    CONV_RULE (RAND_CONV (REWR_CONV RIGHT_AND_OVER_OR THENC
                          LAND_CONV reassoc_internals))
              (AP_THM (AP_TERM conjunction cnightmare_cons0) pvar)

val calculate_nightmare = let
  val reducer =
      BINDER_CONV (LAND_CONV (RAND_CONV
                                (RAND_CONV CooperMath.REDUCE_CONV))) THENC
      calculate_range_disjunct ALL_CONV (* should be a conversion to do
                                           divides elimination *)
  fun recurse t =
      ((REWR_CONV cnightmare1 THENC reducer) ORELSEC
       (REWR_CONV cnightmare_cons THENC LAND_CONV reducer THENC
        RAND_CONV recurse)) t
in
  REWR_CONV calculational_nightmare THENC
  expand_evals THENC
  recurse
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
        val th = MP (MATCH_MP exact_shadow_case (CONJ ups_nzero lows_nzero))
                    disj
      in
        K th THENC calculate_shadow (alt_rshadow, alt_rrow)
      end
    | EXACT_UP => let
        val up_fst1 = prove_every_fst1 ups
        val disj = DISJ1 up_fst1 (list_mk_comb(every_t, [fst1_t, lows]))
        val th = MP (MATCH_MP exact_shadow_case (CONJ ups_nzero lows_nzero))
                    disj
      in
        K th THENC calculate_shadow (alt_rshadow, alt_rrow)
      end
    | NIGHTMARE m => let
        val uppers_lt_m = prove_every_fst_lt_m m ups
      in
        K (MATCH_MP alternative_equivalence
                    (LIST_CONJ [ups_nzero, lows_nzero, uppers_lt_m])) THENC
        RAND_CONV (RAND_CONV (ALPHA_CONV v)) THENC
        LAND_CONV (calculate_shadow (alt_dshadow, alt_drow)) THENC
        RAND_CONV (BINDER_CONV calculate_nightmare THENC
                   CooperSyntax.push_one_exists_over_many_disjs)
      end
  end t
  fun elim_rT tm = (if rand tm = boolSyntax.T then REWR_CONV CooperThms.T_and_r
                    else ALL_CONV) tm
in
  initially THENC LAND_CONV finisher THENC elim_rT
end


(* ----------------------------------------------------------------------
    best_variable_to_eliminate vs t

    Given a list of variables vs, and a conjunction of leaves t, pick the
    variable that should be eliminated.  Do this by scanning the term
    while maintaining a map to information about that variable.
   ---------------------------------------------------------------------- *)

type varinfo = { maxupc : Arbint.int ref, maxloc : Arbint.int ref,
                 numups : int ref, numlos : int ref }
fun new_varinfo () : varinfo =
    { maxupc = ref Arbint.zero, maxloc = ref Arbint.zero,
      numups = ref 0, numlos = ref 0}
exception NotFound

fun variable_information vs t = let
  val table = Polyhash.mkPolyTable(10, NotFound)
  fun ins_initial_recs v = Polyhash.insert table (v, new_varinfo())
  val _ = app ins_initial_recs vs
  fun examine_cv t = let
    val (c, v) = dest_mult t
    val c_i = int_of_term c
  in
    case Polyhash.peek table v of
      NONE => ()
    | SOME {maxupc, maxloc, numups, numlos} =>
      if Arbint.<(c_i, Arbint.zero) then (* upper bound *)
        (maxupc := Arbint.max(!maxupc, Arbint.~ c_i);
         numups := !numups + 1)
      else
        (maxloc := Arbint.max(!maxloc, c_i);
         numlos := !numlos + 1)
  end handle HOL_ERR _ => ()
in
  app examine_cv (List.concat (map (strip_plus o rand) (strip_conj t)));
  table
end

fun findleast gt f l =
    case l of
      [] => raise Fail "findleast : empty list"
    | h::t => let
        fun recurse (acc as (e, v)) l =
            case l of
              [] => (e, v)
            | h::t => let val v' = f h
                      in
                        if gt(v, v') then recurse (h, v') t
                        else recurse acc t
                      end
      in
        recurse (h, f h) t
      end

fun best_variable_to_eliminate vs t = let
  val table = variable_information vs t
  val items = Polyhash.listItems table
  fun is_vacuous (_, {numups, numlos,...}) = !numups = 0 orelse !numlos = 0
  fun is_exact (_, {maxloc, maxupc,...}) = !maxloc = Arbint.one orelse
                                           !maxupc = Arbint.one
in
  case List.find is_vacuous items of
    NONE => let
      val exacts = filter is_exact items
    in
      if null exacts then let
          fun f (_, {maxloc, maxupc, ...}) = Arbint.max(!maxloc, !maxupc)
          val ((v, {maxupc, ...}), _) = findleast Arbint.> f items
        in
          (v, NIGHTMARE (rand (term_of_int (!maxupc))))
        end
      else let
          fun f (_, {numups, numlos,...}) = !numups * !numlos
          val ((v, {maxupc, maxloc,...}), _) = findleast op> f exacts
        in
          (v, if !maxupc = Arbint.one then EXACT_UP else EXACT_LOW)
        end
    end
  | SOME (v, {numups, numlos,...}) => (v, if !numlos = 0 then VACUOUS_UP
                                          else VACUOUS_LOW)
end

(* ----------------------------------------------------------------------
    eliminate_an_existential t

    t is of the form ?x1..xn. body, where body is a conjunction of
    fully normalised leaves.  This function picks one of the quantifiers
    to eliminate, and then does this.
   ---------------------------------------------------------------------- *)

fun push_nthvar_to_bot n tm =
    if n <= 0 then TRY_CONV (SWAP_VARS_CONV THENC
                             BINDER_CONV (push_nthvar_to_bot 0)) tm
    else BINDER_CONV (push_nthvar_to_bot (n - 1)) tm

fun eliminate_an_existential t = let
  val (vs, body) = strip_exists t
  val (eliminate, category) = best_variable_to_eliminate vs body
  val v_n = index (fn v => v = eliminate) vs
in
  push_nthvar_to_bot v_n THENC
  LAST_EXISTS_CONV (apply_fmve category)
end t


end (* struct *)
