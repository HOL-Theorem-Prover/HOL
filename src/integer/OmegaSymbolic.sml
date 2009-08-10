structure OmegaSymbolic :> OmegaSymbolic =
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

open HolKernel boolLib intSyntax

open integerTheory OmegaTheory

val lhand = rand o rator


val REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV bool_rewrites

fun EVERY_CONJ_CONV c t =
    if is_conj t then BINOP_CONV (EVERY_CONJ_CONV c) t
    else c t

fun EVERY_DISJ_CONV c t =
    if is_disj t then BINOP_CONV (EVERY_DISJ_CONV c) t
    else c t

fun ERR f msg = HOL_ERR { origin_structure = "OmegaSymbolic",
                          origin_function = f,
                          message = msg}

(* ----------------------------------------------------------------------
    clause_to_evals v t

    where v is a variable, and t is a conjunction of <= or divisibility
    leaves.
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
    val cf = if is_neg t orelse is_divides t then Arbint.zero
             else CooperMath.sum_var_coeffs v (rand t)
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
  val mathnorm = OmegaMath.leaf_normalise
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

    tm is of form evalupper x list1 /\ evallower x list2
    rewrite away the evallower and evalupper terms, keeping everything
    right associated
   ---------------------------------------------------------------------- *)

val (evalhi10, evalhi_cons0) = munge_to_altform "cs" evalupper_def
val (evallo1, evallo_cons) = munge_to_altform "cs" evallower_def

val evalhi1 = AP_THM (AP_TERM conjunction evalhi10) qvar
val evalhi_cons =
    CONV_RULE (RAND_CONV (REWR_CONV (GSYM CONJ_ASSOC)))
              (AP_THM (AP_TERM conjunction evalhi_cons0) qvar)


val expand_evals = let
  fun reclos tm =
      (REWR_CONV evallo1 ORELSEC
       (REWR_CONV evallo_cons THENC RAND_CONV reclos)) tm
  fun rechis tm =
      ((REWR_CONV evalhi1 THENC RAND_CONV reclos) ORELSEC
       (REWR_CONV evalhi_cons THENC RAND_CONV rechis)) tm
in
  rechis
end



(* ----------------------------------------------------------------------
    do_divisibility_analysis v ctxt tm

    tm is of the form   ?x. (c * x = e) /\ c1 /\ c2 /\ c3
    where each ci is either of the form  d * x <= U  or  L <= e * x.
    If e contains any variables that appear in ctxt, then
    leaf_normalise all of the ci's and the equality term and then rename
    x to be v (which is its correct name).

    Otherwise, multiply the ci's through so as to make them include
    c * x as a subterm, then rewrite with the first conjunct, and then
    leaf normalise.  The variable x will have been eliminated from all
    but the first conjunct.  Then push the ?x inwards, and turn that
    first conjunct into a divides term (c int_divides e).
   ---------------------------------------------------------------------- *)

fun lcmify v c c_i tm = let
  (* tm either d * v <= U or L <= e * v, need c * v to be present *)
  val (l,r) = dest_leq tm
  val (accessor, cval) =
      if rand r = v then (rand, RAND_CONV) else (lhand, LAND_CONV)
  val d = lhand (accessor tm)
in
  if  d = c then ALL_CONV
  else let
      open CooperMath
      val d_i = int_of_term d
      val lc = lcm(c_i, d_i)
      fun multiply_through tm =
          if lc <> d_i then let
              val f_i = Arbint.div(lc, d_i)
              val f = term_of_int f_i
              val zero_lt_f =
                  EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, f)))
              val finisher =
                  if f = c then
                    REWR_CONV INT_MUL_ASSOC THENC
                    LAND_CONV (REWR_CONV INT_MUL_COMM) THENC
                    REWR_CONV (GSYM INT_MUL_ASSOC)
                  else
                    REWR_CONV INT_MUL_ASSOC THENC LAND_CONV REDUCE_CONV
            in
              (K (SYM (MP (SPECL [f, l, r] INT_LE_MONO) zero_lt_f)) THENC
               cval finisher) tm
            end
          else ALL_CONV tm
      fun divide_out tm =
          if lc <> c_i andalso rand (accessor tm) = v then let
              val f_i = Arbint.div(lc, c_i)
              val f = term_of_int f_i
              val fc_eq_l = CooperMath.REDUCE_CONV(mk_mult(f, c))
            in
              (cval (LAND_CONV (K (SYM fc_eq_l)) THENC
                     REWR_CONV (GSYM INT_MUL_ASSOC))) tm
            end
          else ALL_CONV tm
    in
      multiply_through THENC divide_out
    end
end tm

fun do_divisibility_analysis v ctxt tm = let
  val (x, body) = dest_exists tm
  val (eqterm, rest) = dest_conj body
in
  if not (null (intersect (free_vars (rand eqterm)) ctxt)) then
    (* leave it as an equality *)
    BINDER_CONV (EVERY_CONJ_CONV OmegaMath.leaf_normalise) THENC
    RAND_CONV (ALPHA_CONV v)
  else let
      val c = lhand (lhand eqterm)
      val c_i = int_of_term c
      fun ctxt_rwt tm = let
        val (c1, c2) = dest_conj tm
        val thm0 = DISCH_ALL (REWRITE_CONV [ASSUME c1] c2)
      in
        MATCH_MP CooperThms.simple_conj_congruence thm0
      end
    in
      BINDER_CONV (RAND_CONV (EVERY_CONJ_CONV (lcmify x c c_i)) THENC
                   ctxt_rwt) THENC
      EXISTS_AND_CONV THENC
      LAND_CONV (BINDER_CONV (LAND_CONV (REWR_CONV INT_MUL_COMM)) THENC
                 REWR_CONV (GSYM INT_DIVIDES) THENC
                 RAND_CONV OmegaMath.sum_normalise THENC
                 CooperMath.minimise_divides) THENC
      RAND_CONV (EVERY_CONJ_CONV OmegaMath.leaf_normalise) THENC
      REWRITE_CONV []
    end
end tm




(* ----------------------------------------------------------------------
    calculate_nightmare ctxt t

    t is a term of the form ?x. nightmare x m ups lows tlist.
    This function expands it into an equation of the form
       |- t =  D1 \/ D2 \/ D3 \/ .. Dn
    Each Di is either free of x entirely (but with a divides term present
    as the first conjunct) or is of the form
       ?x. (c * x = R) /\ C1 /\ C2 /\ .. Cn
    where x is absent in all of the Ci, and where R includes at least
    one variable y, which is present in the list of variables ctxt.

    In this latter situation, the equality and one of the x or y will
    be eliminated through OmegaEq.  In the former situation, the divides
    term will need special treatment later.
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

fun calculate_nightmare ctxt tm = let
  val (v, body) = dest_exists tm
  val reducer =
      BINDER_CONV (LAND_CONV (RAND_CONV
                                (RAND_CONV CooperMath.REDUCE_CONV))) THENC
      OmegaMath.calculate_range_disjunct
  fun recurse t =
      ((REWR_CONV cnightmare1 THENC reducer) ORELSEC
       (REWR_CONV cnightmare_cons THENC LAND_CONV reducer THENC
        RAND_CONV recurse)) t
in
  BINDER_CONV (REWR_CONV calculational_nightmare THENC
               RAND_CONV expand_evals THENC
               recurse THENC REWRITE_CONV []) THENC
  CooperSyntax.push_in_exists THENC
  EVERY_DISJ_CONV (do_divisibility_analysis v ctxt) THENC
  REWRITE_CONV []
end tm


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
               | NIGHTMARE of (term * term list)
(* the nightmare constructor takes a pair as an argument:
     * the term is of type ``:num``, corresponding to
       the maximum coefficient of the variable to be eliminated in an
       upper bound constraint
     * the list of terms is a list of other existentially quantified
       variables that have scope over this clause  *)

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
    | NIGHTMARE (m,ctxt) => let
        val uppers_lt_m = prove_every_fst_lt_m m ups
      in
        K (MATCH_MP alternative_equivalence
                    (LIST_CONJ [ups_nzero, lows_nzero, uppers_lt_m])) THENC
        RAND_CONV (RAND_CONV (ALPHA_CONV v)) THENC
        LAND_CONV (calculate_shadow (alt_dshadow, alt_drow) THENC
                   REWRITE_CONV []) THENC
        RAND_CONV (calculate_nightmare ctxt)
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
  val table = ref (Redblackmap.mkDict Term.compare)
  fun ins_initial_recs v =
    table := Redblackmap.insert (!table, v, new_varinfo())
  val _ = app ins_initial_recs vs
  fun examine_cv t = let
    val (c, v) = dest_mult t
    val c_i = int_of_term c
  in
    case Redblackmap.peek (!table, v) of
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
  val items = Redblackmap.listItems (!table)
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
          (v, NIGHTMARE (rand (term_of_int (!maxupc)), set_diff vs [v]))
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

fun eliminate_an_existential0 t = let
  val (vs, body) = strip_exists t
  val (eliminate, category) = best_variable_to_eliminate vs body
  val v_n = index (fn v => v = eliminate) vs
  fun check_for_eqs tm = let
    val (lvs, body) = strip_exists tm
  in
    if length lvs = length vs then
      Profile.profile "eq" OmegaMath.OmegaEq
    else
      ALL_CONV
  end tm
  fun mypush_in_exs tm = let
    val (vs, body) = strip_exists tm
  in
    CooperSyntax.push_in_exists THENC
    EVERY_DISJ_CONV (RENAME_VARS_CONV (map (#1 o dest_var) vs) THENC
                     check_for_eqs)
  end tm
in
  push_nthvar_to_bot v_n THENC
  LAST_EXISTS_CONV (apply_fmve category) THENC
  mypush_in_exs
end t

val eliminate_an_existential =
    TRY_CONV OmegaMath.eliminate_negative_divides THENC
    EVERY_DISJ_CONV (TRY_CONV OmegaMath.eliminate_positive_divides THENC
                     eliminate_an_existential0) THENC
    REWRITE_CONV []

(* ----------------------------------------------------------------------
    eliminate_existentials t

    given a normalised term of the form
      ?x1..xn. body
    eliminate all of its existentials.
   ---------------------------------------------------------------------- *)

fun eliminate_existentials tm =
    if is_exists tm then
      (eliminate_an_existential THENC
       EVERY_DISJ_CONV eliminate_existentials) tm
    else REWRITE_CONV [] tm


(* ----------------------------------------------------------------------
    sym_normalise tm

    tm is of form
      ?x1..xn. body
    where body has no nested quantifiers.  Only difference with the
    normalisation routine in OmegaShell is that we don't automatically
    eliminate divisibility terms, because we're not necessarily going
    to be able to.  We also have to eliminate equality terms that survive
    the attempt to get rid of them with OmegaEq.
   ---------------------------------------------------------------------- *)

fun ISCONST_CONV tm = if is_const tm then ALL_CONV tm else NO_CONV tm
fun IFEXISTS c tm = if is_exists tm then c tm else ALL_CONV tm

val sym_normalise = let
  fun push_exs tm = let
    val vs = map (#1 o dest_var) (#1 (strip_exists tm))
  in
    CooperSyntax.push_in_exists THENC EVERY_DISJ_CONV (RENAME_VARS_CONV vs)
  end tm
  open OmegaMath
  val elim_eq = REWR_CONV (GSYM INT_LE_ANTISYM) THENC
                RAND_CONV leaf_normalise
in
  STRIP_QUANT_CONV (Canon.NNF_CONV leaf_normalise false THENC
                    REPEATC (CHANGED_CONV CSimp.csimp THENC
                             REWRITE_CONV [])) THENC
  push_exs THENC
  EVERY_DISJ_CONV (OmegaEq THENC DEPTH_CONV elim_eq THENC
                   TRY_CONV (REWR_CONV EXISTS_SIMP) THENC
                   IFEXISTS
                     (STRIP_QUANT_CONV Canon.PROP_DNF_CONV THENC push_exs))
end


(* ----------------------------------------------------------------------
    find_deep_existentials tm

   ---------------------------------------------------------------------- *)

fun is_bool_binop t = let
  val (f,args) = strip_comb t
in
  length args = 2 andalso is_const f andalso
  (List.exists (same_const f) [conjunction, disjunction]
   orelse same_const f equality andalso type_of (hd args) = bool)
end

fun IFEXISTS c tm = if is_exists tm then c tm else ALL_CONV tm

fun findelim_deep_existential tm = let
in
  if is_forall tm then
    (STRIP_QUANT_CONV findelim_deep_existential) ORELSEC
    (CooperSyntax.flip_foralls THENC RAND_CONV findelim_deep_existential)
  else if is_exists tm then
    (STRIP_QUANT_CONV findelim_deep_existential) ORELSEC
    (sym_normalise THENC EVERY_DISJ_CONV (IFEXISTS eliminate_an_existential))
  else if is_bool_binop tm then
    (LAND_CONV findelim_deep_existential) ORELSEC
    (RAND_CONV findelim_deep_existential)
  else if is_neg tm then
    RAND_CONV findelim_deep_existential
  else
    NO_CONV
end tm

end (* struct *)
