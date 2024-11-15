open HolKernel boolLib boolSimps bossLib Parse dep_rewrite
open arithmeticTheory monoidTheory groupTheory ringTheory fieldTheory ffBasicTheory

val _ = new_theory "ellipticCurve";

Datatype:
  weierstrass_curve =
  <| a: 'a
   ; b: 'a
   ; f: 'a ring
   |>
End

Definition WeierstrassEllipticCurve_def:
  WeierstrassEllipticCurve (c:'a weierstrass_curve) <=>
    FiniteField c.f /\ char c.f NOTIN {2; 3} /\
    c.a IN c.f.carrier /\
    c.b IN c.f.carrier
End

Definition weierstrassPoint_def:
  (weierstrassPoint c NONE = T) /\
  (weierstrassPoint c (SOME (x,y)) =
  (x IN c.f.carrier /\
   y IN c.f.carrier /\
   c.f.prod.exp y 2 =
     c.f.sum.op
       (c.f.sum.op (c.f.prod.exp x 3)
         (c.f.prod.op c.a x))
       c.b))
End

Theorem weierstrassPoint_NONE[simp]:
  weierstrassPoint c NONE
Proof
  rw[weierstrassPoint_def]
QED

Definition wec_add_given_slope_def:
  wec_add_given_slope (r :'a ring) (m:'a) px py qx =
  let rx = m ** 2 - px - qx in
  let ry = m * (px - rx) - py in
    (rx, ry)
End

Definition wec_add_def:
  wec_add a (r:'a ring) p NONE = p /\
  wec_add a r NONE q = q /\
  wec_add a r (SOME (px,py)) (SOME (qx,qy)) =
  if px = qx then
    if py = qy /\ py <> #0 then
      let m = (##3 * (px ** 2) + a) / (##2 * py) in
        SOME (wec_add_given_slope r m px py qx)
    else NONE
  else
    let m = (py - qy) / (px - qx) in
    SOME (wec_add_given_slope r m px py qx)
End

Definition WECGroup_def:
  WECGroup c = <|
    carrier := weierstrassPoint c
  ; op := wec_add c.a c.f
  ; id := NONE
  |>
End

val rdist =
  SPEC_ALL ring_mult_ladd
  |> UNDISCH_ALL
  |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> UNDISCH_ALL

val ldist =
  SPEC_ALL ring_mult_radd
  |> UNDISCH_ALL
  |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> UNDISCH_ALL


val ring_expand_conv =
  DEPTH_CONV $
  REWRITE_CONV
  FIRST_CONV[
    REWR_CONV rdist,
    REWR_CONV ldist
  ]
  REWRITE_CONV

fun field_hyp_tac (g as (asl, w)) =
  if is_conj w then
    (conj_tac \\ field_hyp_tac) g
  else
    (((
      irule ring_add_element ORELSE
      irule ring_sub_element ORELSE
      irule ring_mult_element ORELSE
      irule ring_neg_element ORELSE
      irule field_inv_element ORELSE
      irule ring_exp_element ORELSE
      first_assum MATCH_ACCEPT_TAC
     ) \\ field_hyp_tac)
     ORELSE (simp[] \\ NO_TAC)) g

Triviality THREE:
  3 = SUC (SUC (SUC 0))
Proof
  simp[]
QED

val expand_thms = [
 ring_mult_ladd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
,
 ring_mult_radd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
,
 ring_neg_neg |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL
,
 ring_num_0 |> SPEC_ALL
,
 ring_num_1 |> SPEC_ALL |> UNDISCH
,
 ring_num_mult_suc |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL
  |> UNDISCH_ALL |> SPEC_ALL
,
 ring_num_suc |> SPEC_ALL |> UNDISCH |> SPEC_ALL
,
 ring_exp_SUC |> SPEC_ALL
,
 ring_exp_0 |> SPEC_ALL
,
 ring_mult_rone |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_mult_lone |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_mult_rzero |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_mult_lzero |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_add_lzero |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_add_rzero |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ringUnitTheory.ring_inv_one |> SPEC_ALL |> UNDISCH_ALL
,
 ring_sub_eq |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH
,
 ring_add_lcancel |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
,
 ring_add_rcancel |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
,
 field_mult_lcancel |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO, ring_nonzero_eq] |> UNDISCH_ALL
,
 field_mult_rcancel |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO, ring_nonzero_eq] |> UNDISCH_ALL
,
 field_mult_rinv |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO, ring_nonzero_eq] |> UNDISCH_ALL
,
 field_mult_linv |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO, ring_nonzero_eq] |> UNDISCH_ALL
,
 ring_sub_def |> SPEC_ALL
,
 field_div_def |> SPEC_ALL
,
THREE, TWO, ONE
]

fun HYP_REWR_CONV thm tm =
  let
    val (tms, tys) = match_term (lhs (concl thm)) tm
    (* val () = print "hrc" *)
  in
    INST tms (INST_TYPE tys thm)
  end

val prod_comm = ring_mult_comm |> SPEC_ALL |> UNDISCH |> SPEC_ALL |>
  REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
val sum_comm = ring_add_comm |> SPEC_ALL |> UNDISCH |> SPEC_ALL |>
  REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL

val prod_assoc = ring_mult_assoc |> SPEC_ALL |> UNDISCH |> SPEC_ALL |>
  REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL |> SYM
val sum_assoc = ring_add_assoc |> SPEC_ALL |> UNDISCH |> SPEC_ALL |>
  REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL |> SYM

(*
repeat until no change:
  - try all the rewrites, if any fire continue
  - if + or * or reciprocal or negation or equality or ## or **, recurse into the subterms then continue
  - if + or *, ensure first term is on lhs or rewrite with comm and continue
  - if + or *, ensure lhs has only one term, else rewrite with assoc and continue
*)

val ring_recip_tm = ``r*.inv x``
val ring_neg_tm = ``r.sum.inv x``
val ring_numr_tm = ``ring_numr n``
val ring_prod_tm = ``r.prod.op x y``
val ring_sum_tm = ``r.sum.op x y``
val ring_exp_tm = ``r.prod.exp x n``

val [x, y] = ring_sum_tm |> strip_comb |> #2 |> tl
fun mk_ring_summands_acc pat =
  let
    fun f tm acc =
      let
        val (tms, tys) = match_term pat tm
        val xs = f (Term.subst tms (Term.inst tys x)) acc
        val ys = f (Term.subst tms (Term.inst tys y)) xs
      in
        ys
      end handle HOL_ERR _ => tm :: acc
  in
    f
  end
fun ring_summands tm = mk_ring_summands_acc ring_sum_tm tm []
fun ring_factors tm = mk_ring_summands_acc ring_prod_tm tm []

fun term_cmp t1 t2 = case Term.compare (t1, t2) of LESS => true | _ => false

fun IF_CONV P cnv1 cnv2 tm = if P tm then cnv1 tm else cnv2 tm
fun GUARD_CONV n P cnv = IF_CONV P cnv NO_CONV
  (*
    ((fn tm => (print n; ALL_CONV tm)) THENC PRINT_CONV THENC cnv)
    ((fn tm => (print "~"; print n; ALL_CONV tm)) THENC PRINT_CONV THENC NO_CONV)
    *)


fun liftOr P1 P2 x = P1 x orelse P2 x
fun liftAnd P1 P2 x = P1 x andalso P2 x

val sum_or_prod =
  (liftOr (can (match_term ring_sum_tm))
          (can (match_term ring_prod_tm)))

val sum_or_prod_or_exp =
  liftOr sum_or_prod (can (match_term ring_exp_tm))

val neg_or_recip =
  (liftOr (can (match_term ring_neg_tm))
          (can (match_term ring_recip_tm)))
val neg_or_recip_or_numr =
  liftOr neg_or_recip (can (match_term ring_numr_tm))

fun sum_prod_operands tm =
  let val [x,y] = strip_comb tm |> #2 |> tl in (x,y) end

fun lower_on_right sub tm =
  let
    val (x,y) = sum_prod_operands tm
    val xs = sub x
    val ys = sub y
    fun isLower tm = List.all (term_cmp tm) xs
  in
    List.exists isLower ys
  end

fun REPEATNC NONE = REPEATC
  | REPEATNC (SOME 0) = K ALL_CONV
  | REPEATNC (SOME n) = fn conv =>
      let
        fun f n = if n = 1 then conv else
          fn tm =>
            let
              val th = conv tm
            in
              case (SOME (f (n - 1) (rhs (concl th)))
                    handle UNCHANGED => NONE)
                of SOME rth => TRANS th rth
                 | NONE => th
            end
      in
        f n
      end

(*
val tm = top_goal() |> #2 |> rator |> rand |> lhs
val (fx, y) = dest_comb tm
val (f, x) = dest_comb fx
FIRST_CONV (List.map HYP_REWR_CONV expand_thms) y
*)

fun ring_conv literal_thms n =
let
  val check_clock =
    if Option.isSome n
    then fn c => fn tm =>
           if !c = 0 then raise UNCHANGED
           else (c := !c - 1; tm)
    else K I
  val split = if Option.isSome n then
    fn c => fn f => fn tm =>
      let
        val c1_start = !c div 2
        val c2_start = !c - c1_start
        val c1 = ref c1_start
        val c2 = ref c2_start
        fun account () = c := !c - c1_start + !c1 - c2_start + !c2
      in
        FORK_CONV (f c1, f c2) tm before account()
        handle UNCHANGED => (account(); raise UNCHANGED)
      end
    else fn c => fn f => BINOP_CONV (f c)
  fun step c tm =
     check_clock c tm |>
       FIRST_CONV [
         FIRST_CONV (List.map REWR_CONV literal_thms),
         FIRST_CONV (List.map HYP_REWR_CONV expand_thms),
         GUARD_CONV "2" neg_or_recip_or_numr (CHANGED_CONV (RAND_CONV (steps c))),
         GUARD_CONV "3" sum_or_prod_or_exp (CHANGED_CONV (split c steps)),
         GUARD_CONV "4" is_eq (CHANGED_CONV (split c steps)),
         GUARD_CONV "5" (liftAnd (can (match_term ring_sum_tm))
                             (lower_on_right ring_summands))
            (HYP_REWR_CONV sum_comm),
         GUARD_CONV "6" (liftAnd (can (match_term ring_prod_tm))
                             (lower_on_right ring_factors))
            (HYP_REWR_CONV prod_comm),
         GUARD_CONV "7" (liftAnd (can (match_term ring_sum_tm))
                             (can (match_term ring_sum_tm) o
                              #2 o sum_prod_operands))
            (HYP_REWR_CONV sum_assoc),
         GUARD_CONV "8" (liftAnd (can (match_term ring_prod_tm))
                             (can (match_term ring_prod_tm) o
                              #2 o sum_prod_operands))
            (HYP_REWR_CONV prod_assoc)
       ]
  and steps c tm = REPEATC (step c) tm
in
  steps (ref (case n of SOME n => n | NONE => 0))
end

  (*
val ring_expand_conv =
  REPEATC (TOP_DEPTH_CONV (FIRST_CONV (List.map HYP_REWR_CONV expand_thms)))

    val eth =  ring_expand_conv (#2 (top_goal()))
DISCH_ALL eth
*)

fun dep_tac (cnv:conv) (g:goal) =
  let
    val th = cnv (#2 g)
    val hyps = list_mk_conj (hyp th)
    val w = mk_conj (hyps, rhs (concl th))
    fun v ths =
      let
        val sth = el 1 ths
        val hths = CONJUNCTS (CONJUNCT1 sth)
        val gth = CONJUNCT2 sth
        val pth = List.foldl (uncurry PROVE_HYP) th hths
      in
        EQ_MP (SYM pth) gth
      end
  in
    ([(#1 g, w)], v)
  end

fun ring_tac thms n : tactic = dep_tac (ring_conv thms n)

(*
fun ring_expand_tac (g:goal) =
  let
    val eth = ring_expand_conv (#2 g)
    val hyps = list_mk_conj (hyp eth)
    val w = mk_conj (hyps, rhs (concl eth))
    fun v ths =
      let
        val th = el 1 ths
        val hths = CONJUNCTS (CONJUNCT1 th)
        val gth = CONJUNCT2 th
        val peth = List.foldl (uncurry PROVE_HYP) eth hths
      in
        EQ_MP (SYM peth) gth
      end
  in
    ([(#1 g, w)], v)
  end

fun ring_normalise_factor_conv tm =
  let
    val (tms, tys) = match_term ring_prod_tm tm
  in
    val fs = ring_factors tm
  in
    if List.length fs = 1 then raise UNCHANGED
    else
      let
        val sorted = sort term_cmp fs
      in
      end
  end

fun ring_normalise_summand_conv tm =

fun ring_normalise_conv tm =
  let
    val ss = ring_summands tm
  in
    if List.length ss > 1 then
      let
        val ss = List.map ring_normalise_summand_conv ss
        (* sort via AC *)
      in
    else
      raise UNCHANGED
  end

ring_normalise_conv  ``r.sum.inv (r.sum.inv a)``
*)

Theorem wec_add_in_carrier:
  Field c.f /\ {c.a; c.b} SUBSET c.f.carrier /\ 4 <= char c.f /\
  weierstrassPoint c p /\ weierstrassPoint c q ==>
  weierstrassPoint c (wec_add c.a c.f p q)
Proof
  Cases_on`p` \\ Cases_on`q` \\ rw[wec_add_def]
  \\ qmatch_goalsub_rename_tac`_ _ _ (SOME p) (SOME q)`
  \\ PairCases_on`p` \\ PairCases_on`q`
  \\ simp[wec_add_def]
  \\ Cases_on`p0 = q0 /\ p1 <> q1` >- simp[]
  \\ qmatch_goalsub_abbrev_tac`r.sum`
  \\ `p0 IN R /\ p1 IN R /\ q0 IN R /\ q1 IN R` by fs[weierstrassPoint_def]
  \\ qmatch_goalsub_abbrev_tac`q023 + c.a`
  \\ qmatch_goalsub_abbrev_tac`(q023 + _) * _.inv p12`
  \\ `q023 IN R` by simp[Abbr`q023`]
  \\ Cases_on`p0 = q0` \\ fs[]
  >- (
    rw[]
    \\ asm_simp_tac (std_ss++LET_ss) [wec_add_given_slope_def]
    \\ `p1 IN R+` by simp[ring_nonzero_def]
    \\ `p12 IN R+`
    by (
      simp[Abbr`p12`]
      \\ fs[ring_nonzero_def, field_mult_eq_zero]
      \\ irule char_minimal
      \\ simp[] )
    \\ asm_simp_tac std_ss [weierstrassPoint_def]
    \\ conj_asm1_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ qmatch_goalsub_abbrev_tac`f ** 2 - p0 - p0`
    \\ `f IN R` by simp[Abbr`f`]
    \\ rewrite_tac[ring_sub_def]
    \\ DEP_REWRITE_TAC[ring_neg_add] \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[ring_neg_neg] \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GSYM ring_add_assoc] \\ conj_tac >- simp[]
    \\ qpat_x_assum`weierstrassPoint _ _`mp_tac
    \\ asm_simp_tac std_ss [weierstrassPoint_def]
    \\ `Ring r` by simp[]
    \\ `p0 * c.a IN R` by simp[]
    \\ `p0 * p0 * p0 IN R` by simp[]
    \\ `p0 * c.a + p0 * p0 * p0 IN R` by simp[]
    \\ CONV_TAC(LAND_CONV (ring_conv [] NONE))
    \\ qunabbrev_tac`p12`
    \\ qunabbrev_tac`q023`
    \\ qunabbrev_tac`f`
    \\ strip_tac
    \\ qpat_assum`##2 * p1 IN _`mp_tac
    \\ `#1 IN R` by simp[]
    \\ CONV_TAC(LAND_CONV (LAND_CONV (ring_conv [] NONE)))
    \\ strip_tac
    \\ qpat_assum`p1 * p1 = _`(fn th => ring_tac [th] NONE)
    \\ CHANGED_TAC(qpat_assum`_ = _`(fn th => ring_tac [th] (SOME 4096)))
    \\ conj_tac >- field_hyp_tac
    \\ rpt(conj_tac >- field_hyp_tac)
    simp[]
    CONV_TAC(LAND_CONV (ring_conv [] NONE))
    ring_num_suc
    \\ CHANGED_TAC(qpat_assum`_ = _`(fn th => ring_tac [th] (SOME 65536)) \\ conj_tac >- field_hyp_tac)

    \\ rpt (conj_tac >- field_hyp_tac)
    \\ conj_tac >- field_hyp_tac

    \\ `-p0 IN R` by simp[]
    \\ `-p1 IN R` by simp[]
    \\ `-(f ** 2) IN R` by simp[]
    \\ `(f ** 2) IN R` by simp[]
    \\ CONV_TAC(RAND_CONV ring_conv)

    \\ fs[weierstrassPoint_def]
    \\ ring_tac
    reverse conj_tac
    Globals.max_print_depth := 15
    expand_thms
    \\ DEP_REWRITE_TAC[ring_mult_radd, ring_mult_ladd]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ `##2 * p1 = p1 + p1`
    by (
      rewrite_tac[TWO, ONE]
      \\ DEP_REWRITE_TAC[ring_num_mult_suc]
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ ring_tac

    \\ DEP_REWRITE_TAC[ring_num_mult_suc,
         ring_exp_SUC, ring_num_0, ring_exp_0,
         ring_mult_lzero, ring_mult_rzero,
         ring_mult_rone, ring_mult_lone,
         ring_add_lzero, ring_add_rzero,
         ring_neg_sub, ring_neg_add, ring_neg_neg,
         ring_mult_neg_neg, GSYM ring_mult_lneg,
         THREE, TWO, ONE]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ DEP_REWRITE_TAC[ring_mult_radd]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ qmatch_goalsub_abbrev_tac`p02 + p02 + p02`
    \\ qmatch_goalsub_abbrev_tac`p023 * p1v * p0`
    \\ `p02 IN R /\ p1v IN R /\ p023 IN R` by (
      qunabbrev_tac`p02`
      \\ qunabbrev_tac`p1v`
      \\ qunabbrev_tac`p023`
      \\ field_hyp_tac )
    \\ DEP_REWRITE_TAC[GSYM ring_add_assoc]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ conj_tac >- field_hyp_tac
    \\ DEP_REWRITE_TAC[ring_mult_ladd]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ DEP_REWRITE_TAC[ring_mult_radd]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac
    \\ conj_tac >- field_hyp_tac


    irule ring_add_element
    irule ring_mult_element
    \\ conj_tac
    >- field_hyp_tac

    irule field_inv_element

    ring_
    m``|/ _ IN R``
    irule ring_mult_element

    irule ring_add_element
    \\ asm_simp_tac std_ss []
    ring_zero_mul
    ring_num_mult_zero
    overload_info_for"##"
    m``r.prod.op #0 _``

    \\ conj_tac >- simp[]
    \\ conj_tac >- (
      conj_tac >- simp[]
      conj_tac >- (
        irule ring_add_element
        \\ conj_tac >- simp[]
        \\ reverse conj_tac >- simp[]
        \\ irule ring_add_element
        \\ conj_tac >- simp[]
        \\ conj_tac >- simp[]
        \\ irule ring_neg_element
        \\ conj_tac >- simp[]

    \\ CONV_TAC (REWRITE_CONV [ldist, rdist])
    help"REWRITE_CONV"

    2
    \\ qmatch_goalsub_abbrev_tac`f * p03f2`
    \\ `p03f2 = ##3 * p0 - f ** 2`
    by (
      simp[Abbr`p03f2`]
      \\ `3 = SUC(SUC(SUC 0))` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ simp[ring_num_mult_suc]
      \\ DEP_REWRITE_TAC[ring_add_assoc] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_lcancel]
      \\ conj_tac >- ( simp[] \\ irule ring_add_element \\ simp[] )
      \\ DEP_ONCE_REWRITE_TAC[ring_add_comm]
      \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_assoc] \\ simp[] )
    \\ qunabbrev_tac`p03f2`
    \\ pop_assum SUBST_ALL_TAC


    HOL_Interactive.toggle_quietdec()
    \\ DEP_REWRITE_TAC[ring_neg_sub]
    ring_sub_sub
    m``ring_sub r p (ring_sub r x y)``
    f"ring_sub"

    m``x + y IN R``
  >- (
    `p0 - q0 <> #0` by simp[ring_sub_eq_zero] \\ fs[]
    \\ `p0 + -q0 IN R+` by simp[ring_nonzero_def]
    \\ `|/ (p0 + -q0) IN R` by simp[]
    \\ simp_tac (std_ss++LET_ss) [ec_add_given_slope_def]
    \\ qmatch_goalsub_abbrev_tac`f ** 2`
    \\ `f IN R` by simp[Abbr`f`]
    \\ qmatch_goalsub_abbrev_tac`xr,_`
    \\ `xr IN R` by simp[Abbr`xr`]
    \\ DEP_REWRITE_TAC[ring_neg_add] \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GSYM ring_mult_rneg] \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[ring_neg_sub] \\ conj_tac >- simp[]
    \\ asm_simp_tac std_ss [curvePoint_def]
    \\ conj_tac >- simp[]
    ff"add""exp"

    \\ `q0 - xr = q0 - f ** 2 + p0 + p1`
    by (
      qunabbrev_tac`xr`
      \\ rewrite_tac[ring_sub_def]
      \\ DEP_REWRITE_TAC[ring_neg_add] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_neg_neg] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_assoc]
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC

    \\ DEP_REWRITE_TAC[GSYM ring_mult_rsub]
    \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ conj_tac >- simp[]
    \\ asm_simp_tac std_ss [curvePoint_def]
    \\ conj_tac >- simp[]
    \\ conj_tac >- (
      irule ring_add_element
      \\ conj_tac >- simp[]
      \\ conj_tac >- simp[]
      \\ irule ring_sub_element
      \\ conj_tac >- simp[]
      \\ reverse conj_tac >- simp[]
      \\ irule ring_sub_element
      \\ conj_tac >- simp[]
      \\ reverse conj_tac >- simp[]
      \\ simp[] )
    \\ qmatch_goalsub_abbrev_tac`q1 + q2`
    \\ qmatch_goalsub_abbrev_tac`_ = f2 ** 3 + _ + _`
    \\ `q2 = f * f2 - f * q0`
    by (
      qunabbrev_tac`q2`
      \\ qunabbrev_tac`f2`
      \\ DEP_REWRITE_TAC[GSYM ring_mult_rsub]
      \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
      \\ simp[] )
    \\ qunabbrev_tac`q2`
    \\ pop_assum SUBST_ALL_TAC
    \\ qmatch_goalsub_abbrev_tac`q1 + f1`
    \\ `f2 IN R` by simp[Abbr`f2`]
    \\ `f1 IN R` by simp[Abbr`f1`]
    \\ `q1 ** 2 = q0 ** 3 + c.a * q0 + c.b`
    by fs[curvePoint_def]
    \\ `(q1 + f1) ** 2 = q1 ** 2 + f1 ** 2 + r.sum.exp (q1 * f1) 2`
    by (
      rewrite_tac[TWO, ONE]
      \\ rewrite_tac[ring_exp_SUC, ring_exp_0, group_exp_SUC, group_exp_0]
      \\ DEP_REWRITE_TAC[ring_mult_rone, ring_add_rzero] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_mult_ladd] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_mult_radd] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_assoc] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_lcancel] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[GSYM ring_add_assoc] \\ conj_tac >- simp[]
      \\ DEP_ONCE_REWRITE_TAC[ring_add_comm] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_assoc] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_add_lcancel] \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[ring_mult_comm] \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ pop_assum SUBST_ALL_TAC

      m``r.sum.op a b = a + c``
      ff"ring""canc"
      ring_add_assoc

    curvePoint_def

  >- (
    simp[ec_add_given_slope_def]
    \\ DEP_REWRITE_TAC[field_mult_ladd]
    \\ simp[]
    m``pp.inv _ IN R``
    \\ cheat )
  \\ simp[ec_add_given_slope_def]
  \\ fs[curvePoint_def]


Theorem Group_ECGroup:
  EllipticCurve c ==> Group (ECGroup c)
Proof
  rw[EllipticCurve_def, group_def_alt]
  Monoid_def
  monoid_invertibles_def
  m``_ ==> Group _``
  m``Group _ <=> _``
*)

val _ = export_theory();
