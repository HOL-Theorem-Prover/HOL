open HolKernel Parse boolLib bossLib;

open pairTheory
open walkTheory walkstarTheory unifDefTheory
open whileTheory
open substTheory rmfmapTheory
open cpsTheory cpsLib

open relationTheory sptreeTheory pred_setTheory finite_mapTheory optionTheory

val _ = new_theory "tcallUnif";

Definition ispair_def[simp]:
  ispair (Pair t1 t2) = T ∧
  ispair (Var v) = F ∧
  ispair (Const c) = F
End
Definition isconst_def[simp]:
  isconst (Const c) = T ∧
  isconst (Var v) = F ∧
  isconst (Pair c1 c2) = F
End

Definition destpair_def[simp]:
  destpair (term$Pair c1 c2) = (c1,c2)
End


Definition destvar_def[simp]:
  destvar (Var v) = v
End

Theorem contify_optbind:
  contify k (OPTION_BIND opt f) =
  contify (λov. case ov of
                  NONE => k NONE
                | SOME x => contify k (f x))
          opt
Proof
  Cases_on ‘opt’ >> simp[contify_def]
QED

Theorem contify_term_case:
  contify k (term_CASE t v p c) =
  contify (λt. case t of Var n => contify k (v n)
                      | Pair t1 t2 => contify k (p t1 t2)
                      | Const cn => contify k (c cn))
          t
Proof
  Cases_on ‘t’ >> simp[contify_def]
QED

Theorem sum_CASE_pair_CASE:
  sum_CASE (pair_CASE p f) lf rf =
  pair_CASE p (λa b. sum_CASE (f a b) lf rf)
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem sum_CASE_term_CASE:
  sum_CASE (term_CASE t vf pf cf) lf rf =
  term_CASE t
            (λv. sum_CASE (vf v) lf rf)
            (λt1 t2. sum_CASE (pf t1 t2) lf rf)
            (λcn. sum_CASE (cf cn) lf rf)
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem sum_CASE_COND:
  sum_CASE (if p then t else e) lf rf =
  if p then sum_CASE t lf rf else sum_CASE e lf rf
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem sum_CASE_option_CASE:
  sum_CASE (option_CASE ov n sf) lf rf =
  option_CASE ov (sum_CASE n lf rf) (λv. sum_CASE (sf v) lf rf)
Proof
  Cases_on ‘ov’ >> simp[]
QED

Theorem sum_CASE_list_CASE:
  sum_CASE (list_CASE k i tkf) lf rf =
  list_CASE k (sum_CASE i lf rf)
              (λt k. sum_CASE (tkf t k) lf rf)
Proof
  Cases_on ‘k’ >> simp[]
QED

Overload tcall[local] = “TAILCALL”
Overload trec[local] = “TAILREC”

val svwalk_code = rand “
tcall (λ(s,nm).
        case lookup nm s of
          NONE => INR (Var nm)
        | SOME (Var nm') => INL (s,nm')
        | SOME (Pair t1 t2) => INR (Pair t1 t2)
        | SOME (Const c) => INR (Const c))
                  ”

Theorem svwalk_tcallish:
  !x.
    (λ(s,nm). swfs s ∧ wf s) x ==>
    (λ(s,nm). svwalk s nm) x =
    tcall ^svwalk_code (λ(s,nm). svwalk s nm) x
Proof
  simp[TAILCALL_def, FORALL_PROD, sum_CASE_term_CASE,
       sum_CASE_COND] >> rw[] >>
  rename [‘svwalk s k = _’] >> Cases_on ‘lookup k s’ >>
  simp[SimpLHS, Once svwalk_thm] >> simp[] >>
  simp[sum_CASE_term_CASE]
QED

Theorem svwalk_cleaned:
  !x. (λ(s,nm). swfs s ∧ wf s) x ==>
      (λ(s,nm). svwalk s nm) x = trec ^svwalk_code x
Proof
  match_mp_tac TAILREC_GUARD_ELIMINATION >> rpt conj_tac
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >> simp[])
  >- (simp[FORALL_PROD, AllCaseEqs(), swfs_def] >> rw[] >>
      rename [‘wfs (sp2fm s)’] >>
      qexists ‘λ(s0,nm0) (s1,nm). s0 = s ∧ s1 = s ∧ vR (sp2fm s) nm0 nm’ >>
      simp[] >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >>
          irule WF_SUBSET >>
          qexists ‘inv_image (vR $ sp2fm s) SND’ >>
          simp[FORALL_PROD] >>
          simp[WF_inv_image, GSYM wfs_def]) >>
      rpt gen_tac >> strip_tac >>
      rename [‘RTC _ (s0,_)(s,_)’]>>
      ‘s0 = s’ by (qpat_x_assum ‘RTC _ _ _’ mp_tac >> Induct_on ‘RTC’ >>
                   simp[FORALL_PROD]) >>
      gvs[vR_def]) >>
  MATCH_ACCEPT_TAC svwalk_tcallish
QED

Definition tvwalk_def:
  tvwalk s nm = trec ^svwalk_code (s,nm)
End

Theorem tvwalk_thm =
        tvwalk_def
          |> SRULE[Once TAILREC, TAILCALL_def, sum_CASE_option_CASE,
                   sum_CASE_term_CASE]
          |> SRULE[GSYM tvwalk_def]

Theorem tvwalk_correct = svwalk_cleaned |> SRULE[FORALL_PROD, GSYM tvwalk_def]

Definition twalk_def:
  twalk s t =
  case t of
    Var v => tvwalk s v
  | Pair t1 t2 => Pair t1 t2
  | Const c => Const c
End

Theorem twalk_correct:
  swfs s ∧ wf s ⇒ swalk s t = twalk s t
Proof
  simp[twalk_def, swalk_thm, tvwalk_correct]
QED

Definition koc_def:
  koc (s:α term num_map) t v k = cwc (soc s t v) k
End

Theorem disj2cond[local] = DECIDE “p ∨ q ⇔ if p then T else q”
Theorem koc_thm =
        koc_def
          |> SPEC_ALL
          |> SRULE [Once soc_walking, ASSUME “swfs (s:'a term num_map)”,
                    ASSUME “wf (s:'a term num_map)”, twalk_correct,
                    GSYM contify_cwc]
          |> REWRITE_RULE[disj2cond]
          |> CONV_RULE (TOP_DEPTH_CONV (contify_CONV[contify_term_case]))
          |> SRULE [cwcp “term$Pair”, cwcp “term$Pair x0”, cwcp “twalk”,
                    cwcp “$=”, cwcp “(\/)”, cwcp “soc”,
                    cwcp “soc s”, cwcp “twalk s”, cwcp “$= n”]
          |> SRULE [GSYM koc_def]
          |> SRULE [cwc_def]

Definition apply_ockont_def:
  apply_ockont s v [] b = b /\
  apply_ockont s v (t::ts) b =
  if b then T
  else koc s t v (λb. apply_ockont s v ts b)
End

Theorem apply_ockontT[simp]:
  apply_ockont s v k T = T
Proof
  Induct_on ‘k’ >> simp[apply_ockont_def]
QED

Definition dfkoc_def:
  dfkoc s t v k = koc s t v (apply_ockont s v k)
End

(* CV-translatable *)
Theorem apply_ockont_thm =
        REWRITE_RULE [GSYM dfkoc_def] $
              LIST_CONJ [cj 1 apply_ockont_def,
                         cj 2 apply_ockont_def
                           |> SRULE [SF ETA_ss]
                           |> REWRITE_RULE [disj2cond]
                         ]

Theorem dfkoc_thm =
        dfkoc_def
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE [koc_thm]
          |> SRULE[GSYM apply_ockont_thm, SF ETA_ss, GSYM dfkoc_def]

Theorem dfkoc_removed:
  dfkoc s t v k = apply_ockont s v (t :: k) F
Proof
  simp[apply_ockont_thm]
QED

Theorem dfkoc_nonrecursive =
        dfkoc_thm |> CONV_RULE (RAND_CONV (REWRITE_CONV[dfkoc_removed]))

(* "occurs-check worklist" *)
Overload ocwl0 = “apply_ockont”

Theorem ocwl0_thm =
        apply_ockont_thm
          |> CONJUNCTS
          |> map (GEN_ALL o PURE_REWRITE_RULE[dfkoc_nonrecursive] o SPEC_ALL)
          |> LIST_CONJ

Definition kocwl_def: kocwl s v k = ocwl0 s v k F
End

Theorem ocwl0_varcheck: ocwl0 s v k b = if b then T else kocwl s v k
Proof
  rw[kocwl_def] >> Cases_on ‘b’ >> simp[]
QED

Theorem kocwl_thm =
        ocwl0_thm |> SRULE[GSYM kocwl_def]
                  |> SRULE[ocwl0_varcheck]
                  |> SRULE[FORALL_BOOL]
                  |> PURE_REWRITE_RULE [DECIDE “~p = (p = F)”,
                                        DECIDE “p \/ q <=> if p then T else q”]

val oc_code = rand “
               tcall
               (λ(s,k). case k of
                    [] => INR F
                  | t :: k =>
                      case twalk s t of
                        Var n => if v = n then INR T else INL (s,k)
                      | Pair t1 t2 => INL (s, t1 :: t2 :: k)
                      | Const _ => INL (s,k))
”


Theorem kocwl_tcallish:
  !x.
    (λ(s,sm). swfs s ∧ wf s) x ==>
    (λ(s,k). kocwl s v k) x =
    tcall ^oc_code (λ(s,k). kocwl s v k) x
Proof
  simp[TAILCALL_def, FORALL_PROD, sum_CASE_list_CASE, sum_CASE_term_CASE,
       sum_CASE_COND] >> rw[] >>
  rename [‘kocwl s v k ⇔ _’] >> Cases_on ‘k’
  >- (simp[cj 1 kocwl_thm]) >>
  simp[SimpLHS, Once kocwl_thm] >> simp[]
QED

Overload BAG_OF_LIST = “FOLDR BAG_INSERT EMPTY_BAG”

Theorem FINITE_BAG_OF_LIST[simp]:
  FINITE_BAG (BAG_OF_LIST l)
Proof
  Induct_on ‘l’ >> simp[]
QED

Definition BAG_OF_SUM[simp]:
  BAG_OF_SUM (INL (t,k)) = BAG_OF_LIST (t :: k) /\
  BAG_OF_SUM (INR (k,b)) = BAG_OF_LIST k
End

Definition ocR_def:
  ocR (s:α term num_map) =
  inv_image (pair$RPROD (=) (mlt1 (walkstarR (sp2fm s))))
            (λ(s:α term num_map,k:α term list). (s, BAG_OF_LIST k))
End

Theorem WF_ocR:
  swfs s ==> WF (ocR s)
Proof
  strip_tac >> gs[ocR_def, swfs_def] >>
  irule WF_inv_image >>
  irule WF_SUBSET >>
  simp[FORALL_PROD] >>
  qexists ‘inv_image (mlt1 (walkstarR (sp2fm s))) SND’ >>
  simp[] >>
  irule WF_inv_image >>
  irule bagTheory.WF_mlt1 >>
  irule walkstar_thWF >> simp[]
QED

Theorem mlt1_BAG_INSERT:
  FINITE_BAG b ==> mlt1 R b (BAG_INSERT e b)
Proof
  strip_tac >>
  simp[bagTheory.mlt1_def, bagTheory.BAG_INSERT_UNION] >>
  simp[bagTheory.EL_BAG,
       AC bagTheory.COMM_BAG_UNION bagTheory.ASSOC_BAG_UNION] >>
  irule_at Any EQ_REFL >> qexists ‘EMPTY_BAG’ >> simp[]
QED

Theorem RTC_ocR_preserves_subst:
  !x y. (ocR s0)^* (s1, x) (s2, y) ==> s1 = s2
Proof
  Induct_on ‘RTC’ >> simp[ocR_def, PAIR_REL] >>
  simp[FORALL_PROD, LEX_DEF] >> metis_tac[]
QED

Theorem ocwl_cleaned0:
  !x. (λ(s,sm). swfs s ∧ wf s) x ==> (λ(s,k). kocwl s v k) x = trec ^oc_code x
Proof
  match_mp_tac TAILREC_GUARD_ELIMINATION >> rpt conj_tac
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >> simp[])
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >>
      rename [‘swfs th’] >>
      qexists ‘ocR th’ >> simp[] >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >> simp[WF_ocR]) >>
      rw[] >>
      simp[ocR_def, PAIR_REL, LEX_DEF, mlt1_BAG_INSERT] >>
      simp[bagTheory.mlt1_def] >>
      rename [‘twalk s t = Pair t1 t2’] >>
      qexistsl [‘t’, ‘{| t1; t2 |}’] >>
      simp[bagTheory.BAG_UNION_INSERT] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      gs[GSYM twalk_correct] >>
      dxrule_then strip_assume_tac RTC_ocR_preserves_subst >>
      gvs[swalk_def, swfs_def] >>
      metis_tac[walkstar_th1, walkstar_th2]) >>
  MATCH_ACCEPT_TAC kocwl_tcallish
QED

Definition tocwl_def:
  tocwl s v k = trec ^oc_code (s, k)
End

(* CV-translatable:
     refers to itself, and twalk only
*)
Theorem tocwl_thm =
        tocwl_def |> SRULE[TAILREC_TAILCALL]
                  |> SRULE[TAILCALL_def, sum_CASE_list_CASE, sum_CASE_term_CASE,
                           sum_CASE_COND]
                  |> SRULE[GSYM tocwl_def]
                  |> REWRITE_RULE[disj2cond]

Theorem tocwl_correct:
  swfs s ∧ wf s ==> (soc s t v ⇔ tocwl s v [t])
Proof
  simp[tocwl_def, GSYM ocwl_cleaned0, apply_ockont_def, kocwl_def,
       koc_def, apply_ockont_def, cwc_def]
QED

Definition kunify_def:
  kunify (s:α term num_map) t1 t2 k = cwc (sunify s t1 t2) k
End

Theorem disj_oc:
  swfs s ∧ wf s ==> (soc s t1 v \/ soc s t2 v <=> tocwl s v [t1; t2])
Proof
  simp[tocwl_def, GSYM ocwl_cleaned0, kocwl_def, apply_ockont_def,
       koc_def, cwc_def]
QED

Theorem kunify_thm =
        kunify_def
          |> SPEC_ALL
          |> SRULE [Once sunify_thm, GSYM contify_cwc,
                    twalk_correct, disj_oc,
                    ASSUME “swfs (s:α term num_map)”,
                    ASSUME “wf (s:α term num_map)”]
          |> CONV_RULE (TOP_DEPTH_CONV (contify_CONV[contify_term_case,
                                                     contify_option_case,
                                                     contify_pair_case,
                                                     contify_optbind]))
          |> SRULE [cwcp “term$Pair”, cwcp “term$Pair x0”, cwcp “CONS”,
                    cwcp “SOME”, cwcp “CONS x”, cwcp “term$Var”,
                    cwcp “twalk”, cwcp “sptree$insert”, cwcp “$,”,
                    cwcp “sunify”,cwcp “sptree$insert x”,
                    cwcp “sptree$insert x y”,
                    cwcp “sunify s”,
                    cwcp “Const”, cwcp “twalk s”,
                    cwcp “$, x”, cwcp “$=”, cwcp “tocwl”, cwcp “tocwl s”,
                    cwcp “tocwl s n”, cwcp “$= x”]
          |> SRULE [GSYM kunify_def]

Definition apply_unifkont_def:
  apply_unifkont [] x = x /\
  apply_unifkont ((t1,t2)::k) NONE = NONE /\
  apply_unifkont ((t1,t2)::k) (SOME s) = kunify s t1 t2 (apply_unifkont k)
End

Definition dfkunify_def:
  dfkunify (s:α term num_map) t1 t2 k = kunify s t1 t2 (apply_unifkont k)
End

Theorem apply_unifkont_thm =
        SRULE [GSYM dfkunify_def, SF ETA_ss] apply_unifkont_def


Theorem apply_unifkont_NONE:
  apply_unifkont k NONE = NONE
Proof
  Cases_on ‘k’ >> simp[apply_unifkont_def] >>
  Cases_on ‘h’ >> simp[apply_unifkont_def]
QED

Theorem abs_EQ_apply_unifkont:
  (λov. case ov of NONE => NONE | SOME s => dfkunify s t1 t2 k) =
  apply_unifkont ((t1, t2)::k)
Proof
  simp[FUN_EQ_THM, apply_unifkont_def, FORALL_OPTION, SF ETA_ss] >>
  simp[dfkunify_def]
QED

Theorem dfkunify_thm =
        dfkunify_def
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE [kunify_thm]
          |> SRULE[GSYM dfkunify_def, apply_unifkont_NONE,
                   abs_EQ_apply_unifkont]
          |> CONV_RULE (RHS_CONV $
                         REWRITE_CONV [GSYM $ cj 3 $ apply_unifkont_thm])

Overload unifywl0 = “apply_unifkont”

Theorem unifywl0 =
        PURE_REWRITE_RULE[dfkunify_thm]
             (LIST_CONJ (map SPEC_ALL $ CONJUNCTS apply_unifkont_thm))

(* remove slightly unnecessary use of SOME *)
Definition kunifywl_def:
  kunifywl s k = unifywl0 k (SOME s)
End

Theorem unifywl0_NIL = Q.INST [‘x’ |-> ‘SOME s’] $ cj 1 unifywl0

Theorem kunifywl_thm =
        REWRITE_RULE [GSYM kunifywl_def] (CONJ unifywl0_NIL $ cj 3 unifywl0)

(* now to do guard-elimination *)

fun findin f t =
  if aconv f t then SOME []
  else
    case total dest_comb t of
      NONE => NONE
    | SOME (t1,t2) =>
        case findin f t1 of
          NONE => NONE
        | SOME pfx => SOME (pfx @ [t2])


fun tcallify fn_t inty t =
  if TypeBase.is_case t then
    let val (f, ts) = strip_comb t
        val {Thy,Name,Ty} = dest_thy_const f
        val f0 = prim_mk_const{Name=Name,Thy=Thy}
        val basety = type_of f0
        val (argtys, rngty) = strip_fun basety
        val rng_th = match_type rngty (sumSyntax.mk_sum(inty,type_of t))
        val argty_th = match_type (hd argtys) (type_of (hd ts))
        val ft = Term.inst (rng_th @ argty_th) f0
        val ft1 = mk_comb(ft, hd ts)
        val ts' = map (tcallify fn_t inty) (tl ts)
    in
      list_mk_comb(ft1, ts')
    end
  else
    case dest_term t of
      CONST _ => sumSyntax.mk_inr(t,inty)
    | VAR _ => sumSyntax.mk_inr(t,inty)
    | LAMB(vt,bt) => mk_abs(vt, tcallify fn_t inty bt)
    | COMB _ =>
      case findin fn_t t of
        NONE => sumSyntax.mk_inr(t,inty)
      | SOME args => sumSyntax.mk_inl(pairSyntax.list_mk_pair args, type_of t)

fun tcallify_th th =
  let val (l,r) = dest_eq (concl th)
      val (lf, args) = strip_comb l
      val atup = pairSyntax.list_mk_pair args
      val inty = type_of atup
      val body_t = tcallify lf inty r
  in
      pairSyntax.mk_pabs(atup, body_t)
  end

val unify_code =
  DefnBase.one_line_ify NONE kunifywl_thm |> tcallify_th

Definition ucode_def:
  ucode = ^unify_code
End

Theorem kunifywl_tcallish:
  !x.
    (λ(s,k). swfs s ∧ wf s) x ==>
    (λ(s,k). kunifywl s k) x =
    tcall ucode (λ(s,k). kunifywl s k) x
Proof
  simp[TAILCALL_def, FORALL_PROD, sum_CASE_list_CASE, sum_CASE_term_CASE,
       sum_CASE_COND, sum_CASE_pair_CASE, ucode_def] >> rw[] >>
  rename [‘kunifywl s k = _’] >> Cases_on ‘k’
  >- (simp[cj 1 kunifywl_thm]) >>
  rename [‘kunifywl s (h::t)’] >> Cases_on ‘h’ >>
  simp[SimpLHS, Once kunifywl_thm] >> simp[]
QED

Definition plist_vars_def[simp]:
  plist_vars [] = {} ∧
  plist_vars ((t1,t2) :: tps) = vars t1 ∪ vars t2 ∪ plist_vars tps
End

Theorem FINITE_plist_vars[simp]:
  FINITE (plist_vars tps)
Proof
  Induct_on ‘tps’ >> simp[FORALL_PROD]
QED

Definition kuR_def:
  kuR (s : α term num_map, wl : (α term # α term) list) (s0,wl0) ⇔
    wf s ∧ swfs s ∧ wf s0 ∧ swfs s0 ∧ sp2fm s0 ⊑ sp2fm s ∧
    (substvars $ sp2fm s) ∪ plist_vars wl ⊆
    (substvars $ sp2fm s0) ∪ plist_vars wl0 ∧
    mlt1 (measure
          (λ(t1,t2).
             pair_count (walk* (sp2fm s) t1) +
             pair_count (walk* (sp2fm s) t2)))
         (BAG_OF_LIST wl)
         (BAG_OF_LIST wl0)
End

Theorem WF_kuR:
  WF kuR
Proof
  simp[WF_DEF] >> qx_gen_tac ‘A’ >>
  disch_then $ qx_choose_then ‘a’ assume_tac >> CCONTR_TAC >>
  gs[DECIDE “¬p ∨ q ⇔ p ⇒ q”] >>
  ‘∃s0 wl0. a = (s0,wl0)’ by (Cases_on ‘a’ >> simp[])>>
  gvs[FORALL_PROD, EXISTS_PROD] >>
  reverse $ Cases_on ‘swfs s0’
  >- (first_x_assum drule >> simp[kuR_def]) >>
  reverse $ Cases_on ‘wf s0’
  >- (first_x_assum drule >> simp[kuR_def]) >>
  qabbrev_tac ‘R = λ(a,b) (x,y). kuR (a,b) (x,y) ∧ A (a,b)’>>
  ‘∀a b x y. kuR (a,b) (x,y) ∧ A(a,b) ⇔ R (a,b) (x,y)’
    by simp[Abbr‘R’] >>
  qpat_x_assum ‘Abbrev(R = _)’ kall_tac >>
  gvs[] >>
  ‘∀s0 wl0 s wl. R⁺ (s,wl) (s0,wl0) ⇒
                 swfs s0 ∧ wf s0 ∧ swfs s ∧ wf s ∧ sp2fm s0 ⊑ sp2fm s ∧
                 (A (s0,wl0) ⇒ A(s,wl)) ∧
                 substvars (sp2fm s) ∪ plist_vars wl ⊆
                 substvars (sp2fm s0) ∪ plist_vars wl0’
    by (Induct_on ‘TC R’ >> simp[FORALL_PROD] >>
        pop_assum (assume_tac o GSYM) >>
        simp[kuR_def] >> rw[] >~
        [‘_ ⊑ _’] >- metis_tac[SUBMAP_TRANS] >>
        ASM_SET_TAC[]) >>
  ‘∃s wl.
     swfs s ∧ wf s ∧ sp2fm s0 ⊑ sp2fm s ∧ A (s,wl) ∧
     (substvars $ sp2fm s) ∪ plist_vars wl ⊆
     (substvars $ sp2fm s0) ∪ plist_vars wl0 ∧
     ∀s' wl'. TC R (s',wl') (s,wl) ⇒ s' = s’
    by (qpat_x_assum ‘A _’ mp_tac >>
        completeInduct_on
        ‘CARD ((substvars $ sp2fm s0) ∪ plist_vars wl0) -
         CARD (FDOM (sp2fm s0))’ >>
        gvs[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
        rw[] >> gvs[] >>
        reverse $ Cases_on ‘∃s' wl'. TC R (s',wl') (s0,wl0) ∧ s' ≠ s0’ >> gvs[]
        >- (qexistsl [‘s0’, ‘wl0’]>> rw[] >> metis_tac[]) >>
        first_x_assum $ qspecl_then [‘s'’, ‘wl'’] mp_tac >> simp[] >>
        impl_tac
        >- (first_x_assum $ drule_then strip_assume_tac >>
            ‘CARD (domain s0) ≤
               CARD (substvars (sp2fm s0) ∪ plist_vars wl0)’
                  by (irule CARD_SUBSET >> simp[substvars_def] >> SET_TAC[]) >>
            ‘domain s0 ⊂ domain s'’
              by (simp[PSUBSET_DEF] >>
                  qpat_x_assum ‘_ ⊑ _’ mp_tac >>
                  simp[SUBMAP_FLOOKUP_EQN] >> strip_tac >>
                  ‘domain s0 ⊆ domain s'’
                    by (simp[SUBSET_DEF] >>
                        metis_tac[domain_lookup]) >> simp[] >>
                  strip_tac >> qpat_x_assum ‘s' ≠ s0’ mp_tac >>
                  gvs[spt_eq_thm] >> pop_assum mp_tac >>
                  simp[EXTENSION,domain_lookup]>>
                  metis_tac[SOME_11,option_CASES]) >>
            simp[DECIDE “x ≤ y ⇒ (0 < y - x ⇔ x < y)”,
                 DECIDE “a ≤ x ⇒ (y < b + x - a ⇔ a + y < b + x)”] >>
            conj_tac
            >- (irule (DECIDE “x < y ∧ a ≤ b ⇒ x + a < y + b”) >> conj_tac
                >- (irule CARD_PSUBSET >> simp[]) >>
                irule CARD_SUBSET >> simp[]) >>
            irule CARD_PSUBSET >> simp[] >>
            irule PSUBSET_SUBSET_TRANS >> first_assum $ irule_at Any >>
            gs[substvars_def] >> ASM_SET_TAC[]) >>
        strip_tac >> first_x_assum $ drule_then strip_assume_tac >>
        gvs[] >> rename [‘R⁺ _ (s,wl) ⇒ _ = s’] >>
        qexistsl [‘s’, ‘wl’] >> simp[] >> rw[] >~
        [‘_ ⊑ _’] >- metis_tac[SUBMAP_TRANS] >>
        ((qmatch_abbrev_tac ‘_ ⊆ _’ >> ASM_SET_TAC[]) ORELSE metis_tac[])) >>
  qabbrev_tac
    ‘M = (measure (λ(t1,t2).
                     pair_count (sp2fm s ◁ t1) + pair_count (sp2fm s ◁ t2)))’ >>
  ‘∀s' wl'.
     R⁺ (s',wl') (s,wl) ⇒
     mlt M (BAG_OF_LIST wl') (BAG_OF_LIST wl)’
    by (Induct_on ‘TC R’ using TC_STRONG_INDUCT_LEFT1 >>
        simp[GSYM RIGHT_FORALL_IMP_THM, FORALL_PROD] >>
        rw[]
        >- (rename [‘R (s',wl') (s,wl)’] >>
            ‘R⁺ (s',wl') (s,wl)’ by simp[TC_SUBSET] >>
            ‘s' = s’ by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
            irule TC_SUBSET >> qpat_x_assum ‘R _ _’ mp_tac >>
            first_x_assum (assume_tac o GSYM o
                           assert (is_eq o #2 o strip_forall o concl) o
                           assert (is_forall o concl)
                          ) >>
            simp[kuR_def]) >>
        irule TC_LEFT1_I >> first_assum $ irule_at Any >>
        rename [‘TC R (s1,wl1) (s,wl)’, ‘R (s2,wl2) (s1,wl1)’]>>
        ‘s1 = s ∧ s2 = s’ by metis_tac[TC_RULES] >>
        ntac 2 $ pop_assum SUBST_ALL_TAC >>
        qpat_x_assum ‘R _ _’ mp_tac >>
        first_x_assum (assume_tac o GSYM o
                       assert (is_eq o #2 o strip_forall o concl) o
                       assert (is_forall o concl)) >>
        simp[kuR_def]) >>
  qabbrev_tac ‘rwlbs (* "reachable wl bags" *) =
               λrwlb. ∃rwl. R⁺ (s,rwl) (s,wl) ∧ rwlb = BAG_OF_LIST rwl’ >>
  ‘WF (mlt M)’ by simp[WF_TC_EQN, bagTheory.WF_mlt1, Abbr‘M’] >>
  drule_then (assume_tac o SRULE[PULL_EXISTS]) (iffLR WF_DEF) >>
  ‘∀wl'. R꙳(s,wl') (s,wl) ⇒ ∃wl''. R(s,wl'') (s,wl')’
    by (simp[cj 1 (GSYM TC_RC_EQNS), RC_DEF, DISJ_IMP_THM, FORALL_AND_THM] >>
        metis_tac[TC_RULES]) >>
  ‘∃b. rwlbs b’ by (simp[Abbr‘rwlbs’] >> irule_at Any TC_SUBSET >>
                    metis_tac[TC_RULES]) >>
  first_assum (pop_assum o
               mp_then Any (qx_choose_then ‘minwlb’ strip_assume_tac)) >>
  gvs[Abbr‘rwlbs’, PULL_FORALL] >> rename [‘R⁺ (s,minwl) (s,wl)’] >>
  ‘∃cwl. R(s,cwl)(s,minwl)’ by metis_tac[TC_RTC] >>
  ‘R⁺ (s,cwl)(s,wl)’ by metis_tac[TC_LEFT1_I] >>
  first_x_assum (pop_assum o mp_then Concl mp_tac) >>
  pop_assum mp_tac >>
  first_x_assum (assume_tac o GSYM o
                       assert (is_eq o #2 o strip_forall o concl) o
                       assert (is_forall o concl)) >>
  simp[kuR_def, TC_SUBSET]
QED

Theorem vwalk_rangevars:
  wfs s ∧ vwalk s v = t ⇒
  t = Var v ∧ v ∉ FDOM s ∨ vars t ⊆ rangevars s
Proof
  Cases_on ‘wfs s’ >> simp[] >> map_every qid_spec_tac [‘t’, ‘v’] >>
  ho_match_mp_tac vwalk_ind >> rw[] >>
  ONCE_REWRITE_TAC[UNDISCH vwalk_def] >> Cases_on ‘FLOOKUP s v’ >>
  simp[AllCaseEqs()] >> gs[FLOOKUP_DEF] >> rename [‘s ' v = t’] >>
  Cases_on ‘t’ >> simp[]
  >- (gs[] >> simp[rangevars_def, PULL_EXISTS, FRANGE_DEF] >>
      first_assum $ irule_at Any >> simp[]) >>
  simp[rangevars_def, PULL_EXISTS, FRANGE_DEF, SUBSET_DEF] >> rw[] >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem walk_rangevars:
  wfs s ∧ walk s t = u ⇒
  vars u ⊆ rangevars s ∪ vars t
Proof
  Cases_on ‘t’ >> simp[walk_thm] >> rw[] >> simp[]
  >- (drule vwalk_rangevars >> simp[] >> rename [‘vwalk s vn’] >>
      disch_then $ qspec_then ‘vn’ strip_assume_tac >> simp[] >>
      ASM_SET_TAC[]) >>
  SET_TAC[]
QED

Theorem ucode_reduces_at_callsite:
  ∀s k y. swfs s ∧ wf s ∧ ucode (s,k) = INL y ⇒ kuR y (s,k)
Proof
  simp[FORALL_PROD,ucode_def] >> rpt strip_tac >>
  gs[AllCaseEqs(), PULL_EXISTS] >> rw[] >>
  simp[kuR_def, mlt1_BAG_INSERT, wf_insert] >>~-
      ([‘twalk s u1 = Var v’, ‘twalk s u2 = Pair t1 t2’],
       gvs[GSYM twalk_correct, swalk_def, GSYM disj_oc, soc_def] >>
       gvs[swfs_def, oc_eq_vars_walkstar]>>
       ‘∃un. u1 = Var un ∧ v ∉ FDOM (sp2fm s)’ by metis_tac[walk_to_var] >>
       gs[] >> rw[]
       >- (irule wfs_extend >> simp[])
       >- (simp[substvars_def] >> drule_all vwalk_rangevars >> simp[] >>
           strip_tac >> gvs[rangevars_FUPDATE] >> drule_all walk_rangevars >>
           simp[] >> SET_TAC[])
       >- SET_TAC[]) >>~-
      ([‘twalk s u1 = Var v’, ‘twalk s u2 = Const cn’],
       gvs[GSYM twalk_correct, swalk_def] >> gvs[swfs_def] >>
       ‘∃un. u1 = Var un ∧ v ∉ FDOM (sp2fm s)’ by metis_tac[walk_to_var] >>
       gs[] >> rw[]
       >- (irule wfs_extend >> simp[])
       >- (simp[substvars_def, rangevars_FUPDATE] >>
           drule_all_then strip_assume_tac vwalk_rangevars >> gvs[] >>
           SET_TAC[])
       >- SET_TAC[]) >~
  [‘twalk s t1 = Var v1’, ‘twalk s t2 = Var v2’, ‘v1 ≠ v2’]
  >- (gvs[GSYM twalk_correct, swalk_def] >> gvs[swfs_def]>>
      ‘∃u1 u2. t1 = Var u1 ∧ t2 = Var u2 ∧ v1 ∉ FDOM (sp2fm s) ∧
               v2 ∉ FDOM (sp2fm s)’
        by metis_tac[walk_to_var] >> gvs[] >>
      rw[]
      >- (irule wfs_extend >> simp[NOT_FDOM_vwalk])
      >- (simp[substvars_def] >>
          qpat_assum ‘wfs (sp2fm s)’
                     (mp_then Any assume_tac vwalk_rangevars) >>
          pop_assum (rpt o dxrule_then strip_assume_tac) >>
          gvs[rangevars_FUPDATE] >> SET_TAC[])
      >- SET_TAC[]) >~
  [‘twalk s u1 = Const cn’]
  >- SET_TAC[] >~
  [‘twalk s t1 = Var _’]
  >- SET_TAC[] >~
  [‘vars t1 ∪ vars t2 ∪ _’, ‘plist_vars wl’,
   ‘twalk s t1 = Pair a1 a2’, ‘twalk s t2 = Pair b1 b2’]
  >- (gvs[GSYM twalk_correct, swalk_def] >> gvs[swfs_def]>>
      simp[substvars_def] >>
      qpat_assum ‘wfs (sp2fm s)’ (mp_then Any assume_tac walk_rangevars) >>
      rpt conj_tac >~
      [‘mlt1 _ _ _ ’]
      >- (simp[bagTheory.mlt1_def] >>
          qexistsl [‘(t1,t2)’, ‘{|(a1,b1); (a2,b2)|}’, ‘BAG_OF_LIST wl’] >>
          simp[bagTheory.BAG_UNION_INSERT, DISJ_IMP_THM, FORALL_AND_THM] >>
          conj_tac >> irule (DECIDE “a < u1 ∧ b < u2 ⇒ a + b < u1 + u2”) >>
          metis_tac[walkstar_subterm_smaller]) >>
      pop_assum (rpt o dxrule) >> simp[] >> SET_TAC[])
QED

Theorem ucode_preserves_guard:
  wf σ ∧ swfs σ ∧ ucode (σ,k) = INL (σ',k') ⇒ wf σ' ∧ swfs σ'
Proof
  simp[AllCaseEqs(), ucode_def] >> rw[] >> simp[] >>
  gvs[GSYM twalk_correct, GSYM disj_oc] >>
  gvs[swfs_def, wf_insert, swalk_def] >>
  irule wfs_extend >> simp[] >> rpt conj_tac >>~-
  ([‘n ∉ domain s’],
   drule walk_to_var >> disch_then (rpt o dxrule_all) >> simp[]) >~
  [‘vwalk (sp2fm s) nm’]
  >- (‘vwalk (sp2fm s) nm = Var nm’ suffices_by simp[] >>
      irule NOT_FDOM_vwalk >> simp[] >>
      drule walk_to_var >> disch_then (rpt o dxrule_all) >> simp[]) >>
  gs[GSYM oc_eq_vars_walkstar, soc_def]
QED

Theorem kunify_cleaned:
  ∀x. (λ(s,k). swfs s ∧ wf s) x ⇒
      (λ(s,k). kunifywl s k) x = trec ucode x
Proof
  match_mp_tac (GEN_ALL TAILREC_GUARD_ELIMINATION_SIMPLER) >>
  qexists ‘kuR’ >> rpt conj_tac
  >- simp[WF_kuR]
  >- (simp[FORALL_PROD] >> metis_tac[ucode_preserves_guard])
  >- (simp[FORALL_PROD] >> metis_tac[ucode_reduces_at_callsite])
  >- simp[kunifywl_tcallish]
QED

Definition tunifywl_def:
  tunifywl s wl = trec ucode (s,wl)
End

Theorem tunifywl_thm =
        tunifywl_def |> SRULE[TAILREC_TAILCALL, ucode_def]
                     |> SRULE[TAILCALL_def, sum_CASE_list_CASE,
                              sum_CASE_term_CASE, sum_CASE_COND,
                              sum_CASE_pair_CASE]
                     |> SRULE[GSYM tunifywl_def, GSYM ucode_def]

Theorem tunifywl_correct =
        kunify_cleaned
          |> SRULE [GSYM tunifywl_def, FORALL_PROD, kunifywl_def]
          |> Q.SPECL [‘s’, ‘[(t1,t2)]’]
          |> SRULE[GSYM abs_EQ_apply_unifkont, dfkunify_def, kunify_def,
                   cwc_def]
          |> SRULE[apply_unifkont_thm, sunify_def]
          |> Q.INST [‘s’ |-> ‘fm2sp σ’]
          |> SRULE[swfs_def]
          |> UNDISCH
          |> Q.AP_TERM ‘OPTION_MAP sp2fm’
          |> SRULE[OPTION_MAP_COMPOSE, combinTheory.o_DEF]
          |> DISCH_ALL

Theorem option_CASE_MAP:
  option_CASE (OPTION_MAP f x) n sf =
  option_CASE x n (sf o f)
Proof
  Cases_on ‘x’ >> simp[]
QED

Theorem option_CASE_term_CASE:
  option_CASE (term_CASE t vf pf cf) n sf =
  term_CASE t (λv. option_CASE (vf v) n sf)
            (λt1 t2. option_CASE (pf t1 t2) n sf)
            (λc. option_CASE (cf c) n sf)
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem option_CASE_COND:
  option_CASE (COND g t e) n sf =
  COND g (option_CASE t n sf) (option_CASE e n sf)
Proof
  Cases_on ‘g’ >> simp[]
QED

Theorem tunifywl_NIL:
  tunifywl σ [] = SOME σ
Proof
  simp[Once tunifywl_thm]
QED

Theorem twalk_to_var:
  swfs s ∧ wf s ∧ twalk s t = Var v ⇒ v ∉ domain s ∧ ∃u. t = Var u
Proof
  simp[swfs_def, GSYM twalk_correct, SF CONJ_ss] >>
  simp[swalk_def] >> strip_tac >> drule_all walk_to_var >>
  simp[]
QED

Theorem substvars_FUPDATE:
  substvars (fm |+ (v,t)) = substvars (fm \\ v) ∪ {v} ∪ vars t
Proof
  simp[substvars_def, rangevars_def] >> SET_TAC[]
QED

Theorem ucode_EQ_INR:
  ucode (σ, k) = INR y ⇒
  k = [] ∧ y = SOME σ ∨
  ∃t1 t2 s. k = (t1,t2)::s ∧ y = NONE ∧
            ∀s'. ucode(σ,(t1,t2)::s') = INR NONE
Proof
  simp[SimpL “$==>”, ucode_def, AllCaseEqs()] >>
  simp[PULL_EXISTS] >> rw[] >>
  simp[ucode_def]
QED

Theorem ucode_EQ_INL:
  ucode (σ,k) = INL x ⇒
  ∃t1 t2 rest σ' p'.
    k = (t1,t2) :: rest ∧
    x = (σ',p' ++ rest) ∧
    ∀rest'. ucode (σ, (t1,t2) :: rest') =
            INL (σ', p' ++ rest')
Proof
  simp[SimpL “$==>”, ucode_def, AllCaseEqs()] >>
  simp[PULL_EXISTS] >> rw[] >>
  simp[ucode_def]
QED

Theorem tunifywl_APPEND:
  ∀sts σ pfx sfx.
    wf σ ∧ swfs σ ∧ sts = (σ,pfx ++ sfx) ⇒
    tunifywl σ (pfx ++ sfx) =
    OPTION_BIND (tunifywl σ pfx) (λσ'. tunifywl σ' sfx)
Proof
  assume_tac WF_kuR >>
  dxrule_then (ho_match_mp_tac o SRULE[RIGHT_FORALL_IMP_THM])
              WF_INDUCTION_THM >>
  rw[] >> Cases_on ‘pfx’ >> simp[tunifywl_NIL] >>
  rename [‘tunifywl σ (h::(p ++ sfx))’] >>
  ‘∃t1 t2. h = (t1,t2)’ by metis_tac[pair_CASES] >> gvs[] >>
  simp[SimpLHS, Once tunifywl_def] >>
  simp[TAILREC_TAILCALL] >>
  simp[SimpRHS, Once tunifywl_def] >>
  simp[TAILREC_TAILCALL] >>
  simp[TAILCALL_def] >>
  simp[AllCaseEqs()] >>
  reverse $ Cases_on ‘ucode (σ,(t1,t2)::(p ++ sfx))’
  >- (simp[] >> drule ucode_EQ_INR >> simp[]) >>
  simp[] >> drule ucode_EQ_INL >> simp[PULL_EXISTS] >> rw[] >>
  simp[GSYM tunifywl_def] >>
  drule_all_then assume_tac ucode_reduces_at_callsite >>
  first_x_assum irule >> simp[] >>
  drule_all_then strip_assume_tac ucode_preserves_guard >>
  simp[]
QED




val _ = export_theory();
