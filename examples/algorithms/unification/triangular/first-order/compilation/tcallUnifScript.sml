open HolKernel Parse boolLib bossLib;

open pairTheory
open walkTheory walkstarTheory unifDefTheory
open tailcallsTheory
open substTheory rmfmapTheory
open cpsTheory cpsLib

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
  simp[tcall_def, FORALL_PROD, sum_CASE_term_CASE,
       sum_CASE_COND] >> rw[] >>
  rename [‘svwalk s k = _’] >> Cases_on ‘lookup k s’ >>
  simp[SimpLHS, Once svwalk_thm] >> simp[] >>
  simp[sum_CASE_term_CASE]
QED

Theorem svwalk_cleaned:
  !x. (λ(s,nm). swfs s ∧ wf s) x ==>
      (λ(s,nm). svwalk s nm) x = trec ^svwalk_code x
Proof
  match_mp_tac guard_elimination >> rpt conj_tac
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >> simp[])
  >- (simp[FORALL_PROD, AllCaseEqs(), swfs_def] >> rw[] >>
      rename [‘wfs (sp2fm s)’] >>
      qexists ‘λ(s0,nm0) (s1,nm). s0 = s ∧ s1 = s ∧ vR (sp2fm s) nm0 nm’ >>
      simp[] >> conj_tac
      >- (irule $ iffLR relationTheory.WF_EQ_WFP >>
          irule relationTheory.WF_SUBSET >>
          qexists ‘inv_image (vR $ sp2fm s) SND’ >>
          simp[FORALL_PROD] >>
          simp[relationTheory.WF_inv_image, GSYM wfs_def]) >>
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
          |> SRULE[Once trec_thm, tcall_def, sum_CASE_option_CASE,
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
  simp[tcall_def, FORALL_PROD, sum_CASE_list_CASE, sum_CASE_term_CASE,
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
  irule relationTheory.WF_inv_image >>
  irule relationTheory.WF_SUBSET >>
  simp[FORALL_PROD] >>
  qexists ‘inv_image (mlt1 (walkstarR (sp2fm s))) SND’ >>
  simp[] >>
  irule relationTheory.WF_inv_image >>
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
  match_mp_tac guard_elimination >> rpt conj_tac
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >> simp[])
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >>
      rename [‘swfs th’] >>
      qexists ‘ocR th’ >> simp[] >> conj_tac
      >- (irule $ iffLR relationTheory.WF_EQ_WFP >> simp[WF_ocR]) >>
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
        tocwl_def |> SRULE[trec_thm]
                  |> SRULE[tcall_def, sum_CASE_list_CASE, sum_CASE_term_CASE,
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
  simp[FUN_EQ_THM, apply_unifkont_def, optionTheory.FORALL_OPTION, SF ETA_ss] >>
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

Theorem kunifywl_tcallish:
  !x.
    (λ(s,k). swfs s ∧ wf s) x ==>
    (λ(s,k). kunifywl s k) x =
    tcall ^unify_code (λ(s,k). kunifywl s k) x
Proof
  simp[tcall_def, FORALL_PROD, sum_CASE_list_CASE, sum_CASE_term_CASE,
       sum_CASE_COND, sum_CASE_pair_CASE] >> rw[] >>
  rename [‘kunifywl s k = _’] >> Cases_on ‘k’
  >- (simp[cj 1 kunifywl_thm]) >>
  rename [‘kunifywl s (h::t)’] >> Cases_on ‘h’ >>
  simp[SimpLHS, Once kunifywl_thm] >> simp[]
QED

Definition plist_vars_def[simp]:
  plist_vars A [] = A ∧
  plist_vars A ((t1,t2) :: tps) = plist_vars (A ∪ vars t1 ∪ vars t2) tps
End

Definition kuR_def:
  kuR (s : α term num_map, wl : (α term # α term) list) (s0,wl0) ⇔
    swfs s ∧ sp2fm s0 ⊑ sp2fm s ∧
    plist_vars (substvars $ sp2fm s) wl ⊆
       plist_vars (substvars $ sp2fm s0) wl0 ∧
    mlt1 (measure (λ(t1,t2). pair_count t1 + pair_count t2))
         (BAG_OF_LIST wl)
         (BAG_OF_LIST wl0)
End

(*
Theorem kunify_cleaned:
  ∀x. (λ(s,k). swfs s ∧ wf s) x ⇒
      (λ(s,k). kunifywl s k) x = trec ^unify_code x
Proof
  match_mp_tac guard_elimination >> rpt conj_tac
  >- (simp[FORALL_PROD, AllCaseEqs()] >> rw[] >> simp[] >>
      gvs[GSYM twalk_correct, GSYM disj_oc] >>
      gvs[swfs_def, sptreeTheory.wf_insert, swalk_def] >>
      irule wfs_extend >> simp[] >> rpt conj_tac >>~-
      ([‘n ∉ domain s’],
       drule walk_to_var >> disch_then (rpt o dxrule_all) >> simp[]) >~
      [‘vwalk (sp2fm s) nm’]
      >- (‘vwalk (sp2fm s) nm = Var nm’ suffices_by simp[] >>
          irule NOT_FDOM_vwalk >> simp[] >>
          drule walk_to_var >> disch_then (rpt o dxrule_all) >> simp[]) >>
      gs[GSYM oc_eq_vars_walkstar, soc_def])
  >- (simp[FORALL_PROD] >> rpt strip_tac >> ...)
  >- ...
QED
*)

val _ = export_theory();
