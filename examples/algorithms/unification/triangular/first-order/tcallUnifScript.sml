open HolKernel Parse boolLib bossLib;

open pairTheory
open walkTheory walkstarTheory unifDefTheory
open tailcallsTheory
open substTheory
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

Definition corevwalk_def:
  corevwalk s v =
        WHILE (λv. case FLOOKUP s v of
                               | SOME (Var u) => T
                               | _ => F)
                          (λv. case THE (FLOOKUP s v) of
                                 Var u => u
                               | _ => v)
                          v
End

(* CV-translatable *)
Theorem corevwalk_thm:
  corevwalk s v =
  case FLOOKUP s v of
  | SOME (Var u) => corevwalk s u
  | _ => v
Proof
  simp[SimpLHS, corevwalk_def, Once whileTheory.WHILE] >>
  Cases_on ‘FLOOKUP s v’ >> simp[] >> rename [‘FLOOKUP s v = SOME t’] >>
  Cases_on ‘t’ >> simp[corevwalk_def]
QED

(* CV-translatable *)
Definition vwalk_alt_def:
  vwalk_alt s v =
  let u = corevwalk s v
  in
    case FLOOKUP s u of
      NONE => Var u
    | SOME t => t
End

Theorem vwalk_alt_thm:
  wfs s ⇒ vwalk s v = vwalk_alt s v
Proof
  simp[wfs_def, vwalk_alt_def] >> strip_tac >> qid_spec_tac ‘v’ >>
  first_assum (ho_match_mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
  rpt strip_tac >> ONCE_REWRITE_TAC[corevwalk_thm] >>
  Cases_on ‘FLOOKUP s v’ >> simp[] >> gvs[GSYM wfs_def]
  >- simp[Once vwalk_def] >>
  rename [‘term_CASE t’] >> Cases_on ‘t’ >> simp[]
  >- (simp[Once vwalk_def] >> first_x_assum irule >> simp[vR_def]) >>
  simp[Once vwalk_def]
QED

(* CV-translatable *)
Definition walk_alt_def:
  walk_alt s t = case t of Var v => vwalk_alt s v
                            | u => u
End

Theorem walk_alt_correct:
  wfs s ⇒ walk s t = walk_alt s t
Proof
  simp[vwalk_alt_thm, walk_def, walk_alt_def]
QED

Theorem walk_alt_correctD = UNDISCH_ALL walk_alt_correct

Theorem contify_term_case:
  contify k (term_CASE t v p c) =
  contify (λt. case t of Var n => contify k (v n)
                      | Pair t1 t2 => contify k (p t1 t2)
                      | Const cn => contify k (c cn))
          t
Proof
  Cases_on ‘t’ >> simp[contify_def]
QED

Definition kwalkstar_def:
  kwalkstar (s:α subst) t k = cwc (walkstar s t) k
End

Theorem kwalkstar_thm =
        kwalkstar_def
          |> SPEC_ALL
          |> SRULE [Once walkstar_def, ASSUME “wfs (s:'a subst)”,
                    GSYM contify_cwc]
          |> CONV_RULE (TOP_DEPTH_CONV (contify_CONV[contify_term_case]))
          |> SRULE [cwcp “term$Pair”, cwcp “term$Pair x0”, cwcp “walk*”,
                    cwcp “walk”]
          |> SRULE [GSYM kwalkstar_def]
          |> SRULE [cwc_def, walk_alt_correctD]

Datatype:
  kwcon = kwcID | kwc1 ('a term) kwcon | kwc2 ('a term) kwcon
End

Definition apply_kw_def:
  apply_kw s kwcID t = t ∧
  apply_kw s (kwc1 t1 k) t2 = apply_kw s k (Pair t1 t2) ∧
  apply_kw s (kwc2 t2 k) t1 = kwalkstar s t2 (λxk2. apply_kw s k (Pair t1 xk2))
End

Definition dfkwalkstar_def:
  dfkwalkstar s t k = kwalkstar s t (apply_kw s k)
End


(* CV-translatable if dfkwalkstar is, which it isn't *)
Theorem apply_kw_thm =
        SRULE [GSYM dfkwalkstar_def] $
              LIST_CONJ [cj 1 apply_kw_def,
                         cj 2 apply_kw_def,
                         SRULE [GSYM $ cj 2 apply_kw_def, SF ETA_ss]
                               (cj 3 apply_kw_def)]

Theorem dfkwalkstar_thm =
        dfkwalkstar_def
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE [kwalkstar_thm]
          |> SRULE[GSYM apply_kw_thm, SF ETA_ss, GSYM dfkwalkstar_def]

Definition koc_def:
  koc (s:α subst) t v k = cwc (oc s t v) k
End

Theorem disj2cond[local] = DECIDE “p ∨ q ⇔ if p then T else q”
Theorem koc_thm =
        koc_def
          |> SPEC_ALL
          |> SRULE [Once oc_walking, ASSUME “wfs (s:'a subst)”,
                    GSYM contify_cwc]
          |> REWRITE_RULE[disj2cond]
          |> CONV_RULE (TOP_DEPTH_CONV (contify_CONV[contify_term_case]))
          |> SRULE [cwcp “term$Pair”, cwcp “term$Pair x0”, cwcp “walk*”,
                    cwcp “walk”, cwcp “$=”, cwcp “(\/)”, cwcp “oc”,
                    cwcp “oc s”]
          |> SRULE [GSYM koc_def]
          |> SRULE [cwc_def, walk_alt_correctD]

(* isomorphic to a list of terms *)
Datatype: ockont = ocIDk | ock1 ('a term) ockont
End

Definition apply_ockont_def:
  apply_ockont s v ocIDk b = b /\
  apply_ockont s v (ock1 t k) b =
  if b then T
  else koc s t v (λb. apply_ockont s v k b)
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
  dfkoc s t v k = apply_ockont s v (ock1 t k) F
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

Definition ocwl_def: ocwl s v k = ocwl0 s v k F
End

Theorem ocwl0_varcheck: ocwl0 s v k b = if b then T else ocwl s v k
Proof
  rw[ocwl_def] >> Cases_on ‘b’ >> simp[]
QED

Theorem ocwl_thm =
        ocwl0_thm |> SRULE[GSYM ocwl_def]
                  |> SRULE[ocwl0_varcheck]
                  |> SRULE[FORALL_BOOL]
                  |> PURE_REWRITE_RULE [DECIDE “~p = (p = F)”,
                                        DECIDE “p \/ q <=> if p then T else q”]

val oc_code = rand “
               tcall (K F)
          [
            (I,
             K T,
             (λ(s,k). case k of
                    ocIDk => INR F
                  | ock1 t k =>
                      case walk_alt s t of
                        Var n => if v = n then INR T else INL (s,k)
                      | Pair t1 t2 => INL (s, ock1 t1 (ock1 t2 k))
                      | Const _ => INL (s,k)))
          ]
”

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

Theorem ocwl_tcallish:
  !x.
    (λ(s,sm). wfs s) x ==>
    (λ(s,k). ocwl s v k) x =
    tcall (K F) ^oc_code (λ(s,k). ocwl s v k) x
Proof
  simp[FUN_EQ_THM, sumTheory.FORALL_SUM, FORALL_PROD,
      patternMatchesTheory.PMATCH_ROW_def,
      patternMatchesTheory.PMATCH_ROW_COND_def
      ] >>
  rpt gen_tac >> rename [‘ocwl s v k ⇔ _’] >> Cases_on ‘k’ >>
  simp[sum_CASE_term_CASE, sum_CASE_COND]
  >- simp[ocwl_thm] >>
  simp[SimpLHS, Once ocwl_thm]
QED

Definition ocklist_def:
  ocklist ocIDk = [] /\
  ocklist (ock1 t k) = t::ocklist k
End

Overload BAG_OF_LIST = “FOLDR BAG_INSERT EMPTY_BAG”

Theorem FINITE_BAG_OF_LIST[simp]:
  FINITE_BAG (BAG_OF_LIST l)
Proof
  Induct_on ‘l’ >> simp[]
QED


Definition BAG_OF_SUM[simp]:
  BAG_OF_SUM (INL (t,k)) = BAG_OF_LIST (t :: ocklist k) /\
  BAG_OF_SUM (INR (k,b)) = BAG_OF_LIST (ocklist k)
End

Definition ocR_def:
  ocR (s:α subst) =
  inv_image (pair$RPROD (=) (mlt1 (walkstarR s)))
            (λ(s:α subst,k:α ockont). (s, BAG_OF_LIST (ocklist k)))
End

Theorem WF_ocR:
  wfs s ==> WF (ocR s)
Proof
  strip_tac >> simp[ocR_def] >>
  irule relationTheory.WF_inv_image >>
  irule relationTheory.WF_SUBSET >>
  simp[FORALL_PROD] >>
  qexists ‘inv_image (mlt1 (walkstarR s)) SND’ >>
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
  !x. (λ(s,sm). wfs s) x ==> (λ(s,k). ocwl s v k) x = trec (K F) ^oc_code x
Proof
  match_mp_tac guard_elimination >> rpt conj_tac
  >- (simp[FORALL_PROD, sumTheory.FORALL_SUM] >>
      rw[patternMatchesTheory.PMATCH_ROW_def,
         patternMatchesTheory.PMATCH_ROW_COND_def] >>
      rename [‘ockont_CASE k’]>>
      Cases_on ‘k’ >> gvs[sum_CASE_term_CASE, sum_CASE_COND] >>
      rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >> gvs[])
  >- (simp[FORALL_PROD] >> rw[] >>
      rename [‘wfs th’] >>
      qexists ‘ocR th’ >> simp[] >> conj_tac
      >- (irule $ iffLR relationTheory.WF_EQ_WFP >> simp[WF_ocR]) >>
      simp[sumTheory.FORALL_SUM, FORALL_PROD,
           patternMatchesTheory.PMATCH_ROW_COND_def,
           patternMatchesTheory.PMATCH_ROW_def] >>
      rpt gen_tac >> rename [‘ockont_CASE k’] >> Cases_on ‘k’ >>
      simp[sum_CASE_term_CASE, sum_CASE_COND] >>
      rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >> simp[] >>
      strip_tac >>
      simp[ocR_def, ocklist_def, PAIR_REL, LEX_DEF, mlt1_BAG_INSERT] >>
      simp[bagTheory.mlt1_def] >>
      rename [‘walk_alt s t = Pair t1 t2’] >>
      qexistsl [‘t’, ‘{| t1; t2 |}’] >>
      simp[bagTheory.BAG_UNION_INSERT] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      gs[GSYM walk_alt_correct] >>
      dxrule_then strip_assume_tac RTC_ocR_preserves_subst >>
      metis_tac[walkstar_th1, walkstar_th2]) >>
  MATCH_ACCEPT_TAC ocwl_tcallish
QED

Definition ocwl'_def:
  ocwl' s v k = trec (K F) ^oc_code (s, k)
End

Theorem trec_term_case:
  trec e opts (term_CASE t vf pf cf) =
  case t of
    Var v => trec e opts (vf v)
  | Pair t1 t2 => trec e opts (pf t1 t2)
  | Const cn => trec e opts (cf cn)
Proof
  Cases_on ‘t’ >> simp[]
QED

Theorem sum_CASE_ockont_CASE:
  sum_CASE (ockont_CASE k i tkf) lf rf =
  ockont_CASE k (sum_CASE i lf rf)
              (λt k. sum_CASE (tkf t k) lf rf)
Proof
  Cases_on ‘k’ >> simp[]
QED

(* CV-translatable:
     refers to itself, walk_alt and apply_kont'
     apply_kont' refers to dfkoc_alt only
*)
Theorem ocwl'_thm =
        ocwl'_def |> SRULE[Once trec_thm, tcall_EQN]
                  |> SRULE [patternMatchesTheory.PMATCH_ROW_def,
                            patternMatchesTheory.PMATCH_ROW_COND_def,
                            sum_CASE_ockont_CASE, sum_CASE_term_CASE,
                            sum_CASE_COND]
                  |> SRULE[GSYM ocwl'_def]

Theorem ocwl'_alt_oc:
  wfs s ==> oc s t v = ocwl' s v (ock1 t ocIDk)
Proof
  simp[ocwl'_def, GSYM ocwl_cleaned0, apply_ockont_def, ocwl_def,
       koc_def, apply_ockont_def, cwc_def]
QED

Theorem contify_optbind:
  contify k (OPTION_BIND opt f) =
  contify (λov. case ov of
                  NONE => k NONE
                | SOME x => contify k (f x))
          opt
Proof
  Cases_on ‘opt’ >> simp[contify_def]
QED

Definition kunify_def:
  kunify (s:α subst) t1 t2 k = cwc (unify s t1 t2) k
End

Theorem disj_oc:
  wfs s ==> (oc s t1 v \/ oc s t2 v <=> ocwl' s v (ock1 t1 (ock1 t2 ocIDk)))
Proof
  simp[ocwl'_def, GSYM ocwl_cleaned0, ocwl_def, apply_ockont_def,
       koc_def, cwc_def]
QED

Theorem kunify_thm =
        kunify_def
          |> SPEC_ALL
          |> SRULE [Once unify_def, GSYM contify_cwc, ASSUME “wfs (s:α subst)”]
          |> CONV_RULE (TOP_DEPTH_CONV (contify_CONV[contify_term_case,
                                                     contify_option_case,
                                                     contify_pair_case,
                                                     contify_optbind]))
          |> SRULE [cwcp “term$Pair”, cwcp “term$Pair x0”,
                    cwcp “walk”, cwcp “$|+”, cwcp “$,”, cwcp “unify”,
                    cwcp “unify s”, cwcp “Const”,
                    cwcp “$, x”, cwcp “$=”, cwcp “oc”, cwcp “oc s”]
          |> SRULE [GSYM kunify_def]
          |> SRULE [cwc_def, walk_alt_correctD, UNDISCH_ALL disj_oc]

Datatype: unifkont = unifIDk | unifk1 (α term) (α term) unifkont
End

Definition apply_unifkont_def:
  apply_unifkont unifIDk x = x /\
  apply_unifkont (unifk1 t1 t2 k) NONE = NONE /\
  apply_unifkont (unifk1 t1 t2 k) (SOME s) = kunify s t1 t2 (apply_unifkont k)
End

Definition dfkunify_def:
  dfkunify (s:α subst) t1 t2 k = kunify s t1 t2 (apply_unifkont k)
End

Theorem apply_unifkont_thm =
        SRULE [GSYM dfkunify_def, SF ETA_ss] apply_unifkont_def


Theorem apply_unifkont_NONE:
  apply_unifkont k NONE = NONE
Proof
  Cases_on ‘k’ >> simp[apply_unifkont_def]
QED

Theorem abs_EQ_apply_unifkont:
  (λov. case ov of NONE => NONE | SOME s => dfkunify s t1 t2 k) =
  apply_unifkont (unifk1 t1 t2 k)
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
Definition unifywl_def:
  unifywl k s = unifywl0 k (SOME s)
End

Theorem unifywl0_NIL = Q.INST [‘x’ |-> ‘SOME s’] $ cj 1 unifywl0

Theorem unifywl_thm =
        REWRITE_RULE [GSYM unifywl_def] (CONJ unifywl0_NIL $ cj 3 unifywl0)

val _ = export_theory();
