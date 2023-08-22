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

(* INL is dfkoc; INR = apply_ockont *)
Definition jointoc_def:
  jointoc v (s, INL (t,k)) = dfkoc s t v k /\
  jointoc v (s, INR (k,b)) = apply_ockont s v k b
End

Theorem jointoc_thm = jointoc_def |> SPEC_ALL |> SRULE [Once dfkoc_thm]
                                  |> SRULE [GSYM jointoc_def]

val oc_code = rand “
               tcall (K F)
          [
            INR ((λ(_,s). case s of INR (k,b) => b | _ => F),
                 (λ(_,s). case s of INR (k,b) => b));
            INR ((λ(_,s). ISR s /\ FST (OUTR s) = ocIDk),
                 (λ(_,s). SND (OUTR s)));
            INL (ISL o SND,
                 (λ(s,sm).
                    case sm of
                      INL (t,k) =>
                        (case walk_alt s t of
                           Var n => (s,INR (k,v = n))
                         | Pair t1 t2 => (s, INL (t1,ock1 t2 k))
                         | Const cn => (s, INR (k,F)))));
            INL (ISR o SND,
                 (λ(s,sm). case sm of
                           | INR (ock1 t k, b) => (s,INL (t,k))));
          ]

”

Theorem jointoc_tcallish:
  !x.
    (λ(s,sm). wfs s) x ==>
    jointoc v x =
    tcall (K F) ^oc_code (jointoc v) x
Proof
  simp[FUN_EQ_THM, sumTheory.FORALL_SUM, FORALL_PROD] >>
  rw[jointoc_def]
  >- (rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >>
      simp[jointoc_def] >> simp[Once dfkoc_thm]) >>
  rename [‘apply_ockont s v k b’] >> Cases_on ‘k’ >>
  simp[apply_ockont_thm, jointoc_def]
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
  inv_image (pair$RPROD (=) (mlt1 (walkstarR s)) LEX $<)
            (λ(s,sm). ((s,BAG_OF_SUM sm : α term bag),if ISR sm then 1 else 0))
End

Theorem WF_ocR:
  wfs s ==> WF (ocR s)
Proof
  strip_tac >> simp[ocR_def] >>
  irule relationTheory.WF_inv_image >>
  irule WF_LEX >> simp[] >>
  irule relationTheory.WF_SUBSET >>
  simp[FORALL_PROD] >>
  qexists ‘inv_image (mlt1 (walkstarR s)) SND’ >>
  simp[walkstar_thWF, bagTheory.WF_mlt1, relationTheory.WF_inv_image,
       PAIR_REL]
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


Theorem jointoc_cleaned0:
  !x. (λ(s,sm). wfs s) x ==> jointoc v x = trec (K F) ^oc_code x
Proof
  match_mp_tac guard_elimination >> rpt conj_tac
  >- (simp[FORALL_PROD, sumTheory.FORALL_SUM] >> rw[]
      >- (rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >> simp[]) >>
      rename [‘k <> ocIDk’] >> Cases_on ‘k’ >> gs[])
  >- (simp[FORALL_PROD] >> rw[] >>
      rename [‘wfs th’] >>
      qexists ‘ocR th’ >> simp[] >> conj_tac
      >- (irule $ iffLR relationTheory.WF_EQ_WFP >> simp[WF_ocR]) >>
      simp[sumTheory.FORALL_SUM, FORALL_PROD] >> rw[]
      >- (rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >>
          simp[ocR_def, ocklist_def, PAIR_REL,
               LEX_DEF, mlt1_BAG_INSERT] >>
          simp[bagTheory.mlt1_def] >>
          rename [‘walk_alt s t = Pair t1 t2’] >>
          qexistsl [‘t’, ‘{| t1; t2 |}’] >>
          simp[bagTheory.BAG_UNION_INSERT] >>
          simp[DISJ_IMP_THM, FORALL_AND_THM] >>
          gs[GSYM walk_alt_correct] >>
          dxrule_then strip_assume_tac RTC_ocR_preserves_subst >>
          metis_tac[walkstar_th1, walkstar_th2]) >>
      rename [‘k <> ocIDk’] >> Cases_on ‘k’ >> gvs[] >>
      simp[ocR_def, ocklist_def, LEX_DEF]) >>
  simp[sumTheory.FORALL_SUM, FORALL_PROD, jointoc_def] >>
  rw[]
  >- (rename [‘walk_alt s t’] >> Cases_on ‘walk_alt s t’ >>
      simp[jointoc_def] >> simp[Once dfkoc_thm]) >>
  rename [‘k <> ocIDk’] >> Cases_on ‘k’ >>
  simp[apply_ockont_thm, jointoc_def]
QED

Definition dfkoc_alt_def:
  dfkoc_alt s v t k = trec (K F) ^oc_code (s, INL (t,k))
End

Definition apply_kont'_def:
  apply_kont' s v k b = trec (K F) ^oc_code (s, INR (k, b))
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

(* CV-translatable:
     refers to itself, walk_alt and apply_kont'
     apply_kont' refers to dfkoc_alt only
*)
Theorem dfkoc_alt_thm =
        dfkoc_alt_def |> SRULE[Once trec_thm, tcall_EQN]
                      |> SRULE [trec_term_case]
                      |> SRULE[GSYM dfkoc_alt_def, GSYM apply_kont'_def]

Theorem apply_kont'_thm:
  apply_kont' s v ocIDk b = b /\
  apply_kont' s v (ock1 t k) b = if b then T
                                 else dfkoc_alt s v t k
Proof
  simp[apply_kont'_def] >> ONCE_REWRITE_TAC[trec_thm] >>
  simp[tcall_EQN, GSYM dfkoc_alt_def]
QED

Theorem dfkoc_alt_oc:
  wfs s ==> oc s t v = dfkoc_alt s v t ocIDk
Proof
  simp[dfkoc_alt_def, GSYM jointoc_cleaned0, jointoc_def, dfkoc_def,
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
  wfs s ==> (oc s t1 v \/ oc s t2 v <=> dfkoc_alt s v t1 (ock1 t2 ocIDk))
Proof
  simp[dfkoc_alt_def, GSYM jointoc_cleaned0, jointoc_def, dfkoc_def,
       koc_def, cwc_def, apply_ockont_def]
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



(*
Theorem dfkunify_alt_unify:
  wfs s ==> unify s t1 t2 = dfkunify_alt apply_unifkont s t1 t2 unifIDk
Proof
  simp[GSYM dfkunify_alt_correct, dfkunify_def, kunify_def, cwc_def,
       apply_unifkont_def]
QED
*)

val _ = export_theory();
