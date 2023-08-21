open HolKernel Parse boolLib bossLib;

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


(* CV-translatable *)
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

Definition core_dfkwalkstar_def:
  core_dfkwalkstar s t0 k0 =
  WHILE (λ(t, k). ispair t)
        (λ(t, k). let (t1,t2) = destpair t
                  in
                    (walk_alt s t1, kwc2 t2 k))
        (t0, k0)
End

(* CV-translatable *)
Theorem core_dfkwalkstar_thm:
  core_dfkwalkstar s t0 k0 =
  case t0 of
    Const cn => (t0, k0)
  | Var n => (t0, k0)
  | Pair t1 t2 => core_dfkwalkstar s (walk_alt s t1) (kwc2 t2 k0)
Proof
  simp[SimpLHS, Once whileTheory.WHILE, core_dfkwalkstar_def] >>
  Cases_on ‘t0’ >> simp[core_dfkwalkstar_def]
QED

(* CV-translatable *)
Definition dfkwalkstar_alt_def:
  dfkwalkstar_alt s t0 k0 =
  let t1 = walk_alt s t0 ;
      (t, k) = core_dfkwalkstar s t1 k0
  in
    apply_kw s k t
End

Theorem dfkwalkstar_alt_correct:
  wfs s ⇒ dfkwalkstar s t k = dfkwalkstar_alt s t k
Proof
  strip_tac >> map_every qid_spec_tac [‘k’, ‘t’] >>
  ho_match_mp_tac walkstar_ind >> rpt strip_tac >>
  simp[dfkwalkstar_alt_def] >> Cases_on ‘walk_alt s t’ >>
  simp[Once dfkwalkstar_thm, Once core_dfkwalkstar_thm] >>
  gvs[walk_alt_correct] >> simp[dfkwalkstar_alt_def]
QED

Theorem dfkwalkstar_alt_walkstar:
  wfs s ⇒ walk* s t = dfkwalkstar_alt s t kwcID
Proof
  simp[GSYM dfkwalkstar_alt_correct, dfkwalkstar_def, kwalkstar_def, cwc_def,
       apply_kw_thm]
QED

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

Definition core_oc_def:
  core_oc s t k =
  WHILE (λ(t,k). ispair t)
        (λ(t,k). let (t1, t2) = destpair t in
                   (walk_alt s t1, ock1 t2 k))
        (t, k)
End

(* CV-translatable *)
Theorem core_oc_thm:
  core_oc s t k =
  case t of
    Pair t1 t2 => core_oc s (walk_alt s t1) (ock1 t2 k)
  | _ => (t, k)
Proof
  simp[SimpLHS, core_oc_def, Once whileTheory.WHILE] >>
  Cases_on ‘t’ >> simp[core_oc_def]
QED

(* CV-translatable *)
Definition dfkoc_alt_def:
  dfkoc_alt s t0 v k0 =
  let t1 = walk_alt s t0 ;
      (t, k) = core_oc s t1 k0 ;
  in
    case t of
      Var u => apply_ockont s v k (v = u)
    | Const _ => apply_ockont s v k F
    | Pair _ _ => F
End

Theorem dfkoc_alt_correct:
  wfs s ==> !t v k. dfkoc s t v k = dfkoc_alt s t v k
Proof
  strip_tac >>
  ho_match_mp_tac walkstar_ind >> rw[] >>
  gvs[walk_alt_correct] >> simp[dfkoc_alt_def] >>
  Cases_on ‘walk_alt s t’ >> gvs[] >>
  simp[Once dfkoc_thm, Once core_oc_thm] >>
  simp[dfkoc_alt_def]
QED

Theorem dfkoc_alt_oc:
  wfs s ==> oc s t v = dfkoc_alt s t v ocIDk
Proof
  simp[GSYM dfkoc_alt_correct, dfkoc_def, koc_def, apply_ockont_def, cwc_def]
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
  wfs s ==> (oc s t1 v \/ oc s t2 v <=> dfkoc_alt s t1 v (ock1 t2 ocIDk))
Proof
  simp[GSYM dfkoc_alt_correct, dfkoc_def, koc_def, cwc_def, apply_ockont_def]
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
  dfkunify A (s:α subst) t1 t2 k = kunify s t1 t2 (A k)
End

Theorem apply_unifkont_thm =
        SRULE [GSYM dfkunify_def, SF ETA_ss] apply_unifkont_def


Theorem apply_unifkont_NONE:
  apply_unifkont k NONE = NONE
Proof
  Cases_on ‘k’ >> simp[apply_unifkont_def]
QED

Theorem abs_EQ_apply_unifkont:
  (λov. case ov of NONE => NONE | SOME s => dfkunify apply_unifkont s t1 t2 k) =
  apply_unifkont (unifk1 t1 t2 k)
Proof
  simp[FUN_EQ_THM, apply_unifkont_def, optionTheory.FORALL_OPTION, SF ETA_ss] >>
  simp[dfkunify_def]
QED

Theorem dfkunify_thm =
        dfkunify_def
          |> Q.ISPEC ‘apply_unifkont’
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE [kunify_thm]
          |> SRULE[GSYM dfkunify_def, apply_unifkont_NONE,
                   abs_EQ_apply_unifkont]

Definition core_dfkunify_def:
  core_dfkunify s t1 t2 k =
  WHILE (λ(t1,t2,k). ispair t1 /\ ispair t2)
        (λ(t1,t2,k).
           let (t11,t12) = destpair t1 ;
               (t21,t22) = destpair t2 ;
           in
             (walk_alt s t11,walk_alt s t21,unifk1 t12 t22 k))
        (t1,t2,k)
End

(* CV-translatable *)
Theorem core_dfkunify_thm:
  core_dfkunify s t1 t2 k =
  case (t1,t2) of
    (Pair t11 t12, Pair t21 t22) =>
      core_dfkunify s (walk_alt s t11) (walk_alt s t21) (unifk1 t12 t22 k)
  | _ => (t1,t2,k)
Proof
  simp[SimpLHS, core_dfkunify_def, Once whileTheory.WHILE] >>
  map_every Cases_on [‘t1’, ‘t2’] >> simp[] >>
  simp[core_dfkunify_def]
QED

(* CV-translatable, once apply_unifkont is as well *)
Definition dfkunify_alt_def:
  dfkunify_alt A s t10 t20 k0 =
  let t1 = walk_alt s t10 ; t2 = walk_alt s t20 ;
      (T1,T2,k) = core_dfkunify s t1 t2 k0
  in
    case (T1,T2) of
      (Var v1, Var v2) => if v1 = v2 then A k (SOME s)
                          else A k (SOME (s |+ (v1,Var v2)))
    | (Var v1, Const c2) => A k (SOME (s |+ (v1, Const c2)))
    | (Var v1, Pair t1 t2) =>
        if dfkoc_alt s t1 v1 (ock1 t2 ocIDk) then NONE
        else A k (SOME (s |+ (v1, Pair t1 t2)))
    | (Const c1, Var v2) => A k (SOME (s |+ (v2, Const c1)))
    | (Const c1, Pair t1 t2) => NONE
    | (Const c1, Const c2) => if c1 = c2 then A k (SOME s)
                              else NONE
    | (Pair t1 t2, Var v2) =>
        if dfkoc_alt s t1 v2 (ock1 t2 ocIDk) then NONE
        else A k (SOME (s |+ (v2, Pair t1 t2)))
    | (Pair _ _, Pair _ _) => NONE
    | (Pair t1 t2, Const c2) => NONE
End

Theorem dfkunify_alt_correct:
  !s t1 t2 A k.
    wfs s ==>
    dfkunify apply_unifkont s t1 t2 k = dfkunify_alt apply_unifkont s t1 t2 k
Proof
  recInduct unify_ind >> rw[] >> gvs[walk_alt_correct] >>
  simp[dfkunify_alt_def] >>
  map_every Cases_on [‘walk_alt s t1’, ‘walk_alt s t2’] >> gvs[] >>
  simp[Once dfkunify_thm, Once core_dfkunify_thm] >>
  simp[dfkunify_alt_def]
QED

Theorem dfkunify_alt_unify:
  wfs s ==> unify s t1 t2 = dfkunify_alt apply_unifkont s t1 t2 unifIDk
Proof
  simp[GSYM dfkunify_alt_correct, dfkunify_def, kunify_def, cwc_def,
       apply_unifkont_def]
QED
(*
Definition apply_unifkont'_def:
  apply_unifkont' unifIDk x = x /\
  apply_unifkont' (unifk1 t1 t2 k) NONE = NONE /\
  apply_unifkont' (unifk1 t1 t2 k) (SOME s) = dfkunify_alt s t1 t2 k
End

Theorem apply_unifkont'_rwt:
  wfs s ==> apply_unifkont k (SOME s) = apply_unifkont' k (SOME s)
Proof
  Cases_on ‘k’ >>
  simp[apply_unifkont'_def, apply_unifkont_thm, dfkunify_alt_correct]
QED

Theorem dfkunify_alt_thm = SRULE[apply_unifkont'_rwt] dfkunify_alt_def
*)


val _ = export_theory();
