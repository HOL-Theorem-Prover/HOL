open HolKernel Parse boolLib bossLib;

open walkTheory walkstarTheory
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

Definition destvar_def[simp]:
  destvar (Var v) = v
End

Theorem vwalk_characterisation:
  wfs s ⇒
  vwalk s v =
  tcall Var
        [INR ((λv : num. FLOOKUP s v = NONE), Var);
         INR ((λt. ispair t ∨ isconst t) o THE o FLOOKUP s,
              THE o FLOOKUP s);
         INL (K T, destvar o THE o FLOOKUP s)]
        (vwalk s)
        v
Proof
  simp[tcall_def] >> rename [‘FLOOKUP s v’] >>
  Cases_on ‘FLOOKUP s v’ >>
  strip_tac >> simp[]
  >- simp[Once vwalk_def] >>
  rename [‘FLOOKUP s v = SOME t’] >> simp[] >>
  Cases_on ‘t’ >> simp[]
  >- (simp[SimpLHS, Once vwalk_def]) >>
  simp[Once vwalk_def]
QED

Theorem bad_vwalk_guard_eliminated:
  wfs s ⇒
  ∀v.
    K T v ⇒
    vwalk s v =
    trec Var
         [INR ((λv : num. FLOOKUP s v = NONE), Var);
          INR ((λt. ispair t ∨ isconst t) o THE o FLOOKUP s,
               THE o FLOOKUP s);
          INL (K T, destvar o THE o FLOOKUP s)]
         v
Proof
  strip_tac >> MATCH_MP_TAC (Q.GEN ‘R’ guard_elimination) >>
  simp[pairTheory.FORALL_PROD] >> qexists_tac ‘vR s’ >>
  gvs[wfs_def] >> rw[] >> rename [‘FLOOKUP s v = NONE’] >>
  Cases_on ‘FLOOKUP s v’ >> gvs[] >>~-
  ([‘FLOOKUP s v = SOME t’],
   Cases_on ‘t’ >> gvs[] >> simp[vR_def] >>
   gvs[GSYM wfs_def, Once vwalk_def]) >>
  gvs[GSYM wfs_def, Once vwalk_def]
QED

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

Theorem walk_alt_def:
  wfs s ⇒ walk s t = case t of Var v => vwalk_alt s v
                            | u => u
Proof
  simp[vwalk_alt_thm, walk_def]
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
          |> SRULE [cwc_def]

Datatype:
  kwcon = kwcID | kwc1 ('a term) kwcon | kwc2 ('a subst) ('a term) kwcon
End

Definition apply_kw_def:
  apply_kw kwcID t = t ∧
  apply_kw (kwc1 t1 k) t2 = apply_kw k (Pair t1 t2) ∧
  apply_kw (kwc2 s t2 k) t1 = kwalkstar s t2 (λxk2. apply_kw k (Pair t1 xk2))
End

Definition dfkwalkstar_def:
  dfkwalkstar s t k = kwalkstar s t (apply_kw k)
End

Theorem apply_kw_thm =
        SRULE [GSYM dfkwalkstar_def] $
              LIST_CONJ [cj 1 apply_kw_def,
                         cj 2 apply_kw_def,
                         SRULE [GSYM $ cj 2 apply_kw_def, SF ETA_ss]
                               (cj 3 apply_kw_def)]

Theorem dfwalkstar_thm =
        dfkwalkstar_def
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE [kwalkstar_thm]
          |> SRULE[GSYM apply_kw_thm, SF ETA_ss, GSYM dfkwalkstar_def]


val _ = export_theory();
