Theory Program
Ancestors list arithmetic CBPV_Mutual_Recursive

(* --------------------------------
    Encoding CBPV Terms as Programs
   -------------------------------- *)

Datatype:
  Tok = varT num | appT | lamT | endLamT | retT | endRetT |
  forceT | thunkT | endThunkT | seqT | endSeqT | letinT | endLetinT |
  pseqT | endPseqT
End

Type Pro = ``:Tok list``;

(* compilation function : Ter → Pro
    translates CBPV terms into programs: *)
Definition compileVal_def:
  (compileVal (var x) = [varT x]) ∧
  (compileVal (thunk m) = thunkT::compileComp m ++ [endThunkT]) ∧
  (compileComp (force v) = compileVal v ++ [forceT]) ∧
  (compileComp (ret v) = retT ::compileVal v ++ [endRetT]) ∧
  (compileComp (lam m) = lamT::compileComp m ++ [endLamT]) ∧
  (compileComp (app m v) = compileComp m ++ compileVal v ++ [appT]) ∧
  (compileComp (seq m n) = compileComp m ++ [seqT] ++ compileComp n ++ [endSeqT]) ∧
  (compileComp (pseq m2 m1 n) = compileComp m1 ++ compileComp m2 ++ [pseqT] ++ compileComp n ++ [endPseqT]) ∧
  (compileComp (letin v m) = compileVal v ++ [letinT] ++ compileComp m ++ [endLetinT])
End

Theorem compile_not_empty:
  (∀v. compileVal v ≠ []) ∧
  ∀s. compileComp s ≠ []
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[compileVal_def]
QED

val t1 = ``force (thunk (app (lam (ret (var 0))) (var 1)))``
val compile_t1 = EVAL ``compile ^t1``;

Definition sizeT:
  sizeT t =
  case t of
  | varT n => 1 + n
  | _ => 1
End

Definition sizeP:
  sizeP P = SUM (MAP sizeT P) + 1
End

Theorem size_geq_1:
  (∀s. 1≤ sizeVal s) ∧
  (∀s. 1≤ sizeComp s)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[] >>
  rw[Once sizeVal_def]
QED

Theorem sizeP_geq_1:
  ∀p. 1 ≤ sizeP p
Proof
  rw[sizeP]
QED

Theorem sizeP_size':
  (∀s. sizeVal s ≤ SUM (MAP sizeT (compileVal s))) ∧
  (∀s. sizeComp s ≤ SUM (MAP sizeT (compileComp s)))
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >>
  rw[] (* 8 *) >> rw[Once sizeVal_def, sizeT, compileVal_def, SUM_APPEND]
QED


Theorem sizeP_size:
  (∀s. SUM (MAP sizeT (compileVal s)) + 1 ≤ 2*sizeVal s) ∧
  (∀s. SUM (MAP sizeT (compileComp s)) + 1 ≤ 2*sizeComp s)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >>
  rw[] (* 8 *) >> rw[Once sizeVal_def, sizeT, compileVal_def, SUM_APPEND]
QED

Theorem sizeP_size_n:
  ∀n. 2 ≤ n ⇒
      (∀s. SUM (MAP sizeT (compileVal s)) + 1 ≤ n*sizeVal s) ∧
      (∀s. SUM (MAP sizeT (compileComp s)) + 1 ≤ n*sizeComp s)
Proof
  ntac 2 strip_tac >> rw[]
  >- (qspec_then ‘s’ assume_tac $ cj 1 sizeP_size >>
      ‘2*sizeVal s ≤ n*sizeVal s’ suffices_by intLib.COOPER_TAC >> rw[])
  >> qspec_then ‘s’ assume_tac $ cj 2 sizeP_size >> rw[] >>
  ‘2*sizeComp s ≤ n*sizeComp s’ suffices_by intLib.COOPER_TAC >> rw[]
QED

(* extracts the body of an abstraction *)
Definition jumpTarget:
  jumpTarget k res P =
  case P of
  | endLamT :: P => (case k of
                     | 0 => SOME (res, P)
                     | SUC k => jumpTarget k (res++[endLamT]) P)
  | lamT :: P => jumpTarget (SUC k) (res++[lamT]) P
  | t :: P => jumpTarget k (res++[t]) P
  | [] => NONE
End

Theorem jumpTarget_correct':
  (∀s k l res. jumpTarget k res (compileVal s ++ l) = jumpTarget k (res++compileVal s) l) ∧
  (∀s k l res. jumpTarget k res (compileComp s ++ l) = jumpTarget k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpTarget])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpTarget] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpTarget] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpTarget] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpTarget] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpTarget] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpTarget] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpTarget_correct:
  (∀s c. jumpTarget 0 [] (compileVal s ++ endLamT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpTarget 0 [] (compileComp s ++ endLamT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpTarget 0 ([]++compileVal s) (endLamT::c)`
        by rw[jumpTarget] >> metis_tac[jumpTarget_correct'])
  >> `SOME (compileComp s, c) = jumpTarget 0 ([]++compileComp s) (endLamT::c)`
    by rw[jumpTarget] >> metis_tac[jumpTarget_correct']
QED

Theorem jumpTarget_correct_conc:
  (∀s c. jumpTarget 0 [] (compileVal s ++ [endLamT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpTarget 0 [] (compileComp s ++ [endLamT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpTarget 0 [] (compileVal s ++ endLamT::c) = SOME (compileVal s, c)`
        by rw[jumpTarget_correct] >>
      `compileVal s ⧺ [endLamT] ⧺ c = compileVal  s ⧺ endLamT::c`
        suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpTarget 0 [] (compileComp s ++ endLamT::c) = SOME (compileComp s, c)`
    by rw[jumpTarget_correct] >>
  `compileComp s ⧺ [endLamT] ⧺ c = compileComp  s ⧺ endLamT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

Theorem jumpTarget_eq':
  ∀k c c0 c1 c2.
  jumpTarget k c0 c = SOME (c1,c2)
  ⇒ c1++[endLamT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpTarget]
  >> pop_assum mp_tac >>
  rw[Once jumpTarget] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpTarget_eq:
  ∀c c0 c1 c2.
  jumpTarget 0 c0 c = SOME (c1,c2)
  ⇒ c1++[endLamT]++c2=c0++c
Proof
  metis_tac[jumpTarget_eq']
QED

(* extracts the second argument of a seq *)
Definition jumpSeq:
  jumpSeq k res P =
  case P of
  | endSeqT :: P => (case k of
                     | 0 => SOME (res, P)
                     | SUC k => jumpSeq k (res++[endSeqT]) P)
  | seqT :: P => jumpSeq (SUC k) (res++[seqT]) P
  | t :: P => jumpSeq k (res++[t]) P
  | [] => NONE
End

Theorem jumpSeq_correct':
  (∀s k l res. jumpSeq k res (compileVal s ++ l) = jumpSeq k (res++compileVal s) l) ∧
  (∀s k l res. jumpSeq k res (compileComp s ++ l) = jumpSeq k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpSeq])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpSeq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpSeq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpSeq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpSeq] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpSeq] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpSeq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpSeq_correct:
  (∀s c. jumpSeq 0 [] (compileVal s ++ endSeqT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpSeq 0 [] (compileComp s ++ endSeqT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpSeq 0 ([]++compileVal s) (endSeqT::c)`
        by rw[jumpSeq] >> metis_tac[jumpSeq_correct'])
  >> `SOME (compileComp s, c) = jumpSeq 0 ([]++compileComp s) (endSeqT::c)`
    by rw[jumpSeq] >> metis_tac[jumpSeq_correct']
QED

Theorem jumpSeq_correct_conc:
  (∀s c. jumpSeq 0 [] (compileVal s ++ [endSeqT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpSeq 0 [] (compileComp s ++ [endSeqT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpSeq 0 [] (compileVal s ++ endSeqT::c) = SOME (compileVal s, c)`
        by rw[jumpSeq_correct] >>
      `compileVal s ⧺ [endSeqT] ⧺ c = compileVal  s ⧺ endSeqT::c`
        suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpSeq 0 [] (compileComp s ++ endSeqT::c) = SOME (compileComp s, c)`
    by rw[jumpSeq_correct] >>
  `compileComp s ⧺ [endSeqT] ⧺ c = compileComp  s ⧺ endSeqT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED


Theorem jumpSeq_eq':
  ∀k c c0 c1 c2.
  jumpSeq k c0 c = SOME (c1,c2)
  ⇒ c1++[endSeqT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpSeq]
  >> pop_assum mp_tac >>
  rw[Once jumpSeq] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpSeq_eq:
  ∀c c0 c1 c2.
  jumpSeq 0 c0 c = SOME (c1,c2)
  ⇒ c1++[endSeqT]++c2=c0++c
Proof
  metis_tac[jumpSeq_eq']
QED

(* extracts the second argument of a pseq *)
Definition jumpPseq:
  jumpPseq k res P =
    case P of
      | endPseqT :: P => (case k of
                       | 0 => SOME (res, P)
                       | SUC k => jumpPseq k (res++[endPseqT]) P)
      | pseqT :: P => jumpPseq (SUC k) (res++[pseqT]) P
      | t :: P => jumpPseq k (res++[t]) P
      | [] => NONE
End

Theorem jumpPseq_correct':
  (∀s k l res. jumpPseq k res (compileVal s ++ l) = jumpPseq k (res++compileVal s) l) ∧
  (∀s k l res. jumpPseq k res (compileComp s ++ l) = jumpPseq k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpPseq])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpPseq] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpPseq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpPseq] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
  rw[Once jumpPseq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpPseq] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpPseq] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpPseq] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpPseq_correct:
  (∀s c. jumpPseq 0 [] (compileVal s ++ endPseqT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpPseq 0 [] (compileComp s ++ endPseqT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpPseq 0 ([]++compileVal s) (endPseqT::c)`
        by rw[jumpPseq] >> metis_tac[jumpPseq_correct'])
  >> `SOME (compileComp s, c) = jumpPseq 0 ([]++compileComp s) (endPseqT::c)`
        by rw[jumpPseq] >> metis_tac[jumpPseq_correct']
QED

Theorem jumpPseq_correct_conc:
  (∀s c. jumpPseq 0 [] (compileVal s ++ [endPseqT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpPseq 0 [] (compileComp s ++ [endPseqT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpPseq 0 [] (compileVal s ++ endPseqT::c) = SOME (compileVal s, c)`
          by rw[jumpPseq_correct] >>
      `compileVal s ⧺ [endPseqT] ⧺ c = compileVal  s ⧺ endPseqT::c`
          suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpPseq 0 [] (compileComp s ++ endPseqT::c) = SOME (compileComp s, c)`
    by rw[jumpPseq_correct] >>
  `compileComp s ⧺ [endPseqT] ⧺ c = compileComp  s ⧺ endPseqT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED


Theorem jumpPseq_eq':
  ∀k c c0 c1 c2.
    jumpPseq k c0 c = SOME (c1,c2)
    ⇒ c1++[endPseqT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpPseq]
  >> pop_assum mp_tac >>
  rw[Once jumpPseq] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpPseq_eq:
  ∀c c0 c1 c2.
    jumpPseq 0 c0 c = SOME (c1,c2)
    ⇒ c1++[endPseqT]++c2=c0++c
Proof
  metis_tac[jumpPseq_eq']
QED

(* extracts the second argument of a letin *)
Definition jumpLetin:
  jumpLetin k res P =
  case P of
  | endLetinT :: P => (case k of
                       | 0 => SOME (res, P)
                       | SUC k => jumpLetin k (res++[endLetinT]) P)
  | letinT :: P => jumpLetin (SUC k) (res++[letinT]) P
  | t :: P => jumpLetin k (res++[t]) P
  | [] => NONE
End

Theorem jumpLetin_correct':
  (∀s k l res. jumpLetin k res (compileVal s ++ l) = jumpLetin k (res++compileVal s) l) ∧
  (∀s k l res. jumpLetin k res (compileComp s ++ l) = jumpLetin k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpLetin])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpLetin] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpLetin] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpLetin] >> metis_tac[GSYM APPEND_ASSOC, rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpLetin] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpLetin] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpLetin] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpLetin_correct:
  (∀s c. jumpLetin 0 [] (compileVal s ++ endLetinT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpLetin 0 [] (compileComp s ++ endLetinT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpLetin 0 ([]++compileVal s) (endLetinT::c)`
        by rw[jumpLetin] >> metis_tac[jumpLetin_correct'])
  >> `SOME (compileComp s, c) = jumpLetin 0 ([]++compileComp s) (endLetinT::c)`
    by rw[jumpLetin] >> metis_tac[jumpLetin_correct']
QED

Theorem jumpLetin_correct_conc:
  (∀s c. jumpLetin 0 [] (compileVal s ++ [endLetinT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpLetin 0 [] (compileComp s ++ [endLetinT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpLetin 0 [] (compileVal s ++ endLetinT::c) = SOME (compileVal s, c)`
        by rw[jumpLetin_correct] >>
      `compileVal s ⧺ [endLetinT] ⧺ c = compileVal  s ⧺ endLetinT::c`
        suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpLetin 0 [] (compileComp s ++ endLetinT::c) = SOME (compileComp s, c)`
    by rw[jumpLetin_correct] >>
  `compileComp s ⧺ [endLetinT] ⧺ c = compileComp  s ⧺ endLetinT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

Theorem jumpLetin_eq':
  ∀k c c0 c1 c2.
  jumpLetin k c0 c = SOME (c1,c2)
  ⇒ c1++[endLetinT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpLetin]
  >> pop_assum mp_tac >>
  rw[Once jumpLetin] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpLetin_eq:
  ∀c c0 c1 c2.
  jumpLetin 0 c0 c = SOME (c1,c2)
  ⇒ c1++[endLetinT]++c2=c0++c
Proof
  metis_tac[jumpLetin_eq']
QED

(* extracts the body of a thunk *)
Definition jumpThunk:
  jumpThunk l res P =
  case P of
  | endThunkT :: P => (case l of
                       | 0 => SOME (res, P)
                       | SUC l => jumpThunk l (res++[endThunkT]) P)
  | thunkT :: P => jumpThunk (SUC l) (res++[thunkT]) P
  | t :: P => jumpThunk l (res++[t]) P
  | [] => NONE
End

Theorem jumpThunk_correct':
  (∀s k l res. jumpThunk k res (compileVal s ++ l) = jumpThunk k (res++compileVal s) l) ∧
  (∀s k l res. jumpThunk k res (compileComp s ++ l) = jumpThunk k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  (* var *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpThunk])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpThunk] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpThunk] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpThunk] >> metis_tac[GSYM APPEND_ASSOC, rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpThunk] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpThunk] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpThunk] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpThunk_correct:
  (∀s c. jumpThunk 0 [] (compileVal s ++ endThunkT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpThunk 0 [] (compileComp s ++ endThunkT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpThunk 0 ([]++compileVal s) (endThunkT::c)`
        by rw[jumpThunk] >> metis_tac[jumpThunk_correct'])
  >> `SOME (compileComp s, c) = jumpThunk 0 ([]++compileComp s) (endThunkT::c)`
    by rw[jumpThunk] >> metis_tac[jumpThunk_correct']
QED

Theorem jumpThunk_correct_conc:
  (∀s c. jumpThunk 0 [] (compileVal s ++ [endThunkT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpThunk 0 [] (compileComp s ++ [endThunkT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpThunk 0 [] (compileVal s ++ endThunkT::c) = SOME (compileVal s, c)`
        by rw[jumpThunk_correct] >>
      `compileVal s ⧺ [endThunkT] ⧺ c = compileVal  s ⧺ endThunkT::c`
        suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpThunk 0 [] (compileComp s ++ endThunkT::c) = SOME (compileComp s, c)`
    by rw[jumpThunk_correct] >>
  `compileComp s ⧺ [endThunkT] ⧺ c = compileComp  s ⧺ endThunkT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

Theorem jumpThunk_eq':
  ∀k c c0 c1 c2.
  jumpThunk k c0 c = SOME (c1,c2)
  ⇒ c1++[endThunkT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpThunk]
  >> pop_assum mp_tac >>
  rw[Once jumpThunk] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpThunk_eq:
  ∀c c0 c1 c2.
  jumpThunk 0 c0 c = SOME (c1,c2)
  ⇒ c1++[endThunkT]++c2=c0++c
Proof
  metis_tac[jumpThunk_eq']
QED

(* extracts the body of a thunk *)
Definition jumpRet:
  jumpRet l res P =
  case P of
  | endRetT :: P => (case l of
                     | 0 => SOME (res, P)
                     | SUC l => jumpRet l (res++[endRetT]) P)
  | retT :: P => jumpRet (SUC l) (res++[retT]) P
  | t :: P => jumpRet l (res++[t]) P
  | [] => NONE
End

Theorem jumpRet_correct':
  (∀s k l res. jumpRet k res (compileVal s ++ l) = jumpRet k (res++compileVal s) l) ∧
  (∀s k l res. jumpRet k res (compileComp s ++ l) = jumpRet k (res++compileComp s) l)
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  (* var *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpRet])
  (* thunk *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* force *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet])
  (* lam *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* app *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet])
  (* ret *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* seq *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpRet] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND])
  (* letin *)
  >- (rw[Once compileVal_def] >> rw[Once compileVal_def] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      rw[Once jumpRet] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >>
      rw[Once jumpRet] >> metis_tac[GSYM APPEND_ASSOC, rich_listTheory.CONS_APPEND])
  (* pseq *)
  >> rw[Once compileVal_def] >> rw[Once compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpRet] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  rw[Once jumpRet] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND] >> rw[] >>
  rw[Once jumpRet] >> metis_tac[GSYM APPEND_ASSOC, GSYM rich_listTheory.CONS_APPEND]
QED

Theorem jumpRet_correct:
  (∀s c. jumpRet 0 [] (compileVal s ++ endRetT::c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpRet 0 [] (compileComp s ++ endRetT::c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`SOME (compileVal s, c) = jumpRet 0 ([]++compileVal s) (endRetT::c)`
        by rw[jumpRet] >> metis_tac[jumpRet_correct'])
  >> `SOME (compileComp s, c) = jumpRet 0 ([]++compileComp s) (endRetT::c)`
    by rw[jumpRet] >> metis_tac[jumpRet_correct']
QED

Theorem jumpRet_correct_conc:
  (∀s c. jumpRet 0 [] (compileVal s ++ [endRetT] ++ c) = SOME (compileVal s, c)) ∧
  (∀s c. jumpRet 0 [] (compileComp s ++ [endRetT] ++ c) = SOME (compileComp s, c))
Proof
  rw[]
  >- (`jumpRet 0 [] (compileVal s ++ endRetT::c) = SOME (compileVal s, c)`
        by rw[jumpRet_correct] >>
      `compileVal s ⧺ [endRetT] ⧺ c = compileVal  s ⧺ endRetT::c`
        suffices_by metis_tac[] >>
      rw[rich_listTheory.CONS_APPEND])
  >> `jumpRet 0 [] (compileComp s ++ endRetT::c) = SOME (compileComp s, c)`
    by rw[jumpRet_correct] >>
  `compileComp s ⧺ [endRetT] ⧺ c = compileComp  s ⧺ endRetT::c`
    suffices_by metis_tac[] >>
  rw[rich_listTheory.CONS_APPEND]
QED

Theorem jumpRet_eq':
  ∀k c c0 c1 c2.
  jumpRet k c0 c = SOME (c1,c2)
  ⇒ c1++[endRetT]++c2=c0++c
Proof
  Induct_on `c` >> rw[]
  >- fs[Once jumpRet]
  >> pop_assum mp_tac >>
  rw[Once jumpRet] >> Cases_on `h` >> gs[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule >> rw[])
  >> Cases_on `k` >> gs[] >>
  metis_tac[]
QED

Theorem jumpRet_eq:
  ∀c c0 c1 c2.
  jumpRet 0 c0 c = SOME (c1,c2)
  ⇒ c1++[endRetT]++c2=c0++c
Proof
  metis_tac[jumpRet_eq']
QED

Definition substP:
  substP P k Q =
    case P of
    | [] => []
    | lamT::P => lamT::substP P (SUC k) Q
    | endLamT::P => (endLamT::(case k of
                          | SUC k => substP P k Q
                          | 0 => [ARB]))
    | seqT::P => seqT::substP P (SUC k) Q
    | endSeqT::P => (endSeqT::(case k of
                          | SUC k => substP P k Q
                          | 0 => [ARB]) )
    | pseqT::P => pseqT::substP P (SUC (SUC k)) Q
    | endPseqT::P => (endPseqT::(case k of
                               | SUC (SUC k) => substP P k Q
                               | _ => [ARB]) )
    | letinT::P => letinT::substP P (SUC k) Q
    | endLetinT::P => (endLetinT::(case k of
                          | SUC k => substP P k Q
                          | 0 => [ARB]))
    | varT k'::P => ((if (k'=k) then Q else [varT k'])++substP P k Q)
    | t::P => t::substP P k Q
End

Theorem substP_correct':
  (∀s k c' t.
      substP (compileVal s++c') k (compileVal t)
        = compileVal (substVal s k t)++substP c' k (compileVal t)) ∧
  (∀s k c' t.
      substP (compileComp s++c') k (compileVal t)
        = compileComp (substComp s k t)++substP c' k (compileVal t))
Proof
  ho_match_mp_tac CBPV_Mutual_RecursiveTheory.val_induction >> rw[]
  (* var *)
  >- (rw[Once compileVal_def, substVal_def, Once substP] >>
      rw[Once compileVal_def])
  (* thunk *)
  >- (rw[Once compileVal_def, substVal_def, Once substP] >>
      rw[Once compileVal_def] >>
      first_x_assum (qspecl_then [`k`, `[endThunkT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP])
  (* force *)
  >- (rw[Once compileVal_def, substVal_def] >>
      first_x_assum (qspecl_then [`k`, `[forceT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP, compileVal_def])
  (* lam *)
  >- (rw[Once compileVal_def, substVal_def, Once substP] >>
      first_x_assum (qspecl_then [`SUC k`, `[endLamT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> simp[SimpR ``$=``, Once compileVal_def] >>
      rw[Once substP, compileVal_def])
  (* app *)
  >- (rw[Once compileVal_def, substVal_def] >>
      first_x_assum (qspecl_then [`k`, `[appT] ⧺ c'`, `t`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`k`, `compileVal s' ⧺ [appT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP] >>
      simp[SimpR ``$=``, Once compileVal_def])
  (* ret *)
  >- (rw[Once compileVal_def, substVal_def, Once substP] >>
      first_x_assum (qspecl_then [`k`, `[endRetT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> simp[SimpR ``$=``, Once compileVal_def] >>
      rw[Once substP, compileVal_def])
  (* seq *)
  >- (rw[Once compileVal_def, substVal_def] >>
      first_x_assum (qspecl_then [`SUC k`, `[endSeqT] ⧺ c'`, `t`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`k`, `[seqT] ++ compileComp s' ⧺ [endSeqT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP] >>
      simp[SimpR ``$=``, Once compileVal_def] >> rw[Once substP])
  (* letin *)
  >- (rw[Once compileVal_def, substVal_def] >>
      first_x_assum (qspecl_then [`SUC k`, `[endLetinT] ⧺ c'`, `t`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`k`, `[letinT] ⧺ compileComp s' ⧺ [endLetinT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP] >>
      simp[SimpR ``$=``, Once compileVal_def] >> rw[Once substP])
  (* pseq *)
  >- (rw[Once compileVal_def, substVal_def] >>
      rw[Once compileVal_def, substVal_def] >>
      first_x_assum (qspecl_then [`SUC (SUC k)`, `[endPseqT] ⧺ c'`, `t`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`k`,
                                   `compileComp s ⧺
                                   [pseqT] ⧺ compileComp s'' ⧺
                                   [endPseqT] ⧺ c'`,
                                   `t`] ASSUME_TAC) >>
      first_x_assum (qspecl_then [`k`, `[pseqT] ++ compileComp s'' ⧺ [endPseqT] ⧺ c'`, `t`] ASSUME_TAC) >>
      rw[] >> gs[] >> rw[Once substP] >>
      simp[SimpR ``$=``, Once compileVal_def] >>
      rw[Once substP] >> rw[Once substP])
QED

Theorem substP_correct:
  ∀s k t.
    substP (compileComp s) k (compileVal t) = compileComp (substComp s k t)
Proof
  `∀s k t. substP (compileComp s++[]) k (compileVal t) = compileComp (substComp s k t)++substP [] k (compileVal t)`
    suffices_by (rw[] >> simp[Once substP]) >>
  metis_tac[substP_correct']
QED

Inductive balanced:
  (∀x. balanced [varT x]) ∧
  (∀t. balanced t ⇒ balanced(thunkT::t++[endThunkT])) ∧
  (∀t. balanced t ⇒ balanced(t++[forceT])) ∧
  (∀t. balanced t ⇒ balanced(retT::t++[endRetT])) ∧
  (∀t. balanced t ⇒ balanced(lamT::t++[endLamT])) ∧
  (∀t. balanced t ⇒ balanced(t ++ [appT])) ∧
  (∀s t. balanced s ∧ balanced t ⇒ balanced(s ++ t)) ∧
  (∀t. balanced t ⇒ balanced(seqT::t++[endSeqT])) ∧
  (∀t. balanced t ⇒ balanced(letinT::t++[endLetinT])) ∧
  (∀s t. balanced s ∧ balanced t ⇒ balanced(s ++ [pseqT] ++ t ++ [endPseqT]))
End

Theorem balanced_compileVal:
  (∀v. balanced(compileVal v)) ∧
  (∀c. balanced(compileComp c))
Proof
  Induct >> rw[compileVal_def] >> rw[Once balanced_cases]
  >- metis_tac[balanced_rules]
  >- (disj1_tac >>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      irule_at Any $ iffRL $ cj 1 APPEND_11 >>
      simp[] >>
      rw[Once balanced_cases])
  >- (disj1_tac >>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      irule_at Any $ iffRL $ cj 1 APPEND_11 >>
      simp[] >>
      rw[Once balanced_cases]) >>
  disj2_tac >>
  irule_at Any $ iffRL $ cj 2 APPEND_11 >>
  simp[] >>
  metis_tac[balanced_rules]
QED

Theorem balanced_thunks:
  balanced xs ⇒ LENGTH(FILTER ($= thunkT) xs) = LENGTH(FILTER ($= endThunkT) xs)
Proof
  Induct_on ‘balanced’ >> rw[] >>
  gvs[FILTER_APPEND_DISTRIB]
QED

Theorem balanced_lams:
  balanced xs ⇒ LENGTH(FILTER ($= lamT) xs) = LENGTH(FILTER ($= endLamT) xs)
Proof
  Induct_on ‘balanced’ >> rw[] >>
  gvs[FILTER_APPEND_DISTRIB]
QED

Theorem balanced_letins:
  balanced xs ⇒ LENGTH(FILTER ($= letinT) xs) = LENGTH(FILTER ($= endLetinT) xs)
Proof
  Induct_on ‘balanced’ >> rw[] >>
  gvs[FILTER_APPEND_DISTRIB]
QED

Theorem balanced_pseqs:
  balanced xs ⇒ LENGTH(FILTER ($= pseqT) xs) = LENGTH(FILTER ($= endPseqT) xs)
Proof
  Induct_on ‘balanced’ >> rw[] >>
  gvs[FILTER_APPEND_DISTRIB]
QED

Theorem balanced_seqs:
  balanced xs ⇒ LENGTH(FILTER ($= seqT) xs) = LENGTH(FILTER ($= endSeqT) xs)
Proof
  Induct_on ‘balanced’ >> rw[] >>
  gvs[FILTER_APPEND_DISTRIB]
QED

val isPREFIX_APPEND1 = REWRITE_RULE [SNOC_APPEND] isPREFIX_SNOC_EQ;

Theorem balanced_thunks_prefix:
  ∀xs ys.
  balanced xs ∧ IS_PREFIX xs ys ⇒ LENGTH(FILTER ($= endThunkT) ys) ≤ LENGTH(FILTER ($= thunkT) ys)
Proof
  Induct_on ‘balanced’ >> rw[] >> gvs[isPREFIX_CONSR,isPREFIX_APPEND1,FILTER_APPEND_DISTRIB]
  >- (res_tac >> intLib.COOPER_TAC)
  >- (simp[ADD1])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_thunks >> simp[])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      irule_at Any LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      conj_tac >- (PURE_ONCE_REWRITE_TAC[oneline TAKE_def] >> simp[] >> rw[]) >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_thunks >> simp[])
  >- (imp_res_tac balanced_thunks >> simp[])
QED

Theorem balanced_lams_prefix:
  ∀xs ys.
  balanced xs ∧ IS_PREFIX xs ys ⇒ LENGTH(FILTER ($= endLamT) ys) ≤ LENGTH(FILTER ($= lamT) ys)
Proof
  Induct_on ‘balanced’ >> rw[] >> gvs[isPREFIX_CONSR,isPREFIX_APPEND1,FILTER_APPEND_DISTRIB]
  >- (res_tac >> intLib.COOPER_TAC)
  >- (simp[ADD1])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_lams >> simp[])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      irule_at Any LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      conj_tac >- (PURE_ONCE_REWRITE_TAC[oneline TAKE_def] >> simp[] >> rw[]) >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_lams >> simp[])
  >- (imp_res_tac balanced_lams >> simp[])
QED

Theorem balanced_seqs_prefix:
  ∀xs ys.
  balanced xs ∧ IS_PREFIX xs ys ⇒ LENGTH(FILTER ($= endSeqT) ys) ≤ LENGTH(FILTER ($= seqT) ys)
Proof
  Induct_on ‘balanced’ >> rw[] >> gvs[isPREFIX_CONSR,isPREFIX_APPEND1,FILTER_APPEND_DISTRIB]
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_seqs >> simp[])
  >- (res_tac >> intLib.COOPER_TAC)
  >- (simp[ADD1])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      irule_at Any LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      conj_tac >- (PURE_ONCE_REWRITE_TAC[oneline TAKE_def] >> simp[] >> rw[]) >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_seqs >> simp[])
  >- (imp_res_tac balanced_seqs >> simp[])
QED

Theorem balanced_letins_prefix:
  ∀xs ys.
  balanced xs ∧ IS_PREFIX xs ys ⇒ LENGTH(FILTER ($= endLetinT) ys) ≤ LENGTH(FILTER ($= letinT) ys)
Proof
  Induct_on ‘balanced’ >> rw[] >> gvs[isPREFIX_CONSR,isPREFIX_APPEND1,FILTER_APPEND_DISTRIB]
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_letins >> simp[])
  >- (res_tac >> intLib.COOPER_TAC)
  >- (simp[ADD1])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      irule_at Any LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      conj_tac >- (PURE_ONCE_REWRITE_TAC[oneline TAKE_def] >> simp[] >> rw[]) >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_letins >> simp[])
  >- (imp_res_tac balanced_letins >> simp[])
QED

Theorem balanced_pseqs_prefix:
  ∀xs ys.
    balanced xs ∧ IS_PREFIX xs ys ⇒ LENGTH(FILTER ($= endPseqT) ys) ≤ LENGTH(FILTER ($= pseqT) ys)
Proof
  Induct_on ‘balanced’ >> rw[] >> gvs[isPREFIX_CONSR,isPREFIX_APPEND1,FILTER_APPEND_DISTRIB]
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_pseqs >> simp[])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      irule_at Any LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      conj_tac >- (PURE_ONCE_REWRITE_TAC[oneline TAKE_def] >> simp[] >> rw[]) >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_pseqs >> simp[])
  >- (gvs[rich_listTheory.IS_PREFIX_EQ_TAKE, SF DNF_ss,rich_listTheory.TAKE_APPEND,
          FILTER_APPEND_DISTRIB] >>
      irule LESS_EQ_LESS_EQ_MONO >>
      simp[] >>
      Cases_on ‘n ≤ LENGTH xs’ >> simp[] >>
      simp[TAKE_LENGTH_TOO_LONG] >>
      imp_res_tac balanced_pseqs >> simp[])
QED

Theorem compileVal_append:
  compileVal v = compileVal v' ++ l ⇒ l = []
Proof
  Cases_on ‘v’ >> Cases_on ‘v'’ >> rw[compileVal_def] >>
  Cases_on ‘l’ using SNOC_CASES >> gvs[] >>
  ‘balanced(compileComp c)’ by metis_tac[balanced_compileVal] >>
  gvs[] >>
  drule balanced_thunks_prefix >>
  simp[] >>
  irule_at Any rich_listTheory.IS_PREFIX_APPEND3 >>
  simp[FILTER_APPEND_DISTRIB] >>
  ‘balanced(compileComp c')’ by metis_tac[balanced_compileVal] >>
  imp_res_tac balanced_thunks >>
  simp[]
QED

Theorem compileVal_append_left:
  compileVal v = l ++ compileVal v' ⇒ l = []
Proof
  Cases_on ‘v’ >> Cases_on ‘v'’ >> rw[compileVal_def] >>
  Cases_on ‘l’ >> gvs[] >>
  ‘balanced(compileComp c)’ by metis_tac[balanced_compileVal] >>
  gvs[] >>
  drule balanced_thunks_prefix >>
  simp[] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
  irule_at Any rich_listTheory.IS_PREFIX_APPEND3 >>
  simp[FILTER_APPEND_DISTRIB] >>
  strip_tac >>
  ‘balanced(compileComp c')’ by metis_tac[balanced_compileVal] >>
  imp_res_tac balanced_thunks >>
  gvs[FILTER_APPEND_DISTRIB]
QED

Theorem compileVal_append':
  compileVal v = compileVal v' ++ l ⇔ l = [] ∧ compileVal v = compileVal v'
Proof
  rw[EQ_IMP_THM] >> imp_res_tac compileVal_append
QED

Theorem compileVal_append_left':
  compileVal v = l ++ compileVal v' ⇔ l = [] ∧ compileVal v = compileVal v'
Proof
  rw[EQ_IMP_THM] >> imp_res_tac compileVal_append_left
QED

Theorem compileVal_append2:
  compileVal s ⧺ l = compileVal t ⧺ l' ⇒
  compileVal s = compileVal t ∧ l = l'
Proof
  strip_tac >> gvs[APPEND_EQ_APPEND,compileVal_append']
QED

Theorem compileVal_append2':
  compileVal s ⧺ l = compileVal t ⧺ l' ⇔
  compileVal s = compileVal t ∧ l = l'
Proof
  metis_tac[compileVal_append2]
QED

Theorem compileVal_append_left2:
  l ++ compileVal s = l' ++ compileVal t ⇒
  compileVal s = compileVal t ∧ l = l'
Proof
  strip_tac >> gvs[APPEND_EQ_APPEND,compileVal_append_left']
QED

Theorem compileVal_append_left2':
  l ++ compileVal s = l' ++ compileVal t ⇔
  compileVal s = compileVal t ∧ l = l'
Proof
  metis_tac[compileVal_append_left2]
QED

Theorem comp_induct = val_induction |> SPEC “λx:val. T” |> REWRITE_RULE[]

Theorem compileComp_append_left:
  ∀c c' l . (compileComp c = l ++ compileComp c' ⇒ l = [])
Proof
  Induct_on ‘SUM (MAP sizeT (compileComp c))’ using COMPLETE_INDUCTION >>
  Cases >> strip_tac
  >- (last_x_assum kall_tac >>
      Cases_on ‘c'’ >> rw[compileVal_def,compileVal_append_left'])
  >- (rpt $ pop_assum kall_tac >>
      Cases >> rw[compileVal_def,compileVal_append_left'] >>
      Cases_on ‘l’ >> gvs[] >>
      ‘balanced(compileComp c')’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_lams_prefix >>
      simp[] >>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      irule_at Any rich_listTheory.IS_PREFIX_APPEND3 >>
      simp[FILTER_APPEND_DISTRIB] >>
      strip_tac >>
      ‘balanced(compileComp c)’ by metis_tac[balanced_compileVal] >>
      imp_res_tac balanced_lams >>
      gvs[FILTER_APPEND_DISTRIB])
  >- (rpt BasicProvers.VAR_EQ_TAC >> fs[SF DNF_ss] >>
      qmatch_asmsub_abbrev_tac ‘a1’ >>
      Cases >> simp[compileVal_def,compileVal_append_left'] >>
      rpt strip_tac >>
      imp_res_tac compileVal_append_left2 >>
      gvs[] >>
      first_x_assum irule >>
      first_x_assum $ irule_at $ Pos last >>
      simp[compileVal_def,SUM_APPEND,sizeT])
  >- (rpt $ pop_assum kall_tac >>
      Cases >> rw[compileVal_def,compileVal_append_left'] >>
      Cases_on ‘l’ >> gvs[compileVal_append_left'])
  >- (qmatch_asmsub_abbrev_tac ‘a1’ >>
      ntac 2 $ pop_assum mp_tac >>
      qmatch_asmsub_abbrev_tac ‘a2’ >>
      rpt strip_tac >>
      Cases_on ‘c''’ >> fs[compileVal_def,compileVal_append_left'] >>
      fs[Once APPEND_EQ_APPEND_MID]
      >- (unabbrev_all_tac >>
          first_assum $ drule_at $ Pos last >>
          disch_then(qspec_then ‘SUM (MAP sizeT (compileComp c0))’ mp_tac) >>
          impl_tac
          >- (last_x_assum kall_tac >>
              fs[SUM_APPEND,sizeT] >>
              imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
              fs[SUM_APPEND,sizeT]) >>
          strip_tac >>
          fs[] >>
          first_assum irule >>
          irule_at Any EQ_REFL >>
          irule_at Any EQ_SYM >>
          first_assum $ irule_at $ Any >>
          last_x_assum kall_tac >>
          fs[SUM_APPEND,sizeT] >>
          imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
          fs[SUM_APPEND,sizeT]) >>
      unabbrev_all_tac >>
      rpt $ PRED_ASSUM is_forall kall_tac >>
      ‘balanced(compileComp c0')’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_seqs_prefix >>
      simp[] >>
      rename1 ‘lll ++ _ ++ _’ >>
      disch_then(qspec_then ‘lll’ mp_tac) >>
      PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3,GSYM APPEND_ASSOC] >>
      simp[] >>
      strip_tac >>
      ‘balanced(compileComp c')’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_seqs_prefix >>
      simp[] >>
      rename1 ‘l ++ compileComp ccc ++ _ ++ _’ >>
      disch_then(qspec_then ‘l ++ compileComp ccc’ mp_tac) >>
      impl_tac
      >- (PURE_REWRITE_TAC[GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPENDS] >>
          PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3]) >>
      strip_tac >>
      imp_res_tac balanced_seqs >>
      gvs[FILTER_APPEND_DISTRIB])
  >- (rpt BasicProvers.VAR_EQ_TAC >> fs[SF DNF_ss] >>
      qmatch_asmsub_abbrev_tac ‘a1’ >>
      Cases >> simp[compileVal_def,compileVal_append_left'] >>
      rpt strip_tac >>
      fs[Once APPEND_EQ_APPEND_MID]
      >- (unabbrev_all_tac >>
          first_assum $ drule_at $ Pos last >>
          impl_tac
          >- (last_x_assum kall_tac >>
              fs[SUM_APPEND,sizeT,compileVal_def] >>
              imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
              fs[SUM_APPEND,sizeT]) >>
          strip_tac >> fs[] >>
          gvs[compileVal_append_left']) >>
      unabbrev_all_tac >>
      rpt $ PRED_ASSUM is_forall kall_tac >>
      ‘balanced(compileComp c)’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_letins_prefix >>
      simp[] >>
      rename1 ‘lll ++ _ ++ _’ >>
      disch_then(qspec_then ‘lll’ mp_tac) >>
      PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3,GSYM APPEND_ASSOC] >>
      simp[] >>
      strip_tac >>
      ‘balanced(compileVal v')’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_letins_prefix >>
      simp[] >>
      rename1 ‘l ++ compileVal vvv ++ _ ++ _’ >>
      disch_then(qspec_then ‘l ++ compileVal vvv’ mp_tac) >>
      impl_tac
      >- (PURE_REWRITE_TAC[GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPENDS] >>
          PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3]) >>
      strip_tac >>
      imp_res_tac balanced_letins >>
      gvs[FILTER_APPEND_DISTRIB])
  >- (rpt BasicProvers.VAR_EQ_TAC >> fs[SF DNF_ss] >>
      qmatch_asmsub_abbrev_tac ‘a1’ >>
      Cases >>
      fs[compileVal_def,compileVal_append_left'] >>
      rpt strip_tac >>
      fs[Once APPEND_EQ_APPEND_MID]
      >- (qunabbrev_tac ‘a1’ >>
          first_assum $ drule_at $ Pos last >>
          impl_tac
          >- (last_x_assum kall_tac >>
              fs[SUM_APPEND,sizeT,compileVal_def] >>
              imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
              fs[SUM_APPEND,sizeT]) >>
          strip_tac >>
          fs[] >>
          fs[Once APPEND_EQ_APPEND]
          >- (first_assum $ drule_at $ Pos last >>
              impl_tac
              >- (last_x_assum kall_tac >>
                  fs[SUM_APPEND,sizeT,compileVal_def] >>
                  imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
                  fs[SUM_APPEND,sizeT]) >>
              strip_tac >>
              fs[] >>
              first_x_assum irule >>
              irule_at Any EQ_SYM >>
              first_x_assum $ irule_at $ Pos hd >>
              simp[SUM_APPEND,sizeT]) >>
          first_assum $ drule_at $ Pos last >>
          impl_tac
          >- (last_x_assum kall_tac >>
              fs[SUM_APPEND,sizeT,compileVal_def] >>
              imp_res_tac $ METIS_PROVE [] “xs = ys ⇒ SUM (MAP sizeT xs) = SUM (MAP sizeT ys)” >>
              fs[SUM_APPEND,sizeT]) >>
          strip_tac >> fs[] >>
          first_x_assum irule >>
          first_assum $ irule_at $ Pos last >>
          simp[SUM_APPEND,sizeT]) >>
      unabbrev_all_tac >>
      rpt $ PRED_ASSUM is_forall kall_tac >>
      ‘balanced(compileComp c0 ++ compileComp c')’ by metis_tac[balanced_compileVal,balanced_rules] >>
      gvs[] >>
      drule balanced_pseqs_prefix >>
      simp[] >>
      rename1 ‘l1 ++ l2 ++ [pseqT] ++ _’ >>
      disch_then(qspec_then ‘l1 ++ l2’ mp_tac) >>
      PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3,GSYM APPEND_ASSOC] >>
      simp[] >>
      strip_tac >>
      ‘balanced(compileComp c1')’ by metis_tac[balanced_compileVal] >>
      gvs[] >>
      drule balanced_pseqs_prefix >>
      simp[] >>
      rename1 ‘l4 ++ _ ++ _’ >>
      disch_then(qspec_then ‘l4’ mp_tac) >>
      impl_tac
      >- (PURE_REWRITE_TAC[GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPENDS] >>
          PURE_REWRITE_TAC[rich_listTheory.IS_PREFIX_APPEND3]) >>
      strip_tac >>
      imp_res_tac balanced_pseqs >>
      gvs[FILTER_APPEND_DISTRIB])
QED

Theorem compileComp_append_left':
  l ++ compileComp c = l' ++ compileComp c' ⇒ l = l' ∧ compileComp c = compileComp c'
Proof
  strip_tac >> gvs[APPEND_EQ_APPEND] >>
  imp_res_tac compileComp_append_left
QED

Theorem compileComp_compileVal_append:
  compileComp s ⧺ compileVal v = compileComp t ⧺ compileVal u ⇒
  compileComp s = compileComp t
Proof
  strip_tac >> gvs[APPEND_EQ_APPEND,compileVal_append_left']
QED

Theorem compileVal_injective:
  (∀s t. compileVal s = compileVal t ⇒ s = t) ∧
  (∀s t. compileComp s = compileComp t ⇒ s = t)
Proof
  Induct
  >- (strip_tac >> Cases >> rw[compileVal_def]) >>
  Cases >> rw[compileVal_def] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  imp_res_tac compileVal_append2 >>
  imp_res_tac compileVal_append_left2 >>
  gvs[] >>
  imp_res_tac compileComp_append_left' >>
  gvs[] >>
  imp_res_tac compileComp_append_left' >>
  gvs[]
QED
