open HolKernel Parse boolLib bossLib;

open pairTheory
open simpleSexpTheory

val _ = new_theory "sexpcode";

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Definition error_free_def[simp]:
  error_free (SX_NUM n) = T ∧
  error_free (SX_STR s) = T ∧
  error_free (SX_SYM s) = (s ≠ "error") ∧
  error_free (SX_CONS s1 s2) = (error_free s1 ∧ error_free s2)
End

Definition wf_decenc_def:
  wf_decenc (d,e : 'a -> sexp) ⇔
    (∀a s. e a = s ∧ error_free s ⇔ d s = SOME a)
End

Theorem decencs_exist:
  ∃p. wf_decenc p
Proof
  qexists ‘(K NONE, K $ SX_SYM "error")’ >> simp[wf_decenc_def]
QED

val {absrep_id, newty, repabs_pseudo_id, termP, termP_exists, termP_term_REP,
     term_ABS_t, term_ABS_pseudo11, term_REP_t, term_REP_11} =
    newtypeTools.rich_new_type{tyname = "sexpcode",
                               exthm = decencs_exist,
                               ABS = "sexpcode_ABS",
                               REP = "sexpcode_REP"};

Definition encode_def[nocompute]:
  encode sc = SND (^term_REP_t sc)
End

Definition decode_def[nocompute]:
  decode sc = FST (^term_REP_t sc)
End

Definition total_def:
  total sc ⇔ ∀a. error_free (encode sc a)
End

Theorem decode_error[simp]:
  decode sc (SX_SYM "error") = NONE
Proof
  simp[decode_def] >> qspec_then ‘sc’ assume_tac (GEN_ALL termP_term_REP) >>
  Cases_on ‘sexpcode_REP sc’ >> gs[wf_decenc_def] >>
  rename [‘dec (SX_SYM "error") = NONE’] >>
  Cases_on ‘dec (SX_SYM "error")’ >> simp[] >>
  first_x_assum (drule o iffRL) >> simp[]
QED

Theorem decode_EQ_SOME_encode:
  decode sc s = SOME a ⇔ encode sc a = s ∧ error_free s
Proof
  simp[decode_def, encode_def] >>
  qspec_then ‘sc’ assume_tac (GEN_ALL termP_term_REP) >>
  Cases_on ‘sexpcode_REP sc’ >> gs[wf_decenc_def]
QED

Theorem total_decode_EQ_SOME:
  total sc ⇒ (decode sc (encode sc a) = SOME a)
Proof
  metis_tac[total_def, decode_EQ_SOME_encode]
QED

Definition NUM0_def:
  NUM0 = ((λs. case s of SX_NUM n => SOME n | _ => NONE), SX_NUM)
End

Definition NUM_def[nocompute]:
  NUM = sexpcode_ABS NUM0
End

Theorem wf_NUM0:
  wf_decenc NUM0
Proof
  simp[NUM0_def, wf_decenc_def] >> Cases_on ‘s’ >> simp[]
QED

Theorem encode_NUM[simp,compute]:
  encode NUM = SX_NUM
Proof
  simp[encode_def, NUM_def, repabs_pseudo_id, wf_NUM0] >>
  simp[NUM0_def]
QED

Theorem decode_NUM[simp,compute]:
  decode NUM (SX_NUM n) = SOME n
Proof
  simp[decode_def, NUM_def, repabs_pseudo_id, wf_NUM0] >>
  simp[NUM0_def]
QED

Theorem total_NUM[simp]:
  total NUM
Proof
  simp[total_def]
QED

Definition STRING0_def[nocompute]:
  STRING0 = ((λs. case s of SX_STR s0 => SOME s0 | _ => NONE), SX_STR)
End

Theorem wf_STRING0:
  wf_decenc STRING0
Proof
  simp[wf_decenc_def, STRING0_def] >> Cases_on ‘s’ >> simp[EQ_SYM_EQ]
QED

Definition STRING_def:
  STRING = sexpcode_ABS STRING0
End

Theorem STRING_THM[simp]:
  encode STRING s = SX_STR s ∧
  decode STRING (SX_NUM n) = NONE ∧
  decode STRING (SX_SYM s) = NONE ∧
  decode STRING (SX_CONS s1 s2) = NONE ∧
  decode STRING (SX_STR s) = SOME s
Proof
  simp[STRING_def, encode_def, decode_def, repabs_pseudo_id, wf_STRING0] >>
  simp[STRING0_def]
QED

Theorem total_STRING[simp]:
  total STRING
Proof
  simp[total_def]
QED

Definition LIST0_def[nocompute]:
  LIST0 sc = ((λs. OPTION_BIND (strip_sxcons s) (OPT_MMAP (decode sc))),
              FOLDR (λa. SX_CONS (encode sc a)) nil)
End

Theorem wf_LIST0:
  wf_decenc (LIST0 sc)
Proof
  simp[wf_decenc_def, LIST0_def] >>
  Induct_on ‘a’ >> simp[SF CONJ_ss, AllCaseEqs()]
  >- (Cases_on ‘s’ >> simp[PULL_EXISTS]) >>
  qx_gen_tac ‘h’ >> Cases_on ‘s’ >> simp[PULL_EXISTS, SF CONJ_ss] >>
  eq_tac >> rpt strip_tac >> gs[decode_EQ_SOME_encode] >>
  metis_tac[]
QED

Definition LIST_def[nocompute]:
  LIST sc = sexpcode_ABS (LIST0 sc)
End

Theorem LIST_lemma:
  decode (LIST sc) = FST $ LIST0 sc ∧
  encode (LIST sc) = SND $ LIST0 sc
Proof
  simp[decode_def,encode_def] >>
  qspec_then ‘LIST sc’ assume_tac (GEN_ALL termP_term_REP) >>
  Cases_on ‘sexpcode_REP (LIST sc)’ >>
  gs[wf_decenc_def, LIST_def, repabs_pseudo_id, wf_LIST0]
QED

Theorem decode_LIST[simp]:
  decode (LIST sc) (SX_SYM s) = (if s = "nil" then SOME [] else NONE) ∧
  decode (LIST sc) (SX_CONS h t) =
  do
    ah <- decode sc h ;
    at <- decode (LIST sc) t ;
    return (ah::at)
  od ∧
  decode (LIST sc) (SX_NUM n) = NONE ∧
  decode (LIST sc) (SX_STR s) = NONE
Proof
  simp[LIST_lemma, LIST0_def, AllCaseEqs()] >>
  Cases_on ‘strip_sxcons t’ >> simp[] >>
  metis_tac[TypeBase.nchotomy_of “:'a option”]
QED

Theorem encode_LIST[simp]:
  encode (LIST sc) [] = nil ∧
  encode (LIST sc) (h::t) = SX_CONS (encode sc h) (encode (LIST sc) t)
Proof
  simp[LIST0_def, LIST_lemma] >> rw[] >> gs[]
QED

Theorem encode_LIST_EQ_ERROR:
  ¬error_free (encode (LIST sc) as) ⇔
  ∃a. MEM a as ∧ ¬error_free (encode sc a)
Proof
  Induct_on ‘as’ >> simp[AllCaseEqs(), SF DNF_ss]
QED

Theorem decode_LIST_EQ_NONE:
  decode (LIST sc) s = NONE ⇔
  case strip_sxcons s of
    NONE => T
  | SOME els => ∃s0. MEM s0 els ∧ decode sc s0 = NONE
Proof
  Induct_on ‘s’ >> simp[]
  >- (rename [‘OPTION_MAP (CONS sh) (strip_sxcons st)’] >>
      Cases_on ‘strip_sxcons st’ >> dsimp[] >>
      Cases_on ‘decode sc sh’ >> simp[]) >>
  rw[]
QED

Theorem total_LIST[simp]:
  total (LIST sc) ⇔ total sc
Proof
  simp[total_def] >> eq_tac >> rw[]
  >- (rename [‘error_free (encode sc a)’] >>
      first_x_assum $ qspec_then ‘[a]’ mp_tac >> simp[]) >>
  CCONTR_TAC >> gs[encode_LIST_EQ_ERROR]
QED

Definition PAIR0_def:
  PAIR0 f g =
  ((λs. case s of
          SX_CONS s1 s2 =>
            do
              x <- decode f s1 ;
              y <- decode g s2 ;
              return (x,y)
            od
        | _ => NONE),
   λp. SX_CONS (encode f (FST p)) (encode g (SND p)) )
End

Theorem wf_PAIR0:
  wf_decenc (PAIR0 f g)
Proof
  simp[PAIR0_def, wf_decenc_def, FORALL_PROD] >>
  Cases_on ‘s’ >> simp[AllCaseEqs()] >>
  simp[decode_EQ_SOME_encode] >> metis_tac[]
QED

Definition PAIR_def:
  PAIR f g = sexpcode_ABS (PAIR0 f g)
End

Theorem PAIR_lemma:
  decode (PAIR f g) = FST (PAIR0 f g) ∧
  encode (PAIR f g) = SND (PAIR0 f g)
Proof
  simp[decode_def, encode_def] >>
  qspec_then ‘PAIR f g’ assume_tac (GEN_ALL termP_term_REP) >>
  Cases_on ‘sexpcode_REP (PAIR f g)’ >>
  gs[wf_decenc_def, PAIR_def, repabs_pseudo_id, wf_PAIR0]
QED

Theorem encode_PAIR[simp]:
  encode (PAIR f g) (x,y) = SX_CONS (encode f x) (encode g y)
Proof
  simp[PAIR_lemma, PAIR0_def]
QED

Theorem decode_PAIR[simp]:
  decode (PAIR f g) (SX_CONS s1 s2) = do
    x <- decode f s1 ;
    y <- decode g s2 ;
    return (x,y)
  od ∧
  decode (PAIR f g) (SX_NUM n) = NONE ∧
  decode (PAIR f g) (SX_STR s) = NONE ∧
  decode (PAIR f g) (SX_SYM s) = NONE
Proof
  simp[PAIR_lemma, PAIR0_def]
QED

Theorem total_PAIR[simp]:
  total (PAIR f g) ⇔ total f ∧ total g
Proof
  simp[total_def, FORALL_PROD] >> metis_tac[]
QED

Definition SUM0_def:
  SUM0 f g =
  ((λs. case s of
          SX_CONS s1 s2 =>
            if s1 = SX_SYM "inl" then OPTION_MAP INL $ decode f s2
            else if s1 = SX_SYM "inr" then OPTION_MAP INR $ decode g s2
            else NONE
        | _ => NONE),
   λsum. case sum of
         | INL x => SX_CONS (SX_SYM "inl") (encode f x)
         | INR y => SX_CONS (SX_SYM "inr") (encode g y))
End

Theorem wf_SUM0:
  wf_decenc (SUM0 f g)
Proof
  simp[wf_decenc_def, SUM0_def] >> Cases_on ‘s’ >>
  simp[AllCaseEqs(), SF CONJ_ss, decode_EQ_SOME_encode] >>
  gen_tac >> eq_tac >> rw[] >> simp[]
QED

Definition SUM_def:
  SUM f g = sexpcode_ABS (SUM0 f g)
End

Theorem SUM_THM[simp]:
  encode (SUM f g) (INL x) = SX_CONS (SX_SYM "inl") (encode f x) ∧
  encode (SUM f g) (INR y) = SX_CONS (SX_SYM "inr") (encode g y) ∧
  decode (SUM f g) (SX_NUM n) = NONE ∧
  decode (SUM f g) (SX_STR s) = NONE ∧
  decode (SUM f g) (SX_SYM s) = NONE ∧
  decode (SUM f g) (SX_CONS s1 s2) =
  if s1 = SX_SYM "inl" then OPTION_MAP INL (decode f s2)
  else if s1 = SX_SYM "inr" then OPTION_MAP INR (decode g s2)
  else NONE
Proof
  qspec_then ‘SUM f g’ (simp o single) encode_def >>
  qspec_then ‘SUM f g’ (simp o single) decode_def >>
  simp[SUM_def, repabs_pseudo_id, wf_SUM0] >> simp[SUM0_def]
QED

Theorem total_SUM[simp]:
  total (SUM f g) ⇔ total f ∧ total g
Proof
  simp[total_def, sumTheory.FORALL_SUM]
QED

Definition OPTION0_def:
  OPTION0 sc = ((λs. case s of
                       SX_SYM s => if s = "none" then SOME NONE else NONE
                     | SX_CONS s1 s2 => if s1 = SX_SYM "some" then
                                          OPTION_MAP SOME (decode sc s2)
                                        else NONE
                     | _ => NONE),
                λaopt. case aopt of NONE => SX_SYM "none"
                                 | SOME a => SX_CONS (SX_SYM "some")
                                                     (encode sc a))
End

Theorem wf_OPTION0:
  wf_decenc (OPTION0 sc)
Proof
  simp[wf_decenc_def, OPTION0_def, optionTheory.FORALL_OPTION, AllCaseEqs(),
       SF CONJ_ss] >>
  simp[decode_EQ_SOME_encode, EQ_IMP_THM, FORALL_AND_THM]
QED

Definition OPTION_def[nocompute]:
  OPTION sc = sexpcode_ABS (OPTION0 sc)
End

Theorem OPTION_THM[simp]:
  encode (OPTION sc) NONE = SX_SYM "none" ∧
  encode (OPTION sc) (SOME x) = SX_CONS (SX_SYM "some") (encode sc x) ∧
  decode (OPTION sc) (SX_NUM n) = NONE ∧
  decode (OPTION sc) (SX_STR s) = NONE ∧
  decode (OPTION sc) (SX_SYM s) = (if s = "none" then SOME NONE else NONE) ∧
  decode (OPTION sc) (SX_CONS s1 s2) =
  if s1 = SX_SYM "some" then OPTION_MAP SOME (decode sc s2)
  else NONE
Proof
  qspec_then ‘OPTION sc’ (simp o single) encode_def >>
  qspec_then ‘OPTION sc’ (simp o single) decode_def >>
  simp[OPTION_def, repabs_pseudo_id, wf_OPTION0] >>
  simp[OPTION0_def]
QED

Theorem total_OPTION[simp]:
  total (OPTION sc) ⇔ total sc
Proof
  simp[total_def, optionTheory.FORALL_OPTION]
QED


val _ = export_theory();
