open HolKernel Parse boolLib bossLib;

open monadsyntax ltlTheory errorStateMonadTheory

local open stringTheory in end

val _ = new_theory "formParse";

(* grammar parsed looks like

     F ::= D "->" F | D
     D ::= C "|" D | C
     C ::= U "&" C | U
     U ::= B "U" U | B
     B ::= "G" B | "F" B | "X" B | "!" B | "(" F ")" | <id>

   all the binary operators (->, |, & and U) are right-associative,
   and that order gives their relative precedences, so that -> is
   weakest and U is tightest.

   Identifiers are non-empty strings of lower-case letters.

   This is (fairly) consistent with the grammar for temporal formulas in

     https://spot.lrde.epita.fr/tl.pdf

   There's no support for 'true' and 'false' as special reserved words.

*)

val _ = ParseExtras.tight_equality()
val _ = add_monadsyntax()

val _ = temp_inferior_overload_on ("return",``errorStateMonad$UNIT``)
val _ = temp_inferior_overload_on ("fail", ``errorStateMonad$ES_FAIL``)
val _ = temp_overload_on ("monad_bind", ``errorStateMonad$BIND``)
val _ = temp_overload_on ("monad_unitbind", ``errorStateMonad$IGNORE_BIND``);
val _ = temp_overload_on ("assert", ``errorStateMonad$ES_GUARD``);
val _ = temp_overload_on ("++", ``errorStateMonad$ES_CHOICE``);

val token_def = Define‘
  (token p [] = p []) ∧
  (token p (h::t) = if isSpace h then token p t else p (h::t))
’;

val token_APPEND = Q.store_thm(
  "token_APPEND[simp]",
  ‘EVERY isSpace s1 ⇒ token p (s1 ++ s2) = token p s2’,
  Induct_on ‘s1’ >> simp[token_def]);

val token_Spaces = token_APPEND |> Q.INST [‘s2’ |-> ‘[]’]
                                |> REWRITE_RULE [listTheory.APPEND_NIL]

val literal_def = Define‘
  literal s inp = if s <<= inp then SOME ((), DROP (LENGTH s) inp)
                  else NONE
’;

val ident_def = Define‘
  (ident [] = NONE) ∧
  (ident (h::t) = if isAlpha h ∧ isLower h then
                    case ident t of
                        NONE => SOME([h], t)
                      | SOME (i, r) => SOME (h::i, r)
                  else NONE)
’;

val ident_EQ_SOME = Q.store_thm(
  "ident_EQ_SOME[simp]",
  ‘ident s = SOME v ⇔
     ∃px sx. s = px ++ sx ∧ px ≠ [] ∧ EVERY (λc. isAlpha c ∧ isLower c) px ∧
             (∀c t. sx = c::t ⇒ ¬isAlpha c ∨ ¬isLower c) ∧ v = (px, sx)’,
  qid_spec_tac ‘v’ >> Induct_on ‘s’ >> simp[ident_def] >>
  rpt gen_tac >> rename [‘isAlpha c1’] >> Cases_on ‘isAlpha c1 ∧ isLower c1’
  >- (simp[optionTheory.option_case_eq, pairTheory.pair_case_eq, PULL_EXISTS] >>
      rw[EQ_IMP_THM]
      >- (rw[] >>
          fs[ident_def, optionTheory.option_case_eq, pairTheory.pair_case_eq])>>
      Cases_on ‘px’ >> fs[] >> rw[] >>
      rename [‘ident (cs ++ sx) = NONE’] >> Cases_on ‘cs’ >> simp[] >>
      Cases_on ‘sx’ >> fs[ident_def]) >>
  simp[] >> rw[] >> Cases_on ‘px’ >> simp[] >> metis_tac[]);

val token_EQ_NONE = Q.store_thm(
  "token_EQ_NONE",
  ‘(token p s = NONE) ⇔
     ∃px sx. s = px ++ sx ∧ EVERY isSpace px ∧ (∀h t. sx = h::t ⇒ ¬isSpace h) ∧
             p sx = NONE’,
  Induct_on ‘s’ >> simp[token_def, TypeBase.case_eq_of ``:bool``] >> rw[] >>
  rw[EQ_IMP_THM]
  >- (rename [‘h :: (px ++ sx)’] >> map_every qexists_tac [‘h::px’, ‘sx’] >>
      simp[])
  >- (rename [‘h::rest = _ ++ _’] >> map_every qexists_tac [‘[]’, ‘h::rest’] >>
      simp[])
  >- (rename [‘h::rest = px ++ sx’] >> Cases_on ‘isSpace h’
      >- (simp[] >> Cases_on ‘px’ >> fs[] >> rw[] >> metis_tac[])
      >- (‘px = []’ by (Cases_on ‘px’ >> fs[] >> rw[] >> fs[]) >>
          fs[])));

val token_EQ_SOME = Q.store_thm(
  "token_EQ_SOME",
  ‘(token p s = SOME (v, s')) ⇔
    ∃px sx. s = px ++ sx ∧ EVERY isSpace px ∧ (∀h t. sx = h :: t ⇒ ¬isSpace h) ∧
            p sx = SOME (v, s')’,
  Induct_on ‘s’ >> simp[token_def, TypeBase.case_eq_of “:bool”] >>
  qx_gen_tac ‘c’ >> Cases_on ‘isSpace c’ >> simp[]
  >- (rw[EQ_IMP_THM]
      >- (map_every qexists_tac [‘c :: px’, ‘sx’] >> simp[]) >>
      ‘∃pt. px = c :: pt’ by (Cases_on ‘px’ >> fs[] >> rw[] >> fs[]) >>
      fs[] >> metis_tac[]) >>
  rw[EQ_IMP_THM]
  >- (rename [‘p (c::s) = SOME _’] >> map_every qexists_tac [‘[]’, ‘c::s’] >>
      simp[]) >>
  Cases_on ‘px’ >> fs[]);

val literal_EQ_SOME = Q.store_thm(
  "literal_EQ_SOME",
  ‘literal l s = SOME ((), sx) ⇔ (s = l ++ sx)’,
  csimp[literal_def, rich_listTheory.IS_PREFIX_APPEND, PULL_EXISTS,
        rich_listTheory.DROP_LENGTH_APPEND]);

val literal_EQ_NONE = Q.store_thm(
  "literal_EQ_NONE",
  ‘literal l s = NONE ⇔ ¬(l <<= s)’,
  simp[literal_def]);

val parseFGX_def = Define ‘
  parseFGX fgx top =
    do
      token (literal "F") ;
      f <- fgx ;
      return (LTL_F f "")
    od ++
    do
      token (literal "G") ;
      f <- fgx ;
      return (LTL_G f "")
    od ++
    do
      token (literal "X") ;
      f <- fgx ;
      return (F_X f)
    od ++
    do
      token (literal "!") ;
      f <- fgx ;
      return (F_NEG f)
    od ++
    do
      token (literal "(") ;
      f <- top ;
      token (literal ")") ;
      return f
    od ++
    do
      v <- token ident ;
      return (F_VAR v)
    od
’;

val parseFGX_CONG = Q.store_thm(
  "parseFGX_CONG[defncong]",
  ‘∀s1 s2 f1 f2 top1 top2.
     (s1 = s2) ∧ (∀s. LENGTH s < LENGTH s1 ⇒ (f1 s = f2 s)) ∧
     (∀s. LENGTH s < LENGTH s1 ⇒ (top1 s = top2 s)) ⇒
     (parseFGX f1 top1 s1 = parseFGX f2 top2 s2)’,
  simp[] >> rpt strip_tac >>
  simp[parseFGX_def, GSYM ES_CHOICE_ASSOC, IGNORE_BIND_DEF] >>
  ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
  ONCE_REWRITE_TAC [BIND_DEF] >>
  rename [‘token (literal "F") s0’] >>
  reverse (Cases_on ‘token (literal "F") s0’) >> simp[]
  >- (rename [‘token (literal "F") s0 = SOME p’] >> Cases_on ‘p’ >> simp[] >>
      simp[BIND_DEF] >> fs[token_EQ_SOME, literal_EQ_SOME] >>
      rename [‘option_CASE (f2 s')’, ‘f1 _ = f2 _’] >>
      reverse (Cases_on ‘f2 s'’) >> simp[UNIT_DEF]
      >- (rename [‘f2 s' = SOME p’] >> Cases_on ‘p’ >> simp[]) >>
      REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      ntac 4 (ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
              simp[BIND_DEF, token_def, literal_def])) >>
  fs[token_EQ_NONE, literal_EQ_NONE] >> Cases_on ‘sx’ >> fs[]
  >- simp[ES_CHOICE_DEF, token_Spaces, BIND_DEF, token_def, literal_def] >>
  ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
  simp[token_Spaces, BIND_DEF, token_def, literal_def] >> rw[]
  >- (rename [‘option_CASE (f2 s2)’, ‘f1 _ = f2 _’] >> Cases_on ‘f2 s2’ >>
      simp[]
      >- ntac 3 (ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
                 simp[BIND_DEF, token_def, literal_def]) >>
      rename [‘f2 s2 = SOME p’] >> Cases_on ‘p’ >> simp[UNIT_DEF]) >>
  ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
  simp[BIND_DEF, token_def, literal_def] >> rw[]
  >- (rename [‘option_CASE (f2 s2)’, ‘f1 _ = f2 _’] >> Cases_on ‘f2 s2’ >>
      simp[]
      >- ntac 2 (ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
                 simp[BIND_DEF, token_def, literal_def]) >>
      rename [‘f2 s2 = SOME p’] >> Cases_on ‘p’ >> simp[UNIT_DEF]) >>
  ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
  simp[BIND_DEF, token_def, literal_def] >> rw[]
  >- (rename [‘option_CASE (f2 s2)’, ‘f1 _ = f2 _’] >> Cases_on ‘f2 s2’ >>
      simp[]
      >- ntac 2 (ONCE_REWRITE_TAC [ES_CHOICE_DEF] >>
                 simp[BIND_DEF, token_def, literal_def]) >>
      rename [‘f2 s2 = SOME p’] >> Cases_on ‘p’ >> simp[UNIT_DEF]) >>
  simp[ES_CHOICE_DEF, BIND_DEF, token_def, literal_def] >> rw[]);

val ParseFGX_def = tDefine "ParseFGX" `
  ParseFGX top s = parseFGX (ParseFGX top) top s
` (WF_REL_TAC ‘inv_image $< (STRLEN o SND)’);

val ParseFGX_thm =
  ParseFGX_def
    |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss)
          [parseFGX_def, Once (GSYM FUN_EQ_THM)]

val mksafe_def = Define‘
  mksafe f s = case f s of
                   NONE => NONE
                 | SOME (v, s') => if IS_SUFFIX s s' then SOME (v, s')
                                   else NONE
’;

val is_safe_def = Define‘
  is_safe p = ∀s s' v. p s = SOME (v,s') ⇒ IS_SUFFIX s s'
’;

val is_safe_mksafe = Q.store_thm(
  "is_safe_mksafe[simp]",
  ‘is_safe (mksafe p)’,
  simp[is_safe_def, mksafe_def, optionTheory.option_case_eq,
       pairTheory.pair_case_eq]);

val IGNORE_BIND_EQ_SOME = Q.store_thm(
  "IGNORE_BIND_EQ_SOME[simp]",
  ‘IGNORE_BIND m1 m2 s = SOME r ⇔ ∃v0 s'. m1 s = SOME (v0,s') ∧ m2 s' = SOME r’,
  simp[IGNORE_BIND_DEF, BIND_DEF, optionTheory.option_case_eq,
       pairTheory.pair_case_eq, PULL_EXISTS]);

val is_safe_mksafe_id = Q.store_thm(
  "is_safe_mksafe_id",
  ‘is_safe p ⇒ mksafe p = p’,
  simp[is_safe_def, mksafe_def, FUN_EQ_THM, optionTheory.option_case_eq,
       pairTheory.pair_case_eq, PULL_EXISTS] >> rw[] >> csimp[] >>
  metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES]);

val IS_SUFFIX_APPEND_I = Q.store_thm(
  "IS_SUFFIX_APPEND_I",
  ‘IS_SUFFIX m n ⇒ IS_SUFFIX (p ++ m) n’,
  simp[rich_listTheory.IS_SUFFIX_APPEND, PULL_EXISTS]);

val IS_SUFFIX_APPEND_E = Q.store_thm(
  "IS_SUFFIX_APPEND_E",
  ‘IS_SUFFIX m (p ++ n) ⇒ IS_SUFFIX m n’,
  simp[rich_listTheory.IS_SUFFIX_APPEND, PULL_EXISTS]);

val IS_SUFFIX_TRANS = Q.store_thm(
  "IS_SUFFIX_TRANS",
  ‘IS_SUFFIX m n ∧ IS_SUFFIX n p ⇒ IS_SUFFIX m p’,
  metis_tac[rich_listTheory.IS_PREFIX_TRANS,
            rich_listTheory.IS_SUFFIX_compute]);

val is_safe_BIND = Q.store_thm(
  "is_safe_BIND",
  ‘is_safe m ∧ (∀v. is_safe (f v)) ⇒ is_safe (BIND m f)’,
  simp[is_safe_def, BIND_DEF, optionTheory.option_case_eq, PULL_EXISTS,
       pairTheory.pair_case_eq] >> rpt strip_tac >>
  rpt (first_x_assum drule) >> metis_tac[IS_SUFFIX_TRANS]);

val is_safe_ParseFGX = Q.store_thm(
  "is_safe_ParseFGX",
  ‘is_safe top ⇒ is_safe (ParseFGX top)’,
  simp[is_safe_def] >> strip_tac >>
  gen_tac >> completeInduct_on ‘STRLEN s’ >> fs[PULL_FORALL] >>
  rw[Once ParseFGX_thm] >> pop_assum mp_tac >>
  simp[ES_CHOICE_DEF, optionTheory.option_case_eq] >>
  simp[BIND_DEF, optionTheory.option_case_eq, token_EQ_SOME, literal_EQ_SOME,
       pairTheory.pair_case_eq, PULL_EXISTS, UNIT_DEF] >>
  rw[]
  >- simp[IS_SUFFIX_APPEND_I]
  >- (first_assum (drule_then assume_tac) >> irule IS_SUFFIX_TRANS >>
      rename [‘IS_SUFFIX s0 (ws ++ ")" ++ s)’] >> qexists_tac ‘s0’ >>
      simp[IS_SUFFIX_APPEND_I] >> metis_tac[IS_SUFFIX_APPEND_E])
  >- (fs[] >> rpt (irule IS_SUFFIX_APPEND_I) >> first_x_assum irule >>
      simp[] >> metis_tac[])
  >- (fs[] >> rpt (irule IS_SUFFIX_APPEND_I) >> first_x_assum irule >>
      simp[] >> metis_tac[])
  >- (fs[] >> rpt (irule IS_SUFFIX_APPEND_I) >> first_x_assum irule >>
      simp[] >> metis_tac[])
  >- (fs[] >> rpt (irule IS_SUFFIX_APPEND_I) >> first_x_assum irule >>
      simp[] >> metis_tac[]));

val IS_SUFFIX_LENGTH = Q.store_thm(
  "IS_SUFFIX_LENGTH",
  ‘IS_SUFFIX m n ⇒ LENGTH n ≤ LENGTH m’,
  metis_tac[listTheory.LENGTH_REVERSE, rich_listTheory.IS_PREFIX_LENGTH,
            rich_listTheory.IS_SUFFIX_compute]);


val ParseFGX_CONG = Q.store_thm("ParseFGX_CONG[defncong]",
  ‘∀s1 s2 t1 t2.
     (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ⇒
     ParseFGX t1 s1 = ParseFGX t2 s2’,
  ONCE_REWRITE_TAC [ParseFGX_def] >> rpt strip_tac >> rw[] >>
  rename [‘parseFGX _ _ s’] >>
  ‘∀t. STRLEN t ≤ STRLEN s ⇒
       parseFGX (λa. ParseFGX t1 a) t1 t = parseFGX (λa. ParseFGX t2 a) t2 t’
    suffices_by metis_tac[DECIDE “x:num ≤ x”] >> gen_tac >>
  completeInduct_on ‘STRLEN t’ >> fs[PULL_FORALL] >> rw[] >>
  irule parseFGX_CONG >> simp[] >> rpt strip_tac >>
  ONCE_REWRITE_TAC [ParseFGX_def] >> first_x_assum irule >> simp[]);

val mksafe_cong = Q.store_thm("mksafe_cong",
  ‘∀n. (∀s. STRLEN s < n ⇒ t1 s = t2 s) ⇒
       ∀s. STRLEN s < n ⇒ mksafe t1 s = mksafe t2 s’,
  simp[mksafe_def]);

val parseU_def = Define‘
  parseU u top =
    do
      f1 <- ParseFGX (mksafe top) ;
      do
        token (literal "U") ;
        f2 <- u ;
        return (F_U f1 f2)
      od ++ return f1
    od
’;

val parseU_CONG = Q.store_thm("parseU_CONG[defncong]",
  ‘∀s1 s2 t1 t2 c1 c2.
      (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ∧
      (∀s. STRLEN s < STRLEN s1 ⇒ c1 s = c2 s) ⇒
      (parseU c1 t1 s1 = parseU c2 t2 s2)’,
  rw[parseU_def, BIND_DEF] >>
  csimp[optionTheory.option_case_eq, pairTheory.pair_case_eq] >>
  rename [‘∀s. STRLEN s < STRLEN s0 ⇒ _ s = _ s’] >>
  ‘∀s. STRLEN s < STRLEN s0 ⇒ mksafe t1 s = mksafe t2 s’
    by metis_tac[mksafe_cong] >>
  ‘ParseFGX (mksafe t2) s0 = ParseFGX (mksafe t1) s0’
    by (irule ParseFGX_CONG >> simp[]) >>
  dsimp[] >> csimp[] >> rename [‘ParseFGX (mksafe t) s = NONE’] >>
  Cases_on ‘ParseFGX (mksafe t) s’ >> simp[] >>
  rename [‘ParseFGX (mksafe t) s = SOME p’] >>
  Cases_on ‘p’ >> simp[BIND_DEF, IGNORE_BIND_DEF, ES_CHOICE_DEF] >>
  rename [‘token (literal "U") s2’] >> Cases_on ‘token (literal "U") s2’ >>
  simp[] >> rename [‘token _ s2 = SOME p’] >> Cases_on ‘p’ >>
  fs[token_EQ_SOME, literal_EQ_SOME, optionTheory.option_case_eq, UNIT_DEF,
     PULL_EXISTS, pairTheory.pair_case_eq] >>
  rename [‘c1 ss = NONE’, ‘c1 _ = c2 _’, ‘c1 ss = SOME (_, ws ++ "U" ++ ss)’] >>
  Cases_on ‘c1 ss’ >> simp[]
  >- (disj1_tac >> rw[] >>
      ‘is_safe (ParseFGX (mksafe t))’ by simp[is_safe_ParseFGX] >>
      fs[is_safe_def] >> pop_assum drule >> strip_tac >>
      drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
      Q.UNDISCH_THEN `c1 ss = NONE` mp_tac >> simp[]) >>
  ‘is_safe (ParseFGX (mksafe t))’ by simp[is_safe_ParseFGX] >>
  fs[is_safe_def] >> pop_assum drule >> strip_tac >>
  drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `c1 ss = SOME _` mp_tac >> simp[] >>
  metis_tac[pairTheory.pair_CASES]);

val ParseU_def = tDefine "ParseU" ‘
  ParseU top s = parseU (ParseU top) top s
’ (WF_REL_TAC ‘inv_image $< (STRLEN o SND)’);

val ParseU_thm =
    ParseU_def |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss) [parseU_def]

val ParseU_CONG = Q.store_thm(
  "ParseU_CONG[defncong]",
  ‘∀s1 s2 t1 t2.
     (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ⇒
     ParseU t1 s1 = ParseU t2 s2’,
  simp[] >> rpt strip_tac >> rename [‘ParseU _ s’] >>
  ‘∀t. STRLEN t ≤ STRLEN s ⇒ ParseU t1 t = ParseU t2 t’
    suffices_by metis_tac[DECIDE “x:num ≤ x”] >> gen_tac >>
  completeInduct_on ‘STRLEN t’ >> fs[PULL_FORALL] >> rw[] >>
  ONCE_REWRITE_TAC [ParseU_def] >> irule parseU_CONG >> simp[]);

val is_safe_ParseU = Q.store_thm(
  "is_safe_ParseU",
  ‘is_safe (ParseU top)’,
  simp[is_safe_def] >> gen_tac >> completeInduct_on ‘STRLEN s’ >>
  fs[PULL_FORALL] >>
  simp[Once ParseU_thm, BIND_DEF, optionTheory.option_case_eq, is_safe_def,
       pairTheory.pair_CASES, PULL_EXISTS, pairTheory.FORALL_PROD,
       ES_CHOICE_DEF, UNIT_DEF, token_EQ_SOME, literal_EQ_SOME] >>
  rw[]
  >- metis_tac[is_safe_def, is_safe_ParseFGX, is_safe_mksafe] >>
  fs[pairTheory.pair_case_eq] >> rw[] >>
  rename [‘ParseFGX (mksafe top) s0 = SOME (f1, px ++ "U" ++ s2)’] >>
  ‘IS_SUFFIX s0 (px ++ "U" ++ s2)’
    by metis_tac[is_safe_def, is_safe_mksafe, is_safe_ParseFGX] >>
  rename [‘ParseU top s2 = SOME (f2, s3)’] >>
  ‘IS_SUFFIX s2 s3’
    by (first_x_assum irule >> simp[] >> fs[rich_listTheory.IS_SUFFIX_APPEND])>>
  metis_tac[IS_SUFFIX_TRANS, IS_SUFFIX_APPEND_E]);

val parseCNJ_def = Define‘
  parseCNJ cnj top =
    do
      f1 <- ParseU (mksafe top) ;
      do
        token (literal "&") ;
        f2 <- cnj ;
        return (F_CONJ f1 f2)
      od ++ return f1
    od
’;

val parseCNJ_CONG = Q.store_thm("parseCNJ_CONG[defncong]",
  ‘∀s1 s2 t1 t2 c1 c2.
      (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ∧
      (∀s. STRLEN s < STRLEN s1 ⇒ c1 s = c2 s) ⇒
      (parseCNJ c1 t1 s1 = parseCNJ c2 t2 s2)’,
  rw[parseCNJ_def, BIND_DEF] >>
  csimp[optionTheory.option_case_eq, pairTheory.pair_case_eq] >>
  rename [‘∀s. STRLEN s < STRLEN s0 ⇒ _ s = _ s’] >>
  ‘∀s. STRLEN s < STRLEN s0 ⇒ mksafe t1 s = mksafe t2 s’
    by metis_tac[mksafe_cong] >>
  ‘ParseU (mksafe t2) s0 = ParseU (mksafe t1) s0’
    by (irule ParseU_CONG >> simp[]) >>
  dsimp[] >> csimp[] >> rename [‘ParseU (mksafe t) s = NONE’] >>
  Cases_on ‘ParseU (mksafe t) s’ >> simp[] >>
  rename [‘ParseU (mksafe t) s = SOME p’] >>
  Cases_on ‘p’ >> simp[BIND_DEF, IGNORE_BIND_DEF, ES_CHOICE_DEF] >>
  rename [‘token (literal "&") s2’] >> Cases_on ‘token (literal "&") s2’ >>
  simp[] >> rename [‘token _ s2 = SOME p’] >> Cases_on ‘p’ >>
  fs[token_EQ_SOME, literal_EQ_SOME, optionTheory.option_case_eq, UNIT_DEF,
     PULL_EXISTS, pairTheory.pair_case_eq] >>
  rename [‘c1 ss = NONE’, ‘c1 _ = c2 _’, ‘c1 ss = SOME (_, ws ++ "&" ++ ss)’] >>
  Cases_on ‘c1 ss’ >> simp[]
  >- (disj1_tac >> rw[] >>
      ‘is_safe (ParseU (mksafe t))’ by simp[is_safe_ParseU] >>
      fs[is_safe_def] >> pop_assum drule >> strip_tac >>
      drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
      Q.UNDISCH_THEN `c1 ss = NONE` mp_tac >> simp[]) >>
  ‘is_safe (ParseU (mksafe t))’ by simp[is_safe_ParseU] >>
  fs[is_safe_def] >> pop_assum drule >> strip_tac >>
  drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `c1 ss = SOME _` mp_tac >> simp[] >>
  metis_tac[pairTheory.pair_CASES]);

val ParseCNJ_def = tDefine "ParseCNJ" ‘
  ParseCNJ top s = parseCNJ (ParseCNJ top) top s
’ (WF_REL_TAC ‘inv_image $< (STRLEN o SND)’)

val ParseCNJ_thm =
    ParseCNJ_def |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss) [parseCNJ_def]

val ParseCNJ_CONG = Q.store_thm(
  "ParseCNJ_CONG[defncong]",
  ‘∀s1 s2 t1 t2.
     (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ⇒
     ParseCNJ t1 s1 = ParseCNJ t2 s2’,
  simp[] >> rpt strip_tac >> rename [‘ParseCNJ _ s’] >>
  ‘∀t. STRLEN t ≤ STRLEN s ⇒ ParseCNJ t1 t = ParseCNJ t2 t’
    suffices_by metis_tac[DECIDE “x:num ≤ x”] >> gen_tac >>
  completeInduct_on ‘STRLEN t’ >> fs[PULL_FORALL] >> rw[] >>
  ONCE_REWRITE_TAC [ParseCNJ_def] >> irule parseCNJ_CONG >> simp[]);

val is_safe_ParseCNJ = Q.store_thm(
  "is_safe_ParseCNJ",
  ‘is_safe (ParseCNJ top)’,
  simp[is_safe_def] >> gen_tac >> completeInduct_on ‘STRLEN s’ >>
  fs[PULL_FORALL] >>
  simp[Once ParseCNJ_thm, BIND_DEF, optionTheory.option_case_eq, is_safe_def,
       pairTheory.pair_CASES, PULL_EXISTS, pairTheory.FORALL_PROD,
       ES_CHOICE_DEF, UNIT_DEF, token_EQ_SOME, literal_EQ_SOME] >>
  rw[]
  >- metis_tac[is_safe_def, is_safe_ParseU, is_safe_mksafe] >>
  fs[pairTheory.pair_case_eq] >> rw[] >>
  rename [‘ParseU (mksafe top) s0 = SOME (f1, px ++ "&" ++ s2)’] >>
  ‘IS_SUFFIX s0 (px ++ "&" ++ s2)’
    by metis_tac[is_safe_def, is_safe_mksafe, is_safe_ParseU] >>
  rename [‘ParseCNJ top s2 = SOME (f2, s3)’] >>
  ‘IS_SUFFIX s2 s3’
    by (first_x_assum irule >> simp[] >> fs[rich_listTheory.IS_SUFFIX_APPEND])>>
  metis_tac[IS_SUFFIX_TRANS, IS_SUFFIX_APPEND_E]);

val F_DISJ_def = zDefine‘
  F_DISJ f1 f2 = F_NEG (F_CONJ (F_NEG f1) (F_NEG f2))
’;

val parseDSJ_def = Define‘
  parseDSJ d top =
    do
      f1 <- ParseCNJ (mksafe top) ;
      do
        token (literal "|") ;
        f2 <- d ;
        return (F_DISJ f1 f2)
      od ++ return f1
    od
’;

val parseDSJ_CONG = Q.store_thm("parseDSJ_CONG[defncong]",
  ‘∀s1 s2 t1 t2 d1 d2.
      (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ∧
      (∀s. STRLEN s < STRLEN s1 ⇒ d1 s = d2 s) ⇒
      (parseDSJ d1 t1 s1 = parseDSJ d2 t2 s2)’,
  rw[parseDSJ_def, BIND_DEF] >>
  csimp[optionTheory.option_case_eq, pairTheory.pair_case_eq] >>
  rename [‘∀s. STRLEN s < STRLEN s0 ⇒ _ s = _ s’] >>
  ‘∀s. STRLEN s < STRLEN s0 ⇒ mksafe t1 s = mksafe t2 s’
    by metis_tac[mksafe_cong] >>
  ‘ParseCNJ (mksafe t2) s0 = ParseCNJ (mksafe t1) s0’
    by (irule ParseCNJ_CONG >> simp[]) >>
  dsimp[] >> csimp[] >> rename [‘ParseCNJ (mksafe t) s = NONE’] >>
  Cases_on ‘ParseCNJ (mksafe t) s’ >> simp[] >>
  rename [‘ParseCNJ (mksafe t) s = SOME p’] >>
  Cases_on ‘p’ >> simp[BIND_DEF, IGNORE_BIND_DEF, ES_CHOICE_DEF] >>
  rename [‘token (literal "|") s2’] >> Cases_on ‘token (literal "|") s2’ >>
  simp[] >> rename [‘token _ s2 = SOME p’] >> Cases_on ‘p’ >>
  fs[token_EQ_SOME, literal_EQ_SOME, optionTheory.option_case_eq, UNIT_DEF,
     PULL_EXISTS, pairTheory.pair_case_eq] >>
  rename [‘c1 ss = NONE’, ‘c1 _ = c2 _’, ‘c1 ss = SOME (_, ws ++ "|" ++ ss)’] >>
  Cases_on ‘c1 ss’ >> simp[]
  >- (disj1_tac >> rw[] >>
      ‘is_safe (ParseCNJ (mksafe t))’ by simp[is_safe_ParseCNJ] >>
      fs[is_safe_def] >> pop_assum drule >> strip_tac >>
      drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
      Q.UNDISCH_THEN `c1 ss = NONE` mp_tac >> simp[]) >>
  ‘is_safe (ParseCNJ (mksafe t))’ by simp[is_safe_ParseCNJ] >>
  fs[is_safe_def] >> pop_assum drule >> strip_tac >>
  drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `c1 ss = SOME _` mp_tac >> simp[] >>
  metis_tac[pairTheory.pair_CASES]);

val ParseDSJ_def = tDefine "ParseDSJ" ‘
  ParseDSJ top s = parseDSJ (ParseDSJ top) top s
’ (WF_REL_TAC ‘inv_image $< (STRLEN o SND)’)

val ParseDSJ_thm =
    ParseDSJ_def |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss) [parseDSJ_def]

val ParseDSJ_CONG = Q.store_thm(
  "ParseDSJ_CONG[defncong]",
  ‘∀s1 s2 t1 t2.
     (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ⇒
     ParseDSJ t1 s1 = ParseDSJ t2 s2’,
  simp[] >> rpt strip_tac >> rename [‘ParseDSJ _ s’] >>
  ‘∀t. STRLEN t ≤ STRLEN s ⇒ ParseDSJ t1 t = ParseDSJ t2 t’
    suffices_by metis_tac[DECIDE “x:num ≤ x”] >> gen_tac >>
  completeInduct_on ‘STRLEN t’ >> fs[PULL_FORALL] >> rw[] >>
  ONCE_REWRITE_TAC [ParseDSJ_def] >> irule parseDSJ_CONG >> simp[]);

val is_safe_ParseDSJ = Q.store_thm(
  "is_safe_ParseDSJ",
  ‘is_safe (ParseDSJ top)’,
  simp[is_safe_def] >> gen_tac >> completeInduct_on ‘STRLEN s’ >>
  fs[PULL_FORALL] >>
  simp[Once ParseDSJ_thm, BIND_DEF, optionTheory.option_case_eq, is_safe_def,
       pairTheory.pair_CASES, PULL_EXISTS, pairTheory.FORALL_PROD,
       ES_CHOICE_DEF, UNIT_DEF, token_EQ_SOME, literal_EQ_SOME] >>
  rw[]
  >- metis_tac[is_safe_def, is_safe_ParseCNJ, is_safe_mksafe] >>
  fs[pairTheory.pair_case_eq] >> rw[] >>
  rename [‘ParseCNJ (mksafe top) s0 = SOME (f1, px ++ "|" ++ s2)’] >>
  ‘IS_SUFFIX s0 (px ++ "|" ++ s2)’
    by metis_tac[is_safe_def, is_safe_mksafe, is_safe_ParseCNJ] >>
  rename [‘ParseDSJ top s2 = SOME (f2, s3)’] >>
  ‘IS_SUFFIX s2 s3’
    by (first_x_assum irule >> simp[] >> fs[rich_listTheory.IS_SUFFIX_APPEND])>>
  metis_tac[IS_SUFFIX_TRANS, IS_SUFFIX_APPEND_E]);

val F_IMP_def = zDefine‘
  F_IMP f1 f2 = F_DISJ (F_NEG f1) f2
’;

val parseIMP_def = Define‘
  parseIMP d top =
    do
      f1 <- ParseDSJ (mksafe top) ;
      do
        token (literal "->") ;
        f2 <- d ;
        return (F_IMP f1 f2)
      od ++ return f1
    od
’;

val parseIMP_CONG = Q.store_thm("parseIMP_CONG[defncong]",
  ‘∀s1 s2 t1 t2 d1 d2.
      (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ∧
      (∀s. STRLEN s < STRLEN s1 ⇒ d1 s = d2 s) ⇒
      (parseIMP d1 t1 s1 = parseIMP d2 t2 s2)’,
  rw[parseIMP_def, BIND_DEF] >>
  csimp[optionTheory.option_case_eq, pairTheory.pair_case_eq] >>
  rename [‘∀s. STRLEN s < STRLEN s0 ⇒ _ s = _ s’] >>
  ‘∀s. STRLEN s < STRLEN s0 ⇒ mksafe t1 s = mksafe t2 s’
    by metis_tac[mksafe_cong] >>
  ‘ParseDSJ (mksafe t2) s0 = ParseDSJ (mksafe t1) s0’
    by (irule ParseDSJ_CONG >> simp[]) >>
  dsimp[] >> csimp[] >> rename [‘ParseDSJ (mksafe t) s = NONE’] >>
  Cases_on ‘ParseDSJ (mksafe t) s’ >> simp[] >>
  rename [‘ParseDSJ (mksafe t) s = SOME p’] >>
  Cases_on ‘p’ >> simp[BIND_DEF, IGNORE_BIND_DEF, ES_CHOICE_DEF] >>
  rename [‘token (literal "->") s2’] >> Cases_on ‘token (literal "->") s2’ >>
  simp[] >> rename [‘token _ s2 = SOME p’] >> Cases_on ‘p’ >>
  fs[token_EQ_SOME, literal_EQ_SOME, optionTheory.option_case_eq, UNIT_DEF,
     PULL_EXISTS, pairTheory.pair_case_eq] >>
  rename [‘c1 ss = NONE’, ‘c1 _ = c2 _’, ‘c1 ss = SOME (_, ws ++ "->" ++ ss)’] >>
  Cases_on ‘c1 ss’ >> simp[]
  >- (disj1_tac >> rw[] >>
      ‘is_safe (ParseDSJ (mksafe t))’ by simp[is_safe_ParseDSJ] >>
      fs[is_safe_def] >> pop_assum drule >> strip_tac >>
      drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
      Q.UNDISCH_THEN `c1 ss = NONE` mp_tac >> simp[]) >>
  ‘is_safe (ParseDSJ (mksafe t))’ by simp[is_safe_ParseDSJ] >>
  fs[is_safe_def] >> pop_assum drule >> strip_tac >>
  drule IS_SUFFIX_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `c1 ss = SOME _` mp_tac >> simp[] >>
  metis_tac[pairTheory.pair_CASES]);

val ParseIMP_def = tDefine "ParseIMP" ‘
  ParseIMP top s = parseIMP (ParseIMP top) top s
’ (WF_REL_TAC ‘inv_image $< (STRLEN o SND)’)

val ParseIMP_thm =
    ParseIMP_def |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss) [parseIMP_def]

val ParseIMP_CONG = Q.store_thm(
  "ParseIMP_CONG[defncong]",
  ‘∀s1 s2 t1 t2.
     (s1 = s2) ∧ (∀s. STRLEN s < STRLEN s1 ⇒ t1 s = t2 s) ⇒
     ParseIMP t1 s1 = ParseIMP t2 s2’,
  simp[] >> rpt strip_tac >> rename [‘ParseIMP _ s’] >>
  ‘∀t. STRLEN t ≤ STRLEN s ⇒ ParseIMP t1 t = ParseIMP t2 t’
    suffices_by metis_tac[DECIDE “x:num ≤ x”] >> gen_tac >>
  completeInduct_on ‘STRLEN t’ >> fs[PULL_FORALL] >> rw[] >>
  ONCE_REWRITE_TAC [ParseIMP_def] >> irule parseIMP_CONG >> simp[]);

val is_safe_ParseIMP = Q.store_thm(
  "is_safe_ParseIMP",
  ‘is_safe (ParseIMP top)’,
  simp[is_safe_def] >> gen_tac >> completeInduct_on ‘STRLEN s’ >>
  fs[PULL_FORALL] >>
  simp[Once ParseIMP_thm, BIND_DEF, optionTheory.option_case_eq, is_safe_def,
       pairTheory.pair_CASES, PULL_EXISTS, pairTheory.FORALL_PROD,
       ES_CHOICE_DEF, UNIT_DEF, token_EQ_SOME, literal_EQ_SOME] >>
  rw[]
  >- metis_tac[is_safe_def, is_safe_ParseDSJ, is_safe_mksafe] >>
  fs[pairTheory.pair_case_eq] >> rw[] >>
  rename [‘ParseDSJ (mksafe top) s0 = SOME (f1, px ++ "->" ++ s2)’] >>
  ‘IS_SUFFIX s0 (px ++ "->" ++ s2)’
    by metis_tac[is_safe_def, is_safe_mksafe, is_safe_ParseDSJ] >>
  rename [‘ParseIMP top s2 = SOME (f2, s3)’] >>
  ‘IS_SUFFIX s2 s3’
    by (first_x_assum irule >> simp[] >> fs[rich_listTheory.IS_SUFFIX_APPEND])>>
  metis_tac[IS_SUFFIX_TRANS, IS_SUFFIX_APPEND_E]);


val Parse_def = tDefine "Parse" ‘Parse s = ParseIMP Parse s’
  (WF_REL_TAC ‘inv_image $< STRLEN’)

val is_safe_Parse = Q.store_thm(
  "is_safe_Parse",
  ‘is_safe Parse’,
  simp[is_safe_def, Once Parse_def] >> simp[GSYM is_safe_def] >>
  simp_tac (srw_ss() ++ boolSimps.ETA_ss) [is_safe_ParseIMP]);

val Parse_thm = save_thm(
  "Parse_thm",
  Parse_def
    |> SIMP_RULE (srw_ss() ++ boolSimps.ETA_ss)
         [ParseIMP_thm, is_safe_mksafe_id, is_safe_Parse]);

val eg1 = time EVAL “Parse "pp & Gq -> pp U X(x|!y|z)"”;

val _ = export_theory();
