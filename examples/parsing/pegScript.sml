open HolKernel Parse boolLib bossLib
open boolSimps

open grammarTheory finite_mapTheory

val _ = new_theory "peg"

(* Based on
     Koprowski and Binzstok, "TRX: A Formally Verified Parser Interpreter".
     LMCS vol 7, no. 2. 2011.
     DOI: 10.2168/LMCS-7(2:18)2011
*)

val _ = Hol_datatype `pegsym =
    empty of 'c
  | any of ('a tok -> 'e -> 'c)
  | tok of 'a tok => ('e -> 'c)
  | nt of 'b inf => ('c -> 'c)
  | seq of pegsym => pegsym => ('c -> 'c -> 'c)
  | choice of pegsym => pegsym => ('c + 'c -> 'c)
  | rpt of pegsym => ('c list -> 'c)
  | not of pegsym => 'c
`

val _ = Hol_datatype`
  peg = <| start : ('a,'b,'c,'e) pegsym ;
           rules : 'b inf |-> ('a,'b,'c,'e) pegsym ;
           cf : 'e -> 'a tok |>
`

val (peg_eval_rules, peg_eval_ind, peg_eval_cases) = Hol_reln`
  (∀s c. peg_eval G (s, empty c) (SOME(s, c))) ∧
  (∀n r s f.
       n ∈ FDOM G.rules ∧ peg_eval G (s, G.rules ' n) (SOME(r,c)) ⇒
       peg_eval G (s, nt n f) (SOME(r, f c))) ∧
  (∀n s f.
       n ∈ FDOM G.rules ∧ peg_eval G (s, G.rules ' n) NONE ⇒
       peg_eval G (s, nt n f) NONE) ∧
  (∀h t f. peg_eval G (h::t, any f) (SOME (t, f (G.cf h) h))) ∧
  (∀f. peg_eval G ([], any f) NONE) ∧
  (∀h e t f. G.cf e = h ⇒ peg_eval G (e::t, tok h f) (SOME(t, f e))) ∧
  (∀h e t f. G.cf e ≠ h ⇒ peg_eval G (e::t, tok h f) NONE) ∧
  (∀h f. peg_eval G ([], tok h f) NONE) ∧
  (∀e s c. peg_eval G (s, e) NONE ⇒ peg_eval G (s, not e c) (SOME(s,c))) ∧
  (∀e s s' c. peg_eval G (s, e) (SOME s') ⇒ peg_eval G (s, not e c) NONE)  ∧
  (∀e1 e2 s f. peg_eval G (s, e1) NONE ⇒ peg_eval G (s, seq e1 e2 f) NONE)  ∧
  (∀e1 e2 s0 s1 c1 f.
     peg_eval G (s0, e1) (SOME (s1, c1)) ∧ peg_eval G (s1, e2) NONE ⇒
     peg_eval G (s0, seq e1 e2 f) NONE) ∧
  (∀e1 e2 s0 s1 s2 c1 c2 f.
     peg_eval G (s0, e1) (SOME(s1, c1)) ∧
     peg_eval G (s1, e2) (SOME(s2, c2)) ⇒
     peg_eval G (s0, seq e1 e2 f) (SOME(s2, f c1 c2))) ∧
  (∀e1 e2 s f.
     peg_eval G (s, e1) NONE ∧ peg_eval G (s, e2) NONE ⇒
     peg_eval G (s, choice e1 e2 f) NONE) ∧
  (∀e1 e2 s s' f c.
     peg_eval G (s, e1) (SOME(s',c)) ⇒
     peg_eval G (s, choice e1 e2 f) (SOME(s', f (INL c)))) ∧
  (∀e1 e2 s s' f c.
     peg_eval G (s, e1) NONE ∧ peg_eval G (s, e2) (SOME(s',c)) ⇒
     peg_eval G (s, choice e1 e2 f) (SOME(s',f (INR c))))  ∧
  (∀e f s s1 list.
     peg_eval_list G (s, e) (s1,list) ⇒
     peg_eval G (s, rpt e f) (SOME(s1, f list))) ∧
  (∀e s. peg_eval G (s, e) NONE ⇒ peg_eval_list G (s, e) (s,[])) ∧
  (∀e s0 s1 s2 c cs.
     peg_eval G (s0, e) (SOME(s1,c)) ∧
     peg_eval_list G (s1, e) (s2,cs) ⇒
     peg_eval_list G (s0, e) (s2,c::cs))
`;

val ind' = theorem "peg_eval_strongind"
             |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
             |> Q.SPECL [`G`, `\es0 r. P1 (FST es0) (SND es0) r`,
                         `\es0 sr. P2 (FST es0) (SND es0) (FST sr) (SND sr)`]
             |> SIMP_RULE (srw_ss()) []

open rich_listTheory
val peg_eval_suffix0 = prove(
  ``(∀s0 e sr. peg_eval G (s0,e) sr ⇒ ∀s r. sr = SOME (s,r) ⇒ IS_SUFFIX s0 s) ∧
    ∀s0 e s rl. peg_eval_list G (s0,e) (s,rl) ⇒ IS_SUFFIX s0 s``,
  HO_MATCH_MP_TAC ind' THEN SRW_TAC [][IS_SUFFIX_compute, IS_PREFIX_APPEND3,
                                       IS_PREFIX_REFL] THEN
  METIS_TAC [IS_PREFIX_TRANS]);

(* Theorem 3.1 *)
val peg_eval_suffix = save_thm(
  "peg_eval_suffix",
  peg_eval_suffix0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [])

(* Theorem 3.2 *)
val peg_deterministic = store_thm(
  "peg_deterministic",
  ``(∀s0 e sr. peg_eval G (s0,e) sr ⇒ ∀sr'. peg_eval G (s0,e) sr' ⇔ sr' = sr) ∧
    ∀s0 e s rl. peg_eval_list G (s0,e) (s,rl) ⇒
                ∀srl'. peg_eval_list G (s0,e) srl' ⇔ srl' = (s,rl)``,
  HO_MATCH_MP_TAC ind' THEN SRW_TAC [][] THEN
  ONCE_REWRITE_TAC [peg_eval_cases] THEN SRW_TAC [][]);

open lcsymtacs
(* Lemma 3.3 *)
val peg_badrpt = store_thm(
  "peg_badrpt",
  ``peg_eval G (s0,e) (SOME(s0,r)) ⇒ ∀r. ¬peg_eval G (s0, rpt e f) r``,
  strip_tac >> simp[Once peg_eval_cases] >> map_every qx_gen_tac [`s1`, `l`] >>
  disch_then (assume_tac o MATCH_MP (CONJUNCT2 peg_deterministic)) >>
  `peg_eval_list G (s0,e) (s1,r::l)`
    by METIS_TAC [last (peg_eval_rules |> SPEC_ALL |> CONJUNCTS)] >>
  pop_assum mp_tac >> simp[]);

val (peg0_rules, peg0_ind, peg0_cases) = Hol_reln`
  (∀c. peg0 G (empty c)) ∧

  (* any *)
  (∀f. peggt0 G (any f)) ∧
  (∀f. pegfail G (any f)) ∧

  (* tok *)
  (∀t f. peggt0 G (tok t f)) ∧
  (∀t f. pegfail G (tok t f)) ∧

  (* rpt *)
  (∀e f. pegfail G e ⇒ peg0 G (rpt e f)) ∧
  (∀e f. peggt0 G e ⇒ peggt0 G (rpt e f)) ∧

  (* nt rules *)
  (∀n f. n ∈ FDOM G.rules ∧ peg0 G (G.rules ' n) ⇒
         peg0 G (nt n f)) ∧
  (∀n f. n ∈ FDOM G.rules ∧ peggt0 G (G.rules ' n) ⇒
         peggt0 G (nt n f)) ∧
  (∀n f. n ∈ FDOM G.rules ∧ pegfail G (G.rules ' n) ⇒
         pegfail G (nt n f)) ∧

  (* seq rules *)
  (∀e1 e2 f. pegfail G e1 ∨ (peg0 G e1 ∧ pegfail G e2) ∨
             (peggt0 G e1 ∧ pegfail G e2) ⇒
             pegfail G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∧ (peg0 G e2 ∨ peggt0 G e2) ∨
             (peg0 G e1 ∨ peggt0 G e1) ∧ peggt0 G e2 ⇒
             peggt0 G (seq e1 e2 f)) ∧
  (∀e1 e2 f. peg0 G e1 ∧ peg0 G e2 ⇒ peg0 G (seq e1 e2 f)) ∧

  (* choice rules *)
  (∀e1 e2 f. peg0 G e1 ∨ (pegfail G e1 ∧ peg0 G e2) ⇒
             peg0 G (choice e1 e2 f)) ∧
  (∀e1 e2 f. pegfail G e1 ∧ pegfail G e2 ⇒ pegfail G (choice e1 e2 f)) ∧
  (∀e1 e2 f. peggt0 G e1 ∨ (pegfail G e1 ∧ peggt0 G e2) ⇒
             peggt0 G (choice e1 e2 f)) ∧

  (* not *)
  (∀e c. pegfail G e ⇒ peg0 G (not e c)) ∧
  (∀e c. peg0 G e ∨ peggt0 G e ⇒ pegfail G (not e c))
`;

val peg_eval_suffix' = store_thm(
  "peg_eval_suffix'",
  ``peg_eval G (s0,e) (SOME(s,c)) ⇒
    s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0``,
  strip_tac >> imp_res_tac peg_eval_suffix >> Cases_on `s0 = s` >- simp[] >>
  fs[IS_SUFFIX_compute] >>
  imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >>
  strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]);

val peg_eval_list_suffix' = store_thm(
  "peg_eval_list_suffix'",
  ``peg_eval_list G (s0, e) (s,rl) ⇒
    s0 = s ∨ IS_SUFFIX s0 s ∧ LENGTH s < LENGTH s0``,
  strip_tac >> imp_res_tac peg_eval_suffix >> Cases_on `s0 = s` >- simp[] >>
  fs[IS_SUFFIX_compute] >> imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
  qsuff_tac `LENGTH s ≠ LENGTH s0` >- (strip_tac >> decide_tac) >> strip_tac >>
  metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]);


fun rule_match th = FIRST (List.mapPartial (total MATCH_MP_TAC)
                                           (th |> SPEC_ALL |> CONJUNCTS))

val lemma4_1a0 = prove(
  ``(∀s0 e r. peg_eval G (s0, e) r ⇒
              (∀c. r = SOME(s0,c) ⇒ peg0 G e) ∧
              (r = NONE ⇒ pegfail G e) ∧
              (∀s c. r = SOME(s,c) ∧ LENGTH s < LENGTH s0 ⇒ peggt0 G e)) ∧
    (∀s0 e s rl. peg_eval_list G (s0,e) (s,rl) ⇒
                 (s0 = s ⇒ pegfail G e) ∧
                 (LENGTH s < LENGTH s0 ⇒ peggt0 G e))``,
  ho_match_mp_tac ind' >> simp[peg0_rules] >> rpt conj_tac
  >- (rpt strip_tac >> imp_res_tac peg_eval_suffix' >> fs[peg0_rules])
  >- (rpt strip_tac >> rule_match peg0_rules >>
      imp_res_tac peg_eval_suffix' >> fs[] >> rw[] >>
      full_simp_tac (srw_ss() ++ ARITH_ss) [])
  >- (rpt strip_tac >> rule_match peg0_rules >>
      imp_res_tac peg_eval_suffix' >> fs[] >> rw[] >>
      full_simp_tac (srw_ss() ++ ARITH_ss) []) >>
  rpt strip_tac
  >- (first_x_assum match_mp_tac >> rw[] >>
      imp_res_tac peg_eval_suffix >> fs[IS_SUFFIX_compute] >>
      imp_res_tac IS_PREFIX_LENGTH >> fs[] >>
      `LENGTH s = LENGTH s0'` by decide_tac >>
      metis_tac [IS_PREFIX_LENGTH_ANTI, LENGTH_REVERSE, REVERSE_REVERSE]) >>
  imp_res_tac peg_eval_suffix' >- rw[] >>
  imp_res_tac peg_eval_list_suffix' >- rw[] >>
  asm_simp_tac (srw_ss() ++ ARITH_ss) [])

val lemma4_1a = lemma4_1a0 |> SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]

val (wfpeg_rules, wfpeg_ind, wfpeg_cases) = Hol_reln`
  (∀n f. n ∈ FDOM G.rules ∧ wfpeg G (G.rules ' n) ⇒ wfpeg G (nt n f)) ∧
  (∀c. wfpeg G (empty c)) ∧
  (∀f. wfpeg G (any f)) ∧
  (∀t f. wfpeg G (tok t f)) ∧
  (∀e c. wfpeg G e ⇒ wfpeg G (not e c)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ (peg0 G e1 ⇒ wfpeg G e2) ⇒
             wfpeg G (seq e1 e2 f)) ∧
  (∀e1 e2 f. wfpeg G e1 ∧ wfpeg G e2 ⇒ wfpeg G (choice e1 e2 f)) ∧
  (∀e f. wfpeg G e ∧ ¬peg0 G e ⇒ wfpeg G (rpt e f))
`

val subexprs_def = Define`
  (subexprs (any f1) = { any f1 }) ∧
  (subexprs (empty c) = { empty c }) ∧
  (subexprs (tok t f2) = { tok t f2 }) ∧
  (subexprs (nt s f) = { nt s f }) ∧
  (subexprs (not e c) = not e c INSERT subexprs e) ∧
  (subexprs (seq e1 e2 f3) = seq e1 e2 f3 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (choice e1 e2 f4) =
    choice e1 e2 f4 INSERT subexprs e1 ∪ subexprs e2) ∧
  (subexprs (rpt e f5) = rpt e f5 INSERT subexprs e)
`
val _ = export_rewrites ["subexprs_def"]


val subexprs_included = store_thm(
  "subexprs_included",
  ``e ∈ subexprs e``,
  Induct_on `e` >> srw_tac[][subexprs_def] )

val Gexprs_def = Define`
  Gexprs G = BIGUNION (IMAGE subexprs (G.start INSERT FRANGE G.rules))
`

val wfG_def = Define`wfG G ⇔ ∀e. e ∈ Gexprs G ⇒ wfpeg G e`;

val IN_subexprs_TRANS = store_thm(
  "IN_subexprs_TRANS",
  ``∀a b c. a ∈ subexprs b ∧ b ∈ subexprs c ⇒ a ∈ subexprs c``,
  Induct_on `c` >> simp[] >> rpt strip_tac >> fs[] >> metis_tac[]);

val Gexprs_subexprs = store_thm(
  "Gexprs_subexprs",
  ``e ∈ Gexprs G ⇒ subexprs e ⊆ Gexprs G``,
  simp_tac (srw_ss() ++ DNF_ss) [Gexprs_def, pred_setTheory.SUBSET_DEF] >>
  strip_tac >> metis_tac [IN_subexprs_TRANS]);

val IN_Gexprs_E = store_thm(
  "IN_Gexprs_E",
  ``(not e c ∈ Gexprs G ⇒ e ∈ Gexprs G) ∧
    (seq e1 e2 f ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
    (choice e1 e2 f2 ∈ Gexprs G ⇒ e1 ∈ Gexprs G ∧ e2 ∈ Gexprs G) ∧
    (rpt e f3 ∈ Gexprs G ⇒ e ∈ Gexprs G)``,
  rpt strip_tac >> imp_res_tac Gexprs_subexprs >> fs[] >>
  metis_tac [pred_setTheory.SUBSET_DEF, subexprs_included]);

val pair_CASES = pairTheory.pair_CASES
val option_CASES = optionTheory.option_nchotomy
val list_CASES = listTheory.list_CASES

val reducing_peg_eval_makes_list = prove(
  ``(∀s. LENGTH s < n ⇒ ∃r. peg_eval G (s, e) r) ∧ ¬peg0 G e ∧ LENGTH s0 < n ⇒
    ∃s' rl. peg_eval_list G (s0,e) (s',rl)``,
  strip_tac >> completeInduct_on `LENGTH s0` >> rw[] >>
  full_simp_tac (srw_ss() ++ DNF_ss ++ ARITH_ss) [] >>
  `peg_eval G (s0,e) NONE ∨ ∃s1 c. peg_eval G (s0,e) (SOME(s1,c))`
    by metis_tac [pair_CASES, option_CASES]
  >- metis_tac [peg_eval_rules] >>
  `s0 ≠ s1` by metis_tac [lemma4_1a] >>
  `LENGTH s1 < LENGTH s0` by metis_tac [peg_eval_suffix'] >>
  metis_tac [peg_eval_rules]);


val peg_eval_total = prove(
  ``wfG G ⇒ ∀s e. e ∈ Gexprs G ⇒ ∃r. peg_eval G (s,e) r``,
  simp[wfG_def] >> strip_tac >> gen_tac >>
  completeInduct_on `LENGTH s` >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> rpt strip_tac >>
  `wfpeg G e` by metis_tac[] >>
  Q.UNDISCH_THEN `e ∈ Gexprs G` mp_tac >>
  pop_assum mp_tac >> qid_spec_tac `e` >>
  Induct_on `wfpeg` >> rw[]
  >- ((* nt *)
      qsuff_tac `G.rules ' n ∈ Gexprs G`
      >- metis_tac [peg_eval_rules, option_CASES, pair_CASES] >>
      asm_simp_tac (srw_ss() ++ DNF_ss) [Gexprs_def, FRANGE_DEF] >>
      metis_tac [subexprs_included])
  >- (* empty *) metis_tac [peg_eval_rules]
  >- (* any *) metis_tac [peg_eval_rules, list_CASES]
  >- (* tok *) metis_tac [peg_eval_rules, list_CASES]
  >- (* not *) metis_tac [peg_eval_rules, optionTheory.option_nchotomy,
                          IN_Gexprs_E]
  >- ((* seq *) Q.MATCH_ASSUM_ABBREV_TAC `seq e1 e2 f ∈ Gexprs G` >>
      markerLib.RM_ALL_ABBREVS_TAC >>
      `e1 ∈ Gexprs G` by imp_res_tac IN_Gexprs_E >>
      `peg_eval G (s,e1) NONE ∨ ∃s' c. peg_eval G (s,e1) (SOME(s',c))`
        by metis_tac[option_CASES, pair_CASES]
      >- metis_tac [peg_eval_rules] >>
      Cases_on `s' = s`
      >- (`peg0 G e1` by metis_tac [lemma4_1a] >>
          `e2 ∈ Gexprs G` by imp_res_tac IN_Gexprs_E >>
          metis_tac [peg_eval_rules, option_CASES, pair_CASES]) >>
      `LENGTH s' < LENGTH s` by metis_tac [peg_eval_suffix'] >>
      `∃r'. peg_eval G (s',e2) r'` by metis_tac [IN_Gexprs_E] >>
      metis_tac [option_CASES, pair_CASES, peg_eval_rules])
  >- (* choice *)
     metis_tac [peg_eval_rules, option_CASES, IN_Gexprs_E, pair_CASES] >>
  (* rpt *) imp_res_tac IN_Gexprs_E >>
  `peg_eval G (s, e) NONE ∨ ∃s' c. peg_eval G (s,e) (SOME (s',c))`
    by metis_tac [option_CASES, pair_CASES]
  >- (`peg_eval_list G (s,e) (s,[])` by metis_tac [peg_eval_rules] >>
      metis_tac [peg_eval_rules]) >>
  `s' ≠ s` by metis_tac [lemma4_1a] >>
  `LENGTH s' < LENGTH s` by metis_tac [peg_eval_suffix'] >>
  metis_tac [peg_eval_rules, reducing_peg_eval_makes_list])





(*
val _ = Hol_datatype`ftok = Plus | Times | Number | LParen | RParen`

val _ = Hol_datatype`etok = EPlus | ETimes | ENumber of num | ELParen | ERParen`

val categorise_def = Define`
  categorise EPlus = mkTok Plus ∧
  categorise ETimes = mkTok Times ∧
  categorise (ENumber n) = mkTok Number ∧
  categorise ELParen = mkTok LParen ∧
  categorise ERParen = mkTok RParen
`;

local open stringTheory in end

val _ = Hol_datatype `
  expr = XN of num
       | XPlus of expr => expr
       | XTimes of expr => expr
       | XList of expr list`;

val _ = overload_on("mkTok", ``mk_finite_image``)


val ty = ty_antiq ``:(ftok, string, expr, etok) pegsym``
val nrule =
  ``tok (mkTok Number) (\e. case e of ENumber n => XN n) : ^ty``
val paren_rule =
  ``seq (tok (mkTok LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok (mkTok RParen) (K (XN 0))) (\a b. a))
        (\a b. b) : ^ty``

val termpair =
  ``(INL "term" : string inf,
     choice ^nrule ^paren_rule (\s. case s of INL e => e | INR e => e))``

val factorpair = ``(INL "factor" : string inf,
                    seq (rpt (seq (nt (INL "term") I)
                                            (tok (mkTok Times) (K ARB))
                                            (\a b. a))
                                       XList)
                                  (nt (INL "term") I)
                                  (\a b.
                                    case a of
                                      XList (h::t) => FOLDL XTimes h (t ++ [b])
                                    | _ => b) : ^ty)``

val exprpair = ``(INL "expr" : string inf,
                  seq (rpt (seq (nt (INL "factor") I)
                                        (tok (mkTok Plus) (K ARB))
                                        (\a b. a))
                                   XList)
                              (nt (INL "factor") I)
                              (\a b.
                                case a of
                                  XList (h::t) => FOLDL XPlus h (t ++ [b])
                                | _ => b) : ^ty)``

val rules = ``FEMPTY |+ ^exprpair |+ ^factorpair |+ ^termpair``

val G = ``<| start := INL "expr"; rules := ^rules; cf := categorise |>``

val testexp = ``[ENumber 3; EPlus; ENumber 4; ETimes; ENumber 5]``

val [emptyI,ntI0,anyOKI,anyFAIL,tokOK,tokFAIL1,tokFAIL2,notOK, notFAIL,
     seqFAIL1, seqFAIL2, seqOK0, choiceFAIL, choiceOK1, choiceOK2,
     rptOK1, list1, list2] = peg_eval_rules |> SPEC_ALL |> CONJUNCTS

val seqOK = let
  val th0 = seqOK0 |> SPEC_ALL |> UNDISCH
  val c = th0 |> concl
  fun check t = let
    val (f, args) = strip_comb t
  in
    not (null args) andalso is_var f
  end
  val fxy = find_term check c
  val th = REWRITE_RULE [ASSUME (mk_eq(fxy, mk_var("x", type_of fxy)))] th0
in
  DISCH_ALL th |> REWRITE_RULE [AND_IMP_INTRO] |> GEN_ALL
end

val ntI = ntI0 |> SPEC_ALL
               |> Q.INST [`f` |-> `I`]
               |> SIMP_RULE (srw_ss()) []

val _ = overload_on ("G", G)

val ok = prove(
  ``peg_eval ^G (nt ^G.start I,^testexp)
                (SOME([], XPlus (XN 3) (XTimes (XN 4) (XN 5))))``,
  SIMP_TAC (srw_ss()) [] THEN
  MATCH_MP_TAC ntI THEN
  SIMP_TAC (srw_ss()) [finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  MATCH_MP_TAC seqOK THEN SIMP_TAC (srw_ss()) []

  FIRST (List.mapPartial (Lib.total MATCH_MP_TAC) (CONJUNCTS peg_eval_rules))




*)
val _ = export_theory()
