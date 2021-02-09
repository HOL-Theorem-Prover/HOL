open HolKernel boolLib bossLib BasicProvers finite_mapSyntax
open ASCIInumbersTheory simpleSexpTheory
open pegTheory pegexecTheory;
open simpleSexpPEGTheory

open listTheory pairTheory stringTheory

val _ = new_theory"simpleSexpParse"

val _ = temp_delsimps ["NORMEQ_CONV"]

(* TODO: move *)

val MAP_DROP = Q.store_thm("MAP_DROP",
  `∀l i. MAP f (DROP i l) = DROP i (MAP f l)`,
  Induct \\ simp[DROP_def] \\ rw[]);

val MAP_FRONT = Q.store_thm("MAP_FRONT",
  `∀ls. ls ≠ [] ⇒ MAP f (FRONT ls) = FRONT (MAP f ls)`,
  Induct \\ simp[] \\ Cases_on`ls`\\fs[])

val option_sequence_def = Define`
  option_sequence [] = SOME [] ∧
  option_sequence (h::t) =
    OPTION_MAP2 CONS h (option_sequence t)`;
val _ = export_rewrites["option_sequence_def"];

val option_sequence_SOME = Q.store_thm("option_sequence_SOME",
  `∀l1 l2.
   (option_sequence l1 = SOME l2 ⇔
    EVERY IS_SOME l1 ∧ l2 = MAP THE l1)`,
  Induct \\ rw[EQ_IMP_THM] \\ rw[]
  \\ fs[optionTheory.IS_SOME_EXISTS]);

val isDigit_HEX = Q.store_thm("isDigit_HEX",
  `∀n. n < 10 ⇒ isDigit (HEX n)`,
  simp[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac \\ EVAL_TAC
  \\ strip_tac \\ var_eq_tac \\ EVAL_TAC);

Theorem EVERY_isDigit_n2s: ∀n. EVERY isDigit (n2s 10 HEX n)
Proof
  rw[n2s_def,EVERY_MAP]
  \\ irule EVERY_MONOTONIC
  \\ qexists_tac‘$> 10’
  \\ simp[]
  \\ metis_tac[isDigit_HEX, arithmeticTheory.GREATER_DEF,
               numposrepTheory.n2l_BOUND,DECIDE“0n < 10”]
QED

Theorem EVERY_isDigit_num_to_dec_string:
  EVERY isDigit (num_to_dec_string n)
Proof
  rw[num_to_dec_string_def,EVERY_isDigit_n2s]
QED

val n2s_not_null = Q.store_thm("n2s_not_null",
  `∀n. ¬NULL(n2s 10 HEX n)`,
  rw[n2s_def,NULL_EQ]
  \\ strip_tac
  \\ qspecl_then[`10`,`n`]mp_tac numposrepTheory.LENGTH_n2l
  \\ simp[]);

val num_to_dec_string_not_null = Q.store_thm("num_to_dec_string_not_null",
  `∀n. ¬NULL(toString n)`,
  rw[num_to_dec_string_def,n2s_not_null]);

val l2n_APPEND = Q.store_thm("l2n_APPEND",
  `∀l1 l2. l2n b (l1 ++ l2) =
           l2n b l1 + b ** (LENGTH l1) * l2n b l2`,
  Induct \\ simp[numposrepTheory.l2n_def,arithmeticTheory.EXP]);

val isDigit_ORD_MOD_10 = Q.store_thm("isDigit_ORD_MOD_10",
  `isDigit x ⇒ (ORD x - 48) < 10`,
  EVAL_TAC \\ DECIDE_TAC);

val isDigit_UNHEX_alt = Q.store_thm("isDigit_UNHEX_alt",
  `isDigit h ⇒
   (combin$C $- 48 o ORD) h = UNHEX h`,
  simp[isDigit_def] \\ rw[]
  \\ Cases_on`h` \\ fs[]
  \\ Cases_on`n = 57` \\ fs[UNHEX_def]
  \\ Cases_on`n = 56` \\ fs[UNHEX_def]
  \\ Cases_on`n = 55` \\ fs[UNHEX_def]
  \\ Cases_on`n = 54` \\ fs[UNHEX_def]
  \\ Cases_on`n = 53` \\ fs[UNHEX_def]
  \\ Cases_on`n = 52` \\ fs[UNHEX_def]
  \\ Cases_on`n = 51` \\ fs[UNHEX_def]
  \\ Cases_on`n = 50` \\ fs[UNHEX_def]
  \\ Cases_on`n = 49` \\ fs[UNHEX_def]
  \\ Cases_on`n = 48` \\ fs[UNHEX_def]);

val s2n_UNHEX_alt = Q.store_thm("s2n_UNHEX_alt",
  `∀ls. EVERY isDigit ls ⇒
    s2n 10 (combin$C $- 48 o ORD) ls = s2n 10 UNHEX ls`,
  simp[s2n_def]
  \\ Induct
  \\ simp[numposrepTheory.l2n_def,l2n_APPEND]
  \\ rw[] \\ simp[GSYM isDigit_UNHEX_alt,isDigit_ORD_MOD_10]);

val num_to_dec_string_eq_cons = Q.store_thm("num_to_dec_string_eq_cons",
  `num_to_dec_string n = h::t ⇒
   n = UNHEX h * 10 ** LENGTH t + num_from_dec_string t`,
  rw[num_to_dec_string_def,num_from_dec_string_def]
  \\ fs[n2s_def]
  \\ qspecl_then[`10`,`n`]mp_tac numposrepTheory.n2l_BOUND
  \\ rw[]
  \\ qspecl_then[`10`,`n`]mp_tac numposrepTheory.l2n_n2l \\ rw[]
  \\ Q.ISPEC_THEN`n2l 10 n`FULL_STRUCT_CASES_TAC SNOC_CASES
  \\ fs[EVERY_SNOC] \\ rpt var_eq_tac
  \\ simp[UNHEX_HEX]
  \\ simp[SNOC_APPEND,l2n_APPEND,numposrepTheory.l2n_def]
  \\ simp[s2n_def,MAP_MAP_o]
  \\ AP_TERM_TAC
  \\ fs[LIST_EQ_REWRITE,EL_MAP,EVERY_MEM,MEM_EL,PULL_EXISTS]
  \\ rw[] \\ res_tac \\ simp[UNHEX_HEX]);

Theorem peg_eval_list_tok_nil:
  ∀ls. (ls = [] ∨ ¬ P(FST(HD ls))) ⇒
       peg_eval_list G (ls, tok P a) (ls,[])
Proof
  rw[Once peg_eval_list,peg_eval_tok_NONE,EVERY_MEM]
  >- simp[Once peg_eval_cases]
  \\ Cases_on`ls` \\ fs[]
  >- simp[Once peg_eval_cases]
  \\ Cases_on`h` \\ fs[] \\ simp[Once peg_eval_cases]
QED

Theorem peg_eval_list_tok_imp_every:
  ∀ls r z.
    peg_eval_list G (ls, tok P a) (r,z) ⇒
    ∃l. ls = l ++ r ∧ EVERY (P o FST) l ∧ (¬NULL r ⇒ ¬P (FST(HD r)))
Proof
  Induct \\ rw[Once peg_eval_list,NULL_EQ,peg_eval_tok_SOME]
  >- (rename [‘isFailure fr’] >> Cases_on ‘fr’ >> gs[peg_eval_tok_NONE])
  \\ first_x_assum $ drule_then strip_assume_tac
  \\ gvs[NULL_EQ]
QED

Theorem peg_eval_list_tok_every_imp:
  ∀ls x rst. EVERY (P o FST) ls ∧ ¬ (P o FST) x ⇒
             peg_eval_list G (ls ++ [x] ++ rst, tok P a) ([x] ++ rst, MAP a ls)
Proof
  Induct \\ simp[] \\ simp[Once peg_eval_list]
  >- simp[EXISTS_result, peg_eval_tok_NONE]
  \\ rw[]
  \\ simp[peg_eval_tok_SOME]
  \\ gvs[]
QED

val FOLDR_STRCAT_destSXSYM = Q.prove(
  `∀ls. FOLDR (λs a. STRCAT (destSXSYM s) a) "" (MAP (λc. SX_SYM (STRING c "")) ls) = ls`,
  Induct >> simp[destSXSYM_def]);

val FOLDR_STRCAT_destSXSYM_FST = Q.prove(
  `∀ls. FOLDR (λs a. STRCAT (destSXSYM s) a) "" (MAP (λ(c,l). SX_SYM (STRING c "")) ls) = MAP FST ls`,
  Induct >> simp[destSXSYM_def,FORALL_PROD]);

(* -- *)

val parse_sexp_def = Define`
  parse_sexp s =
    OPTION_BIND (pegparse sexpPEG s)
      (λ(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest=[])) (SOME sx))`;

val escape_string_def = Define`
  escape_string s =
    case s of
    | "" => ""
    | #"\\"::s => "\\\\"++(escape_string s)
    | #"\""::s => "\\\""++(escape_string s)
    | c::s => c::(escape_string s)`;

val print_space_separated_def = Define`
  (print_space_separated [] = "") ∧
  (print_space_separated [x] = x) ∧
  (print_space_separated (x::xs) = x ++ " " ++ print_space_separated xs)`;

val print_space_separated_cons = Q.store_thm("print_space_separated_cons",
  `print_space_separated (x::xs) = x ++ (if NULL xs then "" else " " ++ print_space_separated xs)`,
  Cases_on`xs` \\ rw[print_space_separated_def]);

val strip_dot_def = Define`
  strip_dot x =
  case x of
  | SX_CONS a d =>
    let (ls,n) = strip_dot d in (a::ls,n)
  | SX_SYM s => if s = "nil" then ([],NONE) else ([],SOME x)
  | _ => ([],SOME x)`;
val strip_dot_ind = theorem"strip_dot_ind";

val strip_dot_strip_sxcons = Q.store_thm("strip_dot_strip_sxcons",
  `∀s ls. strip_sxcons s = SOME ls ⇔ strip_dot s = (ls,NONE)`,
  ho_match_mp_tac strip_sxcons_ind \\ rw[]
  \\ rw[Once strip_sxcons_def]
  \\ CASE_TAC \\ fs[]
  \\ TRY(simp[Once strip_dot_def] \\ rw[] \\ NO_TAC)
  \\ CONV_TAC(RAND_CONV(SIMP_CONV (srw_ss()) [Once strip_dot_def]))
  \\ simp[] \\ pairarg_tac \\ fs[] \\ rw[EQ_IMP_THM]);

val strip_dot_last_sizeleq = Q.store_thm("strip_dot_last_sizeleq",
  `∀x ls last. strip_dot x  = (ls,SOME last) ⇒ sexp_size last ≤ sexp_size x`,
  ho_match_mp_tac strip_dot_ind \\ rw[]
  \\ pop_assum mp_tac
  \\ simp[Once strip_dot_def]
  \\ CASE_TAC \\ fs[]
  \\ TRY(pairarg_tac \\ fs[])
  \\ rw[sexp_size_def] \\ simp[]
  \\ rw[sexp_size_def]);

val strip_dot_last_sizelt = Q.store_thm("strip_dot_last_sizelt",
  `∀x ls last. strip_dot x  = (ls,SOME last) ∧ ¬NULL ls ⇒ sexp_size last < sexp_size x`,
  ho_match_mp_tac strip_dot_ind \\ rw[]
  \\ qpat_x_assum`strip_dot x = _` mp_tac
  \\ simp[Once strip_dot_def]
  \\ CASE_TAC \\ fs[]
  \\ TRY(pairarg_tac \\ fs[])
  \\ rw[sexp_size_def] \\ simp[]
  \\ rw[sexp_size_def]
  \\ fs[]
  \\ TRY (spose_not_then strip_assume_tac \\ fs[] \\ rw[] \\ fs[] \\ NO_TAC)
  \\ qpat_x_assum`strip_dot x = _` mp_tac
  \\ simp[Once strip_dot_def]
  \\ CASE_TAC \\ fs[]
  \\ TRY(pairarg_tac \\ fs[])
  \\ rw[] \\ fs[]);

val strip_dot_MEM_sizelt = Q.store_thm("strip_dot_MEM_sizelt",
  `∀x ls n a. strip_dot x = (ls,n) ∧ MEM a ls ⇒ sexp_size a < sexp_size x`,
  ho_match_mp_tac strip_dot_ind \\ rw[]
  \\ qpat_x_assum`strip_dot x = _` mp_tac
  \\ simp[Once strip_dot_def]
  \\ CASE_TAC \\ fs[]
  \\ TRY(pairarg_tac \\ fs[])
  \\ rw[sexp_size_def] \\ fs[]
  \\ res_tac \\  simp[]);

val strip_dot_valid_sexp = Q.store_thm("strip_dot_valid_sexp",
  `∀x ls n. strip_dot x = (ls,n) ∧ valid_sexp x ⇒
    EVERY valid_sexp ls ∧ (case n of NONE => T | SOME last => valid_sexp last)`,
  ho_match_mp_tac strip_dot_ind \\ rw[]
  \\ qpat_x_assum`strip_dot x = _` mp_tac
  \\ simp[Once strip_dot_def]
  \\ CASE_TAC \\ fs[] \\ rw[] \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rw[]);

val print_sexp_def = tDefine"print_sexp"`
  (print_sexp (SX_SYM s) = s) ∧
  (print_sexp (SX_NUM n) = toString n) ∧
  (print_sexp (SX_STR s) = "\"" ++ escape_string s ++ "\"") ∧
  (print_sexp s =
   let (ls,n) = strip_dot s in
   case n of
   | NONE =>
     if LENGTH ls = 2 ∧ HD ls = SX_SYM "quote"
     then "'" ++ print_sexp (EL 1 ls)
     else "(" ++ print_space_separated (MAP print_sexp ls) ++ ")"
   | SOME last =>
       "(" ++ print_space_separated (MAP print_sexp ls) ++ " . " ++ print_sexp last ++ ")")`
  (WF_REL_TAC`measure sexp_size` >> rw[] >> simp[sexp_size_def] >>
   fs[Once strip_dot_def] >>
   pairarg_tac \\ fs[] \\ rw[sexp_size_def] \\ fs[]
   \\ imp_res_tac strip_dot_MEM_sizelt
   \\ imp_res_tac strip_dot_last_sizeleq
   \\ fsrw_tac[boolSimps.DNF_ss][] \\ simp[]
   \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rw[] \\ fs[]
   \\ res_tac \\ simp[]);

Theorem peg_eval_list_valid_symchars[local]:
  ∀cs. EVERY valid_symchar (MAP FST cs) ⇒
       peg_eval_list sexpPEG (cs,tok valid_symchar (λ(c,l). SX_SYM [c]))
                     ([],MAP (λc. SX_SYM [c]) (MAP FST cs))
Proof
  Induct >> simp[Once peg_eval_cases] >> simp[Once peg_eval_cases] >>
  strip_tac >> Cases_on `h` >> simp[]
QED

Theorem peg_eval_valid_symchars[local]:
  ∀cs. EVERY valid_symchar (MAP FST cs) ⇒
       peg_eval sexpPEG
                (cs,rpt (tok valid_symchar (λ(c,l). SX_SYM (STRING c "")))
                        (SX_SYM o FOLDR (λs a. STRCAT (destSXSYM s) a) []))
                (Success [] (SX_SYM (MAP FST cs)))
Proof
  rw[Once peg_eval_cases] >>
  drule peg_eval_list_valid_symchars >>
  metis_tac[FOLDR_STRCAT_destSXSYM]
QED

Theorem isFailure_eqn:
  isFailure r ⇔ ∃x y. r = Failure x y
Proof
  Cases_on ‘r’ >> simp[]
QED

Theorem isSuccess_eqn:
  isSuccess r ⇔ ∃x y. r = Success x y
Proof
  Cases_on ‘r’ >> simp[]
QED

Theorem sexpnum_never_symbol:
  ¬peg_eval sexpPEG (i0, nt (mkNT sxnt_sexpnum) I) (Success i (SX_SYM s))
Proof
  simp[Once peg_eval_cases, FDOM_sexpPEG, sexpPEG_applied, peg_eval_seq_SOME] >>
  rpt gen_tac >> rename [‘destSXCONS sxp’] >>
  Cases_on ‘sxp’ >> simp[destSXCONS_def]
QED

Theorem sexpdigit_nondigit_fails:
  ¬isDigit q ⇒
  (peg_eval sexpPEG ((q,r) :: rest, nt (mkNT sxnt_digit) I) res ⇔
     res = Failure r sexpPEG.tokFALSE)
Proof
  simp[Once peg_eval_cases, FDOM_sexpPEG, sexpPEG_applied, peg_eval_tok_SOME,
       peg_eval_tok_NONE, sloc_def]
QED

Theorem sexpnum_nondigit_fails:
  ¬isDigit q ⇒
  (peg_eval sexpPEG ((q,r) :: rest, nt (mkNT sxnt_sexpnum) I) res ⇔
     res = Failure r sexpPEG.tokFALSE)
Proof
  simp[Once peg_eval_cases, FDOM_sexpPEG, sexpPEG_applied,
       peg_eval_seq_SOME, sexpdigit_nondigit_fails, pnt_def] >>
  simp[peg_eval_seq_NONE, sexpdigit_nondigit_fails]
QED

Theorem seqtokP:
  peg_eval sexpPEG ((c,r) :: rest, seq (tok P f) p (λa b. b)) res ⇔
    if P c then peg_eval sexpPEG (rest,p) res
    else res = Failure r sexpPEG.tokFALSE
Proof
  simp[Once peg_eval_cases, SimpLHS] >>
  Cases_on ‘res’ >> simp[peg_eval_tok_NONE, peg_eval_tok_SOME, sloc_def] >>
  metis_tac[]
QED

Theorem seqtokeq:
  peg_eval sexpPEG ((c1,r) :: rest, seq (tokeq c2) p (λa b. b)) res ⇔
    if c1 = c2 then peg_eval sexpPEG (rest,p) res
    else res = Failure r sexpPEG.tokFALSE
Proof
  simp[seqtokP, tokeq_def] >> metis_tac[]
QED

Theorem seq_isSuccess_csimp:
  isSuccess r ⇒
  (peg_eval g (i0, seq p1 p2 f) r ⇔
     ∃i1 v1 i2 v2. peg_eval g (i0, p1) (Success i1 v1) ∧
                   peg_eval g (i1, p2) (Success i2 v2) ∧
                   r = Success i2 (f v1 v2))
Proof
  simp[Once peg_eval_cases, SimpLHS] >> Cases_on ‘r’ >> simp[] >> metis_tac[]
QED

Theorem seq_isFailure_csimp:
  isFailure r ⇒
  (peg_eval g (i0, seq p1 p2 f) r ⇔
     ∃r1. peg_eval g (i0, p1) r1 ∧
          (r1 = r ∨ ∃v1 i1. r1 = Success i1 v1 ∧ peg_eval g (i1, p2) r))
Proof
  simp[Once peg_eval_cases, SimpLHS] >> Cases_on ‘r’ >> dsimp[] >> metis_tac[]
QED

Theorem peg_eval_valid_symbol[local]:
  ∀s. valid_symbol (MAP FST s) ⇒
      peg_eval sexpPEG (s,sexpPEG.start) (Success [] (SX_SYM (MAP FST s)))
Proof
  Cases_on`s` >> simp[pnt_def] >>
  rename [‘isGraph (FST h)’] >>
  Cases_on‘h’ >> gvs[] >> rename [‘isGraph q’] >> strip_tac >>
  simp[peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied, ignoreR_def,
       peg_eval_seq_SOME, peg_eval_rpt, PULL_EXISTS] >>
  qexists_tac ‘[]’ >>
  simp[Once peg_eval_list, EXISTS_result, peg_eval_tok_SOME,
       peg_eval_tok_NONE] >>
  simp[pnt_def, peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied, ignoreL_def,
       peg_eval_seq_SOME, peg_eval_rpt, PULL_EXISTS] >>
  `¬isSpace q` by (strip_tac >> Cases_on `q` >> fs[isGraph_def]) >>
  simp[Once peg_eval_list, peg_eval_tok_SOME] >>
  simp[EXISTS_result, peg_eval_tok_NONE] >>
  simp[Once peg_eval_choicel_CONS, sexpnum_nondigit_fails] >>
  simp[AllCaseEqs(), rmax_EQ_Success] >> csimp[] >>
  simp[Once peg_eval_choicel_CONS, seqtokeq] >> csimp[] >>
  simp[AllCaseEqs(), rmax_EQ_Success] >> csimp[] >>
  simp[Once peg_eval_choicel_CONS, ignoreR_def, peg_eval_seq_SOME,
       tokeq_def, peg_eval_tok_SOME] >>
  csimp[seq_isFailure_csimp, seqtokP, AllCaseEqs(), rmax_EQ_Success] >>
  simp[Once peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME] >>
  csimp[seq_isFailure_csimp, seqtokP, AllCaseEqs(), rmax_EQ_Success] >>
  simp[Once peg_eval_choicel_CONS] >>
  simp[EXISTS_result, AllCaseEqs()] >>
  simp[peg_eval_NT_SOME] >>
  dsimp[FDOM_sexpPEG, sexpPEG_applied, peg_eval_seq_NONE, pnt_def,
        peg_eval_rpt, peg_eval_seq_SOME, peg_eval_tok_SOME,
        destSXSYM_def] >>
  drule peg_eval_valid_symchars >> simp[peg_eval_rpt]
QED

val valid_symbol_no_spaces = Q.store_thm("valid_symbol_no_spaces",
  `∀s. valid_symbol s ⇒ EVERY ($~ o isSpace) s`,
  Cases_on`s` \\ rw[valid_symbol_def]
  >- ( fs[isGraph_def,isSpace_def] )
  \\ Induct_on`t`
  \\ rw[]
  >- ( fs[isGraph_def,isSpace_def] ))

val peg_eval_list_num_to_dec_string_no_spaces = Q.prove(
  `peg_eval_list sexpPEG (map_loc (toString n) 0,tok isSpace ARB)
                             (map_loc (toString n) 0 ,[])`,
  match_mp_tac peg_eval_list_tok_nil
  \\ assume_tac EVERY_isDigit_num_to_dec_string
  \\ fs[EVERY_MEM] \\ rw[]
  \\ Cases_on`toString n` \\ fs[]
  \\ fs[isDigit_def,isSpace_def]
  \\ spose_not_then strip_assume_tac
  \\ fs[locationTheory.map_loc_def]
  \\ first_x_assum(qspec_then`h`mp_tac)
  \\ simp[]);

Theorem peg_eval_list_digits:
  ∀s. EVERY isDigit (MAP FST s) ∧ (rst ≠ [] ⇒ ¬ isDigit (FST (HD rst))) ⇒
      peg_eval_list sexpPEG (s ++ rst,nt(mkNT sxnt_digit) I)
                    (rst,MAP (SX_NUM o combin$C $- 48 o ORD) (MAP FST s))
Proof
  Induct \\ simp[Once peg_eval_list]
  >- (Cases_on ‘rst’ >> simp[]
      >- simp[Once peg_eval_cases, FDOM_sexpPEG,sexpPEG_applied,
              peg_eval_tok_SOME, peg_eval_tok_NONE] >>
      Cases_on ‘h’ >> simp[sexpdigit_nondigit_fails]) >>
  simp[FORALL_PROD] >> rw[] >>
  simp[peg_eval_NT_SOME] >>
  simp[FDOM_sexpPEG, sexpPEG_applied, peg_eval_tok_SOME]
QED

Theorem peg_eval_list_chars:
  ∀loc l1 l2.
    EVERY isPrint l1 ⇒
    escape_string l1 = MAP FST l2  ⇒
    peg_eval_list sexpPEG (l2 ++[(#"\"",loc)], nt (mkNT sxnt_strchar) I)
                  ([(#"\"",loc)],MAP (λc. SX_SYM [c]) l1)
Proof
  strip_tac
  \\ Induct \\ simp[Once escape_string_def]
  >- (
    simp[Once peg_eval_list]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS,pnt_def, EXISTS_result, AllCaseEqs()]
    \\ simp[ignoreL_def,peg_eval_seq_NONE,tokeq_def,peg_eval_tok_NONE,
            peg_eval_tok_SOME]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE] \\ metis_tac[])
  \\ rw[] \\ fs[] \\ simp[Once peg_eval_list]
  \\ Cases_on`l2` \\ fs[]
  THENL[(Cases_on`t` \\ fs[] \\ `MAP FST t' = MAP FST t'` by simp[]),
        (Cases_on`t` \\ fs[] \\ `MAP FST t' = MAP FST t'` by simp[]),
        `MAP FST t = MAP FST t` by simp[]]
  \\ first_x_assum $ dxrule_then $ irule_at (Pos last)
  \\ rpt (rename [‘FST p’] \\ Cases_on ‘p’ \\ gvs[])
  \\ simp[peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied,
          peg_eval_choicel_CONS, tokeq_def, peg_eval_tok_SOME,
          ignoreL_def, peg_eval_seq_SOME] >~
  [‘h ≠ #"\\"’, ‘h ≠ #"\""’]
  >- (simp[EXISTS_result, AllCaseEqs(), peg_eval_seq_NONE, peg_eval_tok_NONE,
           EXISTS_OR_THM, LEFT_EXISTS_AND_THM]
      \\ simp[peg_eval_NT_SOME, pnt_def, FDOM_sexpPEG, sexpPEG_applied,
              peg_eval_tok_SOME])
  \\ disj1_tac
  \\ simp[peg_eval_NT_SOME, pnt_def, FDOM_sexpPEG, sexpPEG_applied,
          peg_eval_tok_SOME, peg_eval_choicel_CONS, tokeq_def,
          EXISTS_result, peg_eval_tok_NONE]
QED

val nt_rank_def = Define`
  (nt_rank sxnt_normstrchar = 0n) ∧
  (nt_rank sxnt_escapedstrchar = 0) ∧
  (nt_rank sxnt_strchar = 0) ∧
  (nt_rank sxnt_strcontents = 1) ∧
  (nt_rank sxnt_sexpseq = 2) ∧
  (nt_rank sxnt_sexp0 = 3) ∧
  (nt_rank sxnt_sexp = 4) ∧
  (nt_rank _ = 0)`;
val _ = export_rewrites["nt_rank_def"];

val dest_quote_def = Define`
  (dest_quote (SX_CONS q (SX_CONS a n)) =
     if q = SX_SYM "quote" ∧ n = nil then
       SOME a
     else NONE) ∧
  dest_quote _ = NONE`;
val _ = export_rewrites["dest_quote_def"];

val dest_quote_sizelt = Q.store_thm("dest_quote_sizelt",
  `∀sx a. dest_quote sx = SOME a ⇒ sexp_size a < sexp_size sx`,
  ho_match_mp_tac(theorem"dest_quote_ind")
  \\ rw[] \\ rw[sexp_size_def]);

val print_nt_def = tDefine"print_nt"`
  (print_nt sxnt_normstrchar (SX_SYM [c]) =
     if isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\" then SOME [c] else NONE) ∧
  (print_nt sxnt_normstrchar _ = NONE) ∧
  (print_nt sxnt_escapedstrchar (SX_SYM [c]) =
    if c = #"\\" ∨ c = #"\"" then SOME [c] else NONE) ∧
  (print_nt sxnt_strchar (SX_SYM [c]) =
    if c = #"\\" ∨ c = #"\"" then SOME (#"\\"::[c]) else
    if isPrint c then SOME [c] else NONE) ∧
  (print_nt sxnt_strcontents (SX_STR str) =
    FOLDR (λc a. OPTION_MAP2 (++) (print_nt sxnt_strchar (SX_SYM [c])) a)
          (SOME "") str) ∧
  (print_nt sxnt_sexpsym (SX_SYM str) =
   if ¬NULL str ∧ valid_first_symchar (HD str) ∧ EVERY valid_symchar (TL str)
   then SOME str
   else NONE) ∧
  (print_nt sxnt_sexpsym _ = NONE) ∧
  (print_nt sxnt_sexpseq sx =
   let (ls,n) = strip_dot sx in
   OPTION_BIND (option_sequence (MAP (print_nt sxnt_sexp0) ls))
   (λl1. OPTION_MAP (λl2. print_space_separated l1 ++ l2 ++ ")")
     (case n of NONE => SOME ""
      | SOME d =>
        if NULL ls then NONE else
          OPTION_MAP (APPEND " . ") (print_nt sxnt_sexp0 d)))) ∧
  (print_nt sxnt_sexp0 (SX_STR str) =
    OPTION_MAP (λs. "\"" ++ s ++ "\"")
      (print_nt sxnt_strcontents (SX_STR str))) ∧
  (print_nt sxnt_sexpnum (SX_NUM n) = SOME (toString n)) ∧
  (print_nt sxnt_sexpnum _ = NONE) ∧
  (print_nt sxnt_sexp0 (SX_SYM str) = print_nt sxnt_sexpsym (SX_SYM str)) ∧
  (print_nt sxnt_sexp0 (SX_NUM n) = print_nt sxnt_sexpnum (SX_NUM n)) ∧
  (print_nt sxnt_sexp0 sx =
   case dest_quote sx of SOME a => OPTION_MAP (APPEND "'") (print_nt sxnt_sexp0 a)
      | NONE => OPTION_MAP (APPEND "(") (print_nt sxnt_sexpseq sx)) ∧
  (print_nt sxnt_sexp sx = print_nt sxnt_sexp0 sx) ∧
  (print_nt _ _ = NONE)`
 (WF_REL_TAC`inv_image ($< LEX $<) (λ(x,y). (sexp_size y, nt_rank x))`
  \\ rw[]
  \\ TRY (
    Induct_on`str` \\ rw[list_size_def] \\ fs[] \\ NO_TAC)
  \\ imp_res_tac dest_quote_sizelt \\ fs[sexp_size_def]
  \\ qpat_x_assum`_ = strip_dot _`(assume_tac o SYM)
  \\ imp_res_tac strip_dot_last_sizelt
  \\ imp_res_tac strip_dot_MEM_sizelt
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]);

val print_nt_ind = theorem"print_nt_ind";

val print_nt_sexp0_no_leading_space = Q.store_thm("print_nt_sexp0_no_leading_space",
  `print_nt sxnt_sexp0 s = SOME str ⇒ str ≠ [] ∧ ¬ isSpace (HD str)`,
  Cases_on`s` \\ rw[print_nt_def] \\ rw[]
  \\ TRY (
    rw[GSYM NULL_EQ,num_to_dec_string_not_null]
    \\ NO_TAC)
  \\ TRY (
    qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[NULL_EQ]
    \\ Cases_on`toString n` \\ fs[]
    \\ assume_tac EVERY_isDigit_num_to_dec_string
    \\ rfs[]
    \\ fs[isSpace_def,isDigit_def]
    \\ NO_TAC)
  \\ every_case_tac \\ fs[NULL_EQ]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ fs[isGraph_def,isSpace_def]);

val print_nt_sexp0_no_leading_rparen = Q.store_thm("print_nt_sexp0_no_leading_rparen",
  `print_nt sxnt_sexp0 s = SOME str ⇒ str ≠ [] ∧ HD str ≠ #")"`,
  Cases_on`s` \\ rw[print_nt_def] \\ rw[]
  \\ TRY (
    rw[GSYM NULL_EQ,num_to_dec_string_not_null]
    \\ NO_TAC)
  \\ TRY (
    qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[NULL_EQ]
    \\ Cases_on`toString n` \\ fs[]
    \\ assume_tac EVERY_isDigit_num_to_dec_string
    \\ rfs[]
    \\ spose_not_then strip_assume_tac
    \\ fs[isSpace_def,isDigit_def]
    \\ NO_TAC)
  \\ every_case_tac \\ fs[NULL_EQ]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ fs[isGraph_def,isSpace_def]);

Theorem peg_eval_sexp_sexp0:
  peg_eval sexpPEG (str ++ rst, pnt sxnt_sexp0) (Success rst s) ∧
  (str ≠ [] ⇒ ¬isSpace (FST(HD str))) ∧
  (rst ≠ [] ⇒ ¬isSpace (FST(HD rst))) ⇒
  peg_eval sexpPEG (str ++ rst, pnt sxnt_sexp) (Success rst s)
Proof
  strip_tac
  \\ rw[Ntimes pnt_def 2,Ntimes peg_eval_NT_SOME 2,FDOM_sexpPEG,sexpPEG_applied,
        ignoreR_def,ignoreL_def,peg_eval_seq_SOME,PULL_EXISTS,peg_eval_rpt]
  \\ qspec_then`str++rst`(mp_tac o Q.GEN`a`)
       (Q.ISPECL[`isSpace`,`sexpPEG`](Q.GENL[`P`,`G`]peg_eval_list_tok_nil))
  \\ disch_then(qspec_then`K arb_sexp`mp_tac)
  \\ impl_tac
  >- (
    spose_not_then strip_assume_tac
    \\ Cases_on`str` \\ rfs[] )
  \\ strip_tac
  \\ rpt (first_x_assum $ irule_at Any)
  \\ irule_at Any peg_eval_list_tok_nil \\ metis_tac[]
QED

Theorem peg_eval_seq_ASSOC:
  peg_eval G (toks, seq (seq s1 s2 (λa b. b)) s3 f) =
  peg_eval G (toks, seq s1 (seq s2 s3 f) (λa b. b))
Proof
  simp[FUN_EQ_THM, FORALL_result, peg_eval_seq_SOME, PULL_EXISTS] >>
  conj_tac >- metis_tac[] >>
  simp[peg_eval_seq_NONE, peg_eval_seq_SOME, PULL_EXISTS] >> metis_tac[]
QED

Theorem gen_peg_eval_seqtok:
  peg_eval G ((c,l) :: toks, seq (tok P f) sym g) res =
  if P c then
    (∃fl fe. res = Failure fl fe ∧ peg_eval G (toks,sym) res) ∨
    ∃s2 c2. res = Success s2 (g (f (c,l)) c2) ∧
            peg_eval G (toks,sym) (Success s2 c2)
  else
    res = Failure l G.tokFALSE
Proof
  simp[SimpLHS, Once peg_eval_cases, peg_eval_tok_SOME] >>
  Cases_on ‘res’ >> simp[peg_eval_tok_NONE, sloc_def] >> metis_tac[]
QED

Theorem gen_peg_eval_tok:
  peg_eval G ((c,l) :: toks, tok P f) res <=>
  if P c then res = Success toks (f (c, l)) else res = Failure l G.tokFALSE
Proof
  simp[Once peg_eval_cases] >> metis_tac[]
QED

Theorem sexpnum_requires_digits:
  ¬isDigit c ⇒
  (peg_eval sexpPEG ((c,l)::rest, pnt sxnt_sexpnum) r ⇔
     r = Failure l sexpPEG.tokFALSE)
Proof
  simp[Once peg_eval_cases, pnt_def, sexpPEG_applied, FDOM_sexpPEG,
       peg_eval_seq_SOME] >>
  simp[pnt_def, peg_eval_NT_SOME, sexpPEG_applied, FDOM_sexpPEG,
       peg_eval_tok_SOME] >>
  dsimp[peg_eval_seq_NONE, peg_eval_NT_SOME, sexpPEG_applied, FDOM_sexpPEG,
       peg_eval_tok_SOME] >>
  simp[Once peg_eval_cases, sexpPEG_applied, FDOM_sexpPEG,
       peg_eval_tok_NONE, sloc_def]
QED

Theorem sexpsym_no_rparen[simp]:
  peg_eval sexpPEG ((#")", l) :: toks, pnt sxnt_sexpsym) r ⇔
  r = Failure l sexpPEG.tokFALSE
Proof
  simp[Once peg_eval_cases, pnt_def, sexpPEG_applied, FDOM_sexpPEG,
       gen_peg_eval_seqtok]
QED

Theorem sexpsym_no_dot[simp]:
  peg_eval sexpPEG ((#".", l) :: toks, pnt sxnt_sexpsym) r ⇔
  r = Failure l sexpPEG.tokFALSE
Proof
  simp[Once peg_eval_cases, pnt_def, sexpPEG_applied, FDOM_sexpPEG,
      gen_peg_eval_seqtok]
QED

Theorem peg_eval_sexp0_NONE:
  c = #")" ∨ c = #"." ⇒
  (peg_eval sexpPEG ((c,l)::rst,nt (mkNT sxnt_sexp0) I) res ⇔
     res = Failure l sexpPEG.notFAIL)
Proof
  rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
     tokeq_def, pegf_def, ignoreL_def, ignoreR_def] >>
  simp[peg_eval_seq_ASSOC, gen_peg_eval_seqtok] >>
  csimp[sexpnum_requires_digits, isDigit_def]
QED

val stoppers_def = Define`
  (stoppers sxnt_sexpnum = UNIV DIFF isDigit) ∧
  (stoppers sxnt_normstrchar = UNIV) ∧
  (stoppers sxnt_escapedstrchar = UNIV) ∧
  (stoppers sxnt_strchar = UNIV) ∧
  (stoppers sxnt_strcontents = {#"\""}) ∧
  (stoppers sxnt_sexpsym = UNIV DIFF valid_symchar) ∧
  (stoppers sxnt_sexp0 = UNIV DIFF valid_symchar DIFF isDigit) ∧
  (stoppers sxnt_sexpseq = UNIV) ∧
  (stoppers sxnt_sexp = UNIV DIFF valid_symchar DIFF isDigit DIFF isSpace)`;

Overload EOF = “Locs end_locn end_locn”
Theorem peg_eval_tokNIL[simp]:
  peg_eval G ([], tok P f) r ⇔ r = Failure EOF G.tokEOF
Proof
  simp[Once peg_eval_cases]
QED

Theorem peg_eval_seqtokNIL[simp]:
  peg_eval G ([], seq (tok P f) sym g) r ⇔ r = Failure EOF G.tokEOF
Proof
  csimp[Once peg_eval_cases]
QED

Theorem peg_eval_seq =
        peg_eval_cases |> SPEC_ALL |> cj 1 |> Q.SPEC ‘(inp, seq s1 s2 f)’
                       |> SIMP_RULE (srw_ss())[]

Theorem seqgrabWS:
  inp ≠ [] ∧ ¬isSpace (FST (HD inp)) ⇒
  (peg_eval G (inp, seq (grabWS sym1) sym2 f) res ⇔
     peg_eval G (inp, seq sym1 sym2 f) res) ∧
  (peg_eval G (inp, pegf (grabWS sym) g) res ⇔
     peg_eval G (inp, pegf sym g) res) ∧
  (peg_eval G (inp, grabWS sym) res ⇔ peg_eval G (inp, sym) res)
Proof
  Cases_on ‘inp’ >>
  simp[SimpLHS, Once peg_eval_cases, grabWS_def, ignoreL_def, PULL_EXISTS] >>
  rename [‘¬isSpace (FST h)’] >> Cases_on ‘h’ >> simp[pegf_def] >>
  strip_tac >>
  simp[peg_eval_seq, peg_eval_rpt, PULL_EXISTS] >>
  ONCE_REWRITE_TAC [peg_eval_list] >> csimp[gen_peg_eval_tok] >>
  dsimp[] >> csimp[] >> Cases_on ‘res’ >> simp[]
QED

Theorem grabWS_grabs[simp]:
  (peg_eval G ((#" ", l)::rest, grabWS sym) res ⇔
     peg_eval G (rest, grabWS sym) res) ∧
  (peg_eval G ((#" ", l)::rest, seq (grabWS sym1) sym2 f) res ⇔
     peg_eval G (rest, seq (grabWS sym1) sym2 f) res)
Proof
  csimp[grabWS_def, peg_eval_rpt, ignoreL_def, peg_eval_seq, PULL_EXISTS,
        EXISTS_result] >> conj_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [peg_eval_list])) >>
  csimp[gen_peg_eval_tok, isSpace_def, PULL_EXISTS] >> metis_tac[]
QED

Theorem sxnt_normstrcharNIL[simp]:
  peg_eval sexpPEG ([], pnt sxnt_normstrchar) r ⇔
  r = Failure (Locs end_locn end_locn) sexpPEG.tokEOF
Proof
  simp[pnt_def, Once peg_eval_cases, sexpPEG_applied, FDOM_sexpPEG]
QED

Theorem strip_dot_EQ_NILNONE[simp]:
  strip_dot s = ([], NONE) ⇔ s = ⟪ ⟫
Proof
  ONCE_REWRITE_TAC [strip_dot_def] >> simp[AllCaseEqs(), UNCURRY]
QED

Theorem strip_dot_EQ_E:
  strip_dot s = (sexps, rest) ⇒
    s = FOLDR SX_CONS (case rest of
                         NONE => ⟪ ⟫
                       | SOME s0 => s0) sexps
Proof
  map_every qid_spec_tac [‘s’, ‘rest’] >> Induct_on‘sexps’ >> simp[] >>
  Cases_on‘s’ >> simp[Once strip_dot_def, AllCaseEqs(), DISJ_IMP_THM] >>
  rename [‘_ (strip_dot s0) = _’] >>
  Cases_on‘strip_dot s0’ >> simp[]
QED

Theorem option_sequence_EQ_NIL[simp]:
  option_sequence l = SOME [] ⇔ l = []
Proof
  Cases_on ‘l’ >> simp[]
QED

Theorem peg_eval_rpt_never_fails[simp]:
  ¬peg_eval G (inp, rpt sym f) (Failure fl fe)
Proof
  simp[peg_eval_rpt]
QED


Theorem peg_eval_print_nt:
  ∀nt s strl rst str.
    print_nt nt s = SOME str ∧ (rst ≠ [] ⇒ FST(HD rst) ∈ stoppers nt) ⇒
    MAP FST strl = str ⇒
    peg_eval sexpPEG (strl ++ rst, pnt nt) (Success rst s)
Proof
  ho_match_mp_tac print_nt_ind
  \\ rpt conj_tac
  \\ TRY (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_tok_SOME,peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_NONE,
       ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_seq_NONE] \\ fs[]
       \\ Cases_on`x0`\\ fs[] \\ NO_TAC) >~
  [‘print_nt sxnt_escapedstrchar’]
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_tok_SOME,peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_NONE,
       ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_seq_NONE] \\ fs[]
    \\ rename [‘#"\"" = FST h’] \\ Cases_on ‘h’ \\ gvs[]
    \\ simp[EXISTS_result, peg_eval_tok_SOME, peg_eval_tok_NONE]) >~
  [‘print_nt sxnt_strchar’]
  >- (
    simp[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
         peg_eval_rpt,peg_eval_choicel_CONS,ignoreL_def,ignoreR_def,
         peg_eval_seq_NONE,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_NONE,
         peg_eval_tok_SOME, EXISTS_PROD, AllCaseEqs()]
    \\ rw[PULL_EXISTS]
    \\ simp[EXISTS_result, AllCaseEqs()]
    \\ gvs[MAP_EQ_CONS] >~
    [‘c ≠ #"\\"’, ‘c ≠ #"\""’]
    >- (simp[gen_peg_eval_seqtok]
        \\ simp[peg_eval_NT_SOME, sexpPEG_applied, FDOM_sexpPEG,
                peg_eval_tok_SOME]) >~
    [‘#"\"" = FST p2’, ‘#"\\" = FST p1’]
    >- (map_every Cases_on [‘p1’, ‘p2’]
        \\ gvs[peg_eval_tok_NONE, peg_eval_tok_SOME]) >~
    [‘FST p2 = FST p1’]
    \\ map_every Cases_on [‘p1’, ‘p2’]
    \\ gvs[peg_eval_tok_NONE, peg_eval_tok_SOME]) >~
  [‘print_nt sxnt_strcontents’]
  >- (Induct_on ‘str’
      >- (simp[print_nt_def, stoppers_def] >> Cases >>
          simp[peg_eval_NT_SOME, pnt_def, FDOM_sexpPEG, sexpPEG_applied,
               peg_eval_rpt] >>
          simp[Once peg_eval_cases] >> dsimp[] >> rpt strip_tac >> disj1_tac >>
          simp[Once peg_eval_cases, sexpPEG_applied, FDOM_sexpPEG,
               peg_eval_choicel_CONS, ignoreL_def, tokeq_def] >>
          csimp[] >>
          rename [‘peg_eval _ (cl1::_, _)’] >>
          Cases_on ‘cl1’ >> gvs[] >> simp[gen_peg_eval_seqtok] >>
          ONCE_REWRITE_TAC [peg_eval_cases] >>
          simp[pnt_def, FDOM_sexpPEG, sexpPEG_applied, peg_eval_tok_NONE,
               peg_eval_tok_SOME] >>
          csimp[AllCaseEqs(), rmax_EQ_Success]) >>
      simp[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
           FORALL_PROD] >> gs[] >> qx_gen_tac ‘c1’ >> strip_tac >>
      gs[] >> simp[Once print_nt_def, AllCaseEqs(), PULL_EXISTS] >>
      simp[MAP_EQ_APPEND, PULL_EXISTS] >> rpt strip_tac >>
      gs[stoppers_def] >>
      simp[peg_eval_NT_SOME, pnt_def, FDOM_sexpPEG, sexpPEG_applied,
           peg_eval_rpt] >>
      irule_at Any (peg_eval_rules |> SPEC_ALL |> CONJUNCTS |> last) >>
      gs[pnt_def] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
      last_x_assum $ irule_at Any >> simp[destSXSYM_def] >>
      qpat_x_assum ‘print_nt sxnt_strchar _ = _’ (K ALL_TAC) >>
      first_x_assum $ qspec_then ‘ARB’ (K ALL_TAC) >>
      rename [‘peg_eval_list _ (sfx ++ tail, _)’] >>
      first_x_assum $ qspecl_then [‘sfx’, ‘tail’] mp_tac >>
      simp[Once print_nt_def] >>
      simp[peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied, peg_eval_rpt,
           pnt_def]) >~
  [‘print_nt sxnt_sexpsym’]
  >- (simp[print_nt_def, peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied,
           pnt_def] >>
      rpt strip_tac >>
      rename [‘peg_eval _ (pfx ++ sfx, _)’] >> Cases_on ‘pfx’ >> gvs[] >>
      rename [‘isGraph (FST cl)’] >> Cases_on ‘cl’ >> gvs[] >>
      simp[gen_peg_eval_seqtok, destSXSYM_def, peg_eval_rpt, PULL_EXISTS] >>
      Cases_on ‘sfx’ >> gvs[]
      >- (irule_at Any peg_eval_list_valid_symchars >>
          simp[FOLDR_STRCAT_destSXSYM]) >>
      gvs[stoppers_def] >>
      irule_at Any
               (peg_eval_list_tok_every_imp
                  |> REWRITE_RULE[GSYM APPEND_ASSOC,
                                  APPEND]) >>
      gvs[IN_DEF, EVERY_MAP, Excl "valid_symchar_def",
          combinTheory.o_DEF, FOLDR_STRCAT_destSXSYM_FST]) >~
  [‘print_nt sxnt_sexpseq’, ‘strip_dot’]
  >- (
    rw[print_nt_def, pnt_def] >>
    rename [‘_ (strip_dot s) = SOME _’] >> Cases_on ‘strip_dot s’ >>
    gvs[] >> dxrule_then SUBST_ALL_TAC strip_dot_EQ_E >>
    simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied] >>
    rename [‘NULL sexps’] >>
    Cases_on ‘sexps’ >> gvs[NULL_EQ, print_space_separated_def]
    >- (gvs[AllCaseEqs(), MAP_EQ_APPEND] >>
        rename [‘#")" = FST rpcl’] >> Cases_on ‘rpcl’ >> gvs[] >>
        simp[peg_eval_choicel_CONS, seqgrabWS, isSpace_def,
             pegf_def, tokeq_def, gen_peg_eval_seqtok]) >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    rename [‘print_space_separated (s1::ss)’] >>
    gvs[print_space_separated_cons] >> Cases_on ‘NULL ss’ >>
    gvs[NULL_EQ]
    >- ((* one sexp before end *) all_tac >>
        gvs[MAP_EQ_APPEND] >>
        rename [‘#")" = FST rpcl’] >> Cases_on ‘rpcl’ >> gvs[] >>
        rename [‘print_nt sxnt_sexp0 sexp1 = SOME (MAP FST s1)’] >>
        drule_then strip_assume_tac print_nt_sexp0_no_leading_rparen >>
        ‘∃c l cs. s1 = (c,l)::cs’
          by (Cases_on ‘s1’ >> gvs[] >> metis_tac[pair_CASES]) >>
        gvs[] >>
        drule_then strip_assume_tac print_nt_sexp0_no_leading_space >> gvs[] >>
        simp[peg_eval_choicel_CONS, seqgrabWS] >> disj2_tac >>
        simp[pegf_def, tokeq_def, gen_peg_eval_seqtok] >> dsimp[] >>
        disj1_tac >> simp[peg_eval_seq_SOME, EXISTS_result, PULL_EXISTS] >>
        gvs[MAP_EQ_CONS, PULL_EXISTS, FORALL_PROD]>>
        simp[pnt_def] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
        first_x_assum $ irule_at Any >> simp[] >> gvs[AllCaseEqs()]
        >- (simp[stoppers_def, peg_eval_rpt, Once peg_eval_list, IN_DEF,
                 valid_symchar_def, isDigit_def, PULL_EXISTS,
                 seqgrabWS, isSpace_def, peg_eval_sexp0_NONE] >>
            simp[peg_eval_choicel_CONS, seqgrabWS, isSpace_def,
                 gen_peg_eval_seqtok] >> dsimp[replace_nil_def]) >>
        gvs[MAP_EQ_CONS] >>
        rename [‘#" " = FST spcl’, ‘#"." = FST fscl’, ‘FST sp2cl = FST spcl’] >>
        map_every Cases_on [‘spcl’, ‘fscl’, ‘sp2cl’] >> gvs[] >>
        simp[stoppers_def, valid_symchar_def, isDigit_def, IN_DEF,
             isGraph_def, isSpace_def, seqgrabWS,
             peg_eval_sexp0_NONE, peg_eval_rpt, Once peg_eval_list] >>
        simp[peg_eval_choicel_CONS] >>
        simp[peg_eval_seq_SOME, seqgrabWS, isSpace_def,
             peg_eval_tok_SOME, EXISTS_result, ignoreL_def, ignoreR_def,
             peg_eval_seq_NONE, peg_eval_tok_NONE] >>
        dsimp[AllCaseEqs()] >>
        rename [‘print_nt _ sexp2 = SOME (MAP FST sfx_sl)’] >>
        qpat_x_assum ‘print_nt _ sexp2 = _’ $
           mp_then (Pos hd) strip_assume_tac print_nt_sexp0_no_leading_space >>
        ‘∃d dl sfx0. sfx_sl = (d,dl)::sfx0’
          by (Cases_on ‘sfx_sl’ >> gvs[] >> metis_tac[pair_CASES]) >>
        gvs[seqgrabWS, MAP_EQ_CONS, PULL_EXISTS, FORALL_PROD] >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >> first_x_assum $ irule_at Any >>
        simp[stoppers_def, IN_DEF, isDigit_def, seqgrabWS, isSpace_def,
             peg_eval_tok_SOME, replace_nil_def]) >>
    gvs[MAP_EQ_APPEND] >>
    rename [‘#")" = FST rpcl’, ‘#" " = FST spcl’] >>
    map_every Cases_on [‘rpcl’, ‘spcl’] >> gvs[] >>
    rename [‘print_nt sxnt_sexp0 s1 = SOME (MAP FST s1_s)’] >>
    drule_then strip_assume_tac print_nt_sexp0_no_leading_space >>
    ‘∃c1 l1 rest1. s1_s = (c1,l1)::rest1’
      by (Cases_on ‘s1_s’ >> gvs[] >> metis_tac[pair_CASES]) >> gvs[] >>
    drule_then strip_assume_tac print_nt_sexp0_no_leading_rparen >> gvs[] >>
    simp[Once peg_eval_choicel_CONS, seqgrabWS, tokeq_def] >>
    simp[pegf_def, gen_peg_eval_seqtok] >>
    simp[Once peg_eval_choicel_CONS, EXISTS_result, AllCaseEqs()] >>
    simp[peg_eval_seq_SOME, PULL_EXISTS] >>
    gvs[MAP_EQ_CONS, PULL_EXISTS, FORALL_PROD, pnt_def, seqgrabWS] >>
    REWRITE_TAC [GSYM APPEND_ASSOC] >> first_x_assum $ irule_at Any >>
    simp[stoppers_def, valid_symchar_def, IN_DEF, isDigit_def, isGraph_def,
         isSpace_def, isPrint_def] >>
    rename [‘print_space_separated sl = MAP FST pfx_s’,
            ‘option_sequence (MAP _ sexpl) = SOME sl’,
            ‘(#" ", sploc)’, ‘(#")", rploc)’, ‘pfx_s ++ sfx_s’] >>
    map_every (C qpat_x_assum (K ALL_TAC))
              [‘¬isSpace c1’, ‘c1 ≠ #")"’, ‘print_nt _ _ = _’] >>
    map_every (C qpat_x_assum mp_tac) [
        ‘sl ≠ []’, ‘option_sequence _ = _’, ‘print_space_separated _ = _’,
        ‘∀x. MEM x sexpl ⇒ P ’
      ] >>
    map_every qid_spec_tac [‘sl’, ‘pfx_s’, ‘sploc’, ‘sexpl’] >>
    simp[peg_eval_rpt, PULL_EXISTS] >>
    Induct_on ‘sexpl’ >> simp[] >> rpt strip_tac>>
    rename [‘sl = s1 :: ss’, ‘print_space_separated sl’] >>
    Cases_on ‘ss’ >> gvs[]
    >- (gvs[print_space_separated_cons] >> simp[Once peg_eval_list] >>
        drule_then strip_assume_tac print_nt_sexp0_no_leading_space >>
        dsimp[] >> disj2_tac >>
        ‘∃c1 l1 pfx0_s. pfx_s = (c1,l1) :: pfx0_s’
          by (Cases_on ‘pfx_s’ >> gvs[] >> metis_tac[pair_CASES]) >>
        gvs[seqgrabWS, MAP_EQ_CONS, PULL_EXISTS, FORALL_PROD] >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >> first_x_assum $ irule_at Any >>
        irule_at Any peg_eval_list_nil >> simp[EXISTS_result] >>
        gvs[AllCaseEqs()] >> simp[seqgrabWS, isSpace_def, peg_eval_sexp0_NONE]
        >- (simp[stoppers_def, valid_symchar_def, IN_DEF, isDigit_def] >>
            csimp[Once peg_eval_choicel_CONS, seqgrabWS, isSpace_def,
                  gen_peg_eval_seqtok, replace_nil_def]) >>
        gvs[MAP_EQ_CONS] >>
        rename [‘#" " = FST spcl’, ‘#"." = FST fscl’, ‘FST sp2cl = FST spcl’] >>
        map_every Cases_on [‘spcl’, ‘fscl’, ‘sp2cl’] >> gvs[] >>
        simp[isSpace_def, seqgrabWS, peg_eval_sexp0_NONE, stoppers_def,
             valid_symchar_def, IN_DEF, isGraph_def, isDigit_def] >>
        simp[Once peg_eval_choicel_CONS, peg_eval_seq_SOME, isSpace_def,
             seqgrabWS, peg_eval_tok_SOME, gen_peg_eval_seqtok] >>
        simp[peg_eval_choicel_CONS, ignoreR_def, ignoreL_def,
             peg_eval_seq_ASSOC, seqgrabWS, isSpace_def, gen_peg_eval_seqtok]>>
        simp[EXISTS_result, AllCaseEqs()] >>
        rev_drule_then strip_assume_tac print_nt_sexp0_no_leading_space >>
        rename [‘peg_eval _ (sfx_ls ++ [_] ++ _, _)’] >>
        simp[peg_eval_seq_SOME, PULL_EXISTS] >>
        ‘∃sc sl sfx_ls0. sfx_ls = (sc,sl) ::sfx_ls0’
          by (Cases_on ‘sfx_ls’ >> gvs[] >> metis_tac[pair_CASES]) >>
        gvs[seqgrabWS, MAP_EQ_CONS, PULL_EXISTS, FORALL_PROD] >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >> first_x_assum $ irule_at Any >>
        simp[seqgrabWS, isSpace_def, peg_eval_tok_SOME, replace_nil_def,
             stoppers_def, IN_DEF, isDigit_def]) >>
    (* inductive case (at last!) *)
    cheat) >~
  [‘print_nt sxnt_sexp0’, ‘print_nt sxnt_strcontents’]
  >- (gen_tac >> strip_tac >>
      simp[Once print_nt_def, PULL_EXISTS, MAP_EQ_CONS, FORALL_PROD,
           MAP_EQ_APPEND] >> rpt strip_tac >>
      simp[peg_eval_NT_SOME, pnt_def, FDOM_sexpPEG, sexpPEG_applied] >>
      simp[Once peg_eval_choicel_CONS] >> disj2_tac >>
      simp[REWRITE_RULE [pnt_def] sexpnum_requires_digits, isDigit_def] >>
      simp[Once peg_eval_choicel_CONS, tokeq_def, ignoreL_def,
           gen_peg_eval_seqtok] >> dsimp[] >>
      simp[Once peg_eval_choicel_CONS, ignoreR_def, gen_peg_eval_seqtok,
           peg_eval_seq_ASSOC] >> dsimp[peg_eval_seq_SOME] >> disj1_tac >>
      gvs[pnt_def] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
      first_x_assum $ irule_at Any >>
      simp[stoppers_def, Once peg_eval_cases, gen_peg_eval_tok]) >~
  [‘print_nt sxnt_sexpnum’]
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_seq_SOME,peg_eval_rpt,peg_eval_tok_SOME]
    \\ qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[NULL_EQ]
    \\ Cases_on`toString n` \\ fs[]
    \\ assume_tac EVERY_isDigit_num_to_dec_string
    \\ rfs[PULL_EXISTS]
    \\ Cases_on`strl` \\ fs[] \\ rw[]
    \\ rename1`EVERY isDigit (MAP FST t)`
    \\ qspec_then`t`mp_tac peg_eval_list_digits
    \\ impl_tac >- fs[stoppers_def,IN_DEF]
    \\ strip_tac
    \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
    \\ rw[]
    \\ pairarg_tac \\ fs[destSXNUM_def]
    \\ fs[UNCURRY,destSXCONS_def,destSXNUM_def,rich_listTheory.FOLDL_MAP]
    \\ qmatch_assum_abbrev_tac`FOLDL f a t = _`
    \\ `∀ls a . FST (FOLDL f a ls) = FST a * 10 ** (LENGTH ls)`
    by ( Induct \\ simp[Abbr`f`,arithmeticTheory.EXP])
    \\ first_x_assum(qspecl_then[`t`,`a`]mp_tac)
    \\ rw[Abbr`a`]
    \\ `∀ls a. EVERY isDigit (MAP FST ls) ⇒
          SND (FOLDL f a ls) = (10 ** LENGTH ls * SND a + (l2n 10 (MAP (combin$C $- 48 o ORD) (REVERSE (MAP FST ls)))))`
    by (
      qunabbrev_tac`f` \\ rpt (pop_assum kall_tac)
      \\ ho_match_mp_tac SNOC_INDUCT
      \\ rw[numposrepTheory.l2n_def,FOLDL_SNOC,EVERY_SNOC,
            MAP_SNOC,REVERSE_SNOC,arithmeticTheory.EXP]
      \\ simp[isDigit_ORD_MOD_10] )
    \\ first_x_assum(qspecl_then[`t`,`(1,0)`]mp_tac)
    \\ simp[] \\ disch_then kall_tac
    \\ simp[GSYM s2n_def]
    \\ fs[s2n_UNHEX_alt]
    \\ imp_res_tac num_to_dec_string_eq_cons
    \\ simp[GSYM num_from_dec_string_def]
    \\ imp_res_tac isDigit_UNHEX_alt \\ fs[])
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_seq_SOME,peg_eval_rpt,peg_eval_choicel_CONS,tokeq_def,
       peg_eval_tok_SOME,peg_eval_tok_NONE,ignoreR_def,ignoreL_def,PULL_EXISTS,
       pegf_def,destSXSYM_def]
    \\ disj2_tac
    \\ conj_tac
    >- (
      rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_seq_NONE,pnt_def]
      \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_tok_NONE]
      \\ Cases_on`strl` \\ fs[] )
    \\ disj2_tac
    \\ rw[peg_eval_seq_NONE,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ Cases_on`strl` \\ fs[]
    \\ fs[UNCURRY,destSXSYM_def]
    \\ first_x_assum(qspec_then`h::t`mp_tac) \\ rw[]
    \\ first_x_assum match_mp_tac
    \\ fs[stoppers_def])
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_choicel_CONS]
    \\ disj1_tac
    \\ first_x_assum match_mp_tac
    \\ fs[stoppers_def] )
  >- (
    rw[print_nt_def]
    \\ reverse every_case_tac \\ fs[]
    \\ TRY pairarg_tac \\ fs[] \\ rw[]
    >- (
      fs[pnt_def]
      \\ Cases_on`strl` \\ fs[] \\ rw[]
      \\ rw[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
            pnt_def,peg_eval_seq_SOME,peg_eval_seq_NONE,
            peg_eval_tok_NONE,peg_eval_tok_SOME,isDigit_def,
            tokeq_def,ignoreR_def,ignoreL_def,pegf_def]
      >- (
        rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ rw[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
              pnt_def,peg_eval_seq_SOME,peg_eval_seq_NONE,
              peg_eval_tok_NONE,peg_eval_tok_SOME,isDigit_def,
              tokeq_def,ignoreR_def,ignoreL_def]
        \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ rw[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
              pnt_def,peg_eval_seq_SOME,peg_eval_seq_NONE,
              peg_eval_tok_NONE,peg_eval_tok_SOME,isDigit_def] )
      \\ rw[grabWS_def,ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_rpt]
      \\ qmatch_asmsub_rename_tac`dest_quote (SX_CONS a d) = SOME x`
      \\ Cases_on`d` \\ fs[] \\ rw[] \\ rfs[]
      \\ imp_res_tac print_nt_sexp0_no_leading_space
      \\ rw[Once peg_eval_list]
      \\ rw[peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ Cases_on`t` \\ fs[]
      \\ once_rewrite_tac[rich_listTheory.CONS_APPEND]
      \\ rewrite_tac[APPEND_ASSOC]
      \\ rw[])
    \\ fs[option_sequence_SOME] \\ rw[]
    \\ Cases_on`strl` \\ fs[] \\ rw[]
    \\ rw[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS]
    \\ Cases_on`NULL ls` \\ fs[]
    >- (
      fs[NULL_EQ,print_space_separated_def]
      \\ Cases_on`n` \\ fs[] \\ rw[]
      \\ disj1_tac
      \\ rw[pegf_def,peg_eval_seq_SOME,tokeq_def,grabWS_def,ignoreL_def,peg_eval_tok_SOME,peg_eval_rpt,PULL_EXISTS]
      \\ fs[Once strip_dot_def]
      \\ pairarg_tac \\ fs[])
    \\ disj2_tac
    \\ conj_tac
    >- (
      rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_seq_NONE,pnt_def]
      \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_tok_NONE,isDigit_def] )
    \\ disj1_tac
    \\ rw[tokeq_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_tok_SOME]
    \\ rfs[]
    \\ qmatch_asmsub_rename_tac`dest_quote sx = NONE`
    \\ fsrw_tac[boolSimps.ETA_ss][]
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ qhdtm_x_assum`dest_quote`kall_tac
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ qpat_x_assum`_ = SOME l2`mp_tac
    \\ rw[pnt_def]
    \\ first_x_assum match_mp_tac
    \\ rw[stoppers_def] )
  >- (
    rw[print_nt_def] \\ fs[]
    \\ match_mp_tac peg_eval_sexp_sexp0
    \\ conj_tac
    >- (
      first_x_assum match_mp_tac
      \\ fs[stoppers_def] )
    \\ imp_res_tac print_nt_sexp0_no_leading_space
    \\ Cases_on`strl`
    \\ fs[stoppers_def,IN_DEF]));

val print_nt_print_sexp = Q.store_thm("print_nt_print_sexp",
  `∀s. valid_sexp s ⇒ (print_nt sxnt_sexp s = SOME (print_sexp s)) `,
  ho_match_mp_tac(theorem"print_sexp_ind")
  \\ conj_tac
  >- (
    simp[print_nt_def,print_sexp_def]
    \\ Cases \\ simp[] )
  \\ conj_tac >- ( rw[print_nt_def,print_sexp_def] )
  \\ conj_tac
  >- (
    rw[print_nt_def,print_sexp_def]
    \\ Induct_on`s`
    >- rw[escape_string_def]
    \\ simp[Once escape_string_def]
    \\ CASE_TAC \\ fs[]
    >- (
      rw[] \\ fs[]
      \\ simp[Once escape_string_def] )
    \\ rpt strip_tac \\ fs[]
    \\ simp[Once escape_string_def]
    \\ qpat_x_assum`_ = _`mp_tac
    \\ simp[Once escape_string_def]
    \\ IF_CASES_TAC \\ fs[] \\ strip_tac \\ rpt var_eq_tac
    \\ IF_CASES_TAC \\ fs[] )
  \\ rw[] \\ fs[]
  \\ rw[print_nt_def]
  \\ pairarg_tac \\ fs[]
  \\ simp[print_sexp_def]
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    qmatch_asmsub_rename_tac`dest_quote (SX_CONS a d)`
    \\ Cases_on`d` \\ fs[] \\ rpt var_eq_tac
    \\ pop_assum mp_tac
    \\ simp[Once strip_dot_def]
    \\ simp[Once strip_dot_def]
    \\ simp[Once strip_dot_def]
    \\ strip_tac \\ rpt var_eq_tac \\ fs[]
    \\ qhdtm_x_assum`print_nt`mp_tac
    \\ simp[print_nt_def] )
  \\ qmatch_goalsub_abbrev_tac`COND b (#"'"::_)`
  \\ `n = NONE ⇒ ¬b`
  by (
    qmatch_asmsub_rename_tac`dest_quote (SX_CONS a d)`
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ simp[Once strip_dot_def]
    \\ pairarg_tac \\ fs[]
    \\ ntac 2 strip_tac \\ rpt var_eq_tac
    \\ simp[Abbr`b`] \\ spose_not_then strip_assume_tac
    \\ fs[quantHeuristicsTheory.LIST_LENGTH_2]
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ simp[Once strip_dot_def]
    \\ CASE_TAC \\ fs[] \\ rw[]
    \\ pairarg_tac \\ fs[]
    \\ spose_not_then strip_assume_tac \\ rw[]
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ simp[Once strip_dot_def]
    \\ CASE_TAC \\ fs[] \\ rw[]
    \\ pairarg_tac \\ fs[] )
  \\ Cases_on`n` \\ fs[]
  >- (
    fs[option_sequence_SOME]
    \\ imp_res_tac strip_dot_valid_sexp \\ rfs[]
    \\ fs[EVERY_MEM,MEM_MAP,optionTheory.IS_SOME_EXISTS,PULL_EXISTS]
    \\ conj_tac
    >- (
      rw[]
      \\ last_x_assum(qspec_then`a`mp_tac)
      \\ impl_tac >- metis_tac[markerTheory.Abbrev_def]
      \\ rw[print_nt_def] )
    \\ AP_TERM_TAC
    \\ simp[MAP_MAP_o,MAP_EQ_f]
    \\ rw[]
    \\ last_x_assum(qspec_then`a`mp_tac)
    \\ impl_tac >- metis_tac[markerTheory.Abbrev_def]
    \\ rw[print_nt_def] )
  \\ fs[markerTheory.Abbrev_def] \\ rw[]
  \\ fs[option_sequence_SOME]
  \\ qhdtm_x_assum`strip_dot`mp_tac
  \\ simp[Once strip_dot_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac \\ rpt var_eq_tac
  \\ fs[]
  \\ imp_res_tac strip_dot_valid_sexp
  \\ rfs[]
  \\ simp[PULL_EXISTS,optionTheory.IS_SOME_EXISTS]
  \\ fs[print_nt_def]
  \\ fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]
  \\ simp[print_space_separated_cons,NULL_EQ]
  \\ rw[]
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o,MAP_EQ_f]);

val peg_eval_print_sexp = Q.store_thm("peg_eval_print_sexp",
  `∀s sl. valid_sexp s ⇒
       print_sexp s = MAP FST sl ⇒
       peg_eval sexpPEG (sl,sexpPEG.start) (SOME ([],s))`,
  rw[]
  \\ imp_res_tac print_nt_print_sexp
  \\ imp_res_tac peg_eval_print_nt
  \\ first_x_assum(qspec_then`[]`mp_tac)
  \\ simp[]);

val parse_print = Q.store_thm("parse_print",
  `valid_sexp s ⇒ print_sexp s = MAP FST sl ⇒
   parse_sexp sl = SOME s`,
  rw[parse_sexp_def,EXISTS_PROD]
  \\ imp_res_tac peg_eval_print_sexp
  \\ simp[pegparse_eq_SOME,wfG_sexpPEG]);

(*
val cs = listLib.list_compset()
val () = stringLib.add_string_compset cs;
val () = pairLib.add_pair_compset cs;
val () = combinLib.add_combin_compset cs;
val () = sumSimps.SUM_rws cs;
val () = optionLib.OPTION_rws cs;
val () = pred_setLib.add_pred_set_compset cs;
val () = ASCIInumbersLib.add_ASCIInumbers_compset cs;
val () = pegLib.add_peg_compset cs;
(* TODO: pegLib should not include wfG *)
val () = computeLib.scrub_thms [wfG_def,pegparse_def] cs;
val () = computeLib.add_thms[pegparse_def]cs;
(* -- *)
val () = computeLib.add_thms[
  destResult_def,destSXCONS_def,destSXNUM_def,destSXSYM_def]cs;
val () = computeLib.add_thms[
  sexpPEG_exec_thm,EQT_INTRO wfG_sexpPEG,
  valid_first_symchar_def, valid_symchar_def,
    pnt_def,ignoreR_def,ignoreL_def,tokeq_def,pegf_def,
    choicel_def,grabWS_def,replace_nil_def,
  parse_sexp_def]cs;

val res = computeLib.CBV_CONV cs ``parse_sexp "s1"``;
val res = computeLib.CBV_CONV cs ``parse_sexp "'('1)"``;
val res = computeLib.CBV_CONV cs ``parse_sexp "(1 2 . 3)"``;
val res = computeLib.CBV_CONV cs ``parse_sexp "(1 2 3)"``;
val res = computeLib.CBV_CONV cs ``parse_sexp "(\"hello\" \"there\")"``;
val res = computeLib.CBV_CONV cs ``parse_sexp "'\"hi\""``;
val res = computeLib.CBV_CONV cs ``parse_sexp "(1 (2 . 3) . 2)"``;

EVAL``print_sexp ^(res |> concl |> rhs |> rand)``
val _ = computeLib.add_funs [optionTheory.OPTION_MAP2_THM];
EVAL``print_nt sxnt_sexp ^(res |> concl |> rhs |> rand)``

val _ = clear_overloads_on"STRCAT";
val _ = clear_overloads_on"STRING";
val _ = clear_overloads_on"CONCAT";
val _ = set_trace"Goalstack.print_goal_at_top"0;
*)

val _ = export_theory()
