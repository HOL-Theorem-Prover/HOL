open HolKernel boolLib bossLib lcsymtacs finite_mapSyntax
open ASCIInumbersTheory simpleSexpTheory
open simpleSexpPEGTheory pegTheory pegexecTheory

val _ = new_theory"simpleSexpParse"

(* TODO: move *)

val isDigit_HEX = Q.store_thm("isDigit_HEX",
  `∀n. n < 10 ⇒ isDigit (HEX n)`,
  simp[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac \\ EVAL_TAC
  \\ strip_tac \\ var_eq_tac \\ EVAL_TAC);

val EVERY_isDigit_n2s = Q.store_thm("EVERY_isDigit_n2s",
  `∀n. EVERY isDigit (n2s 10 HEX n)`,
  rw[n2s_def,rich_listTheory.EVERY_REVERSE,listTheory.EVERY_MAP]
  \\ match_mp_tac (MP_CANON listTheory.EVERY_MONOTONIC)
  \\ qexists_tac`$> 10`
  \\ simp[]
  \\ metis_tac[isDigit_HEX,arithmeticTheory.GREATER_DEF,
               numposrepTheory.n2l_BOUND,DECIDE``0n < 10``]);

val EVERY_isDigit_num_to_dec_string = Q.store_thm("EVERY_isDigit_num_to_dec_string",
  `EVERY isDigit (num_to_dec_string n)`,
  rw[num_to_dec_string_def,EVERY_isDigit_n2s]);

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
  simp[stringTheory.isDigit_def] \\ rw[]
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
  \\ Q.ISPEC_THEN`n2l 10 n`FULL_STRUCT_CASES_TAC listTheory.SNOC_CASES
  \\ fs[listTheory.EVERY_SNOC] \\ rpt var_eq_tac
  \\ simp[UNHEX_HEX]
  \\ simp[listTheory.SNOC_APPEND,l2n_APPEND,numposrepTheory.l2n_def]
  \\ simp[s2n_def,listTheory.MAP_MAP_o]
  \\ AP_TERM_TAC
  \\ fs[listTheory.LIST_EQ_REWRITE,listTheory.EL_MAP,listTheory.EVERY_MEM,listTheory.MEM_EL,PULL_EXISTS]
  \\ rw[] \\ res_tac \\ simp[UNHEX_HEX]);

val peg_eval_list_tok_nil = Q.store_thm("peg_eval_list_tok_nil",
  `∀ls. (ls = [] ∨ ¬ P(HD ls)) ⇒
   peg_eval_list G (ls, tok P a) (ls,[])`,
  rw[Once peg_eval_list,peg_eval_tok_NONE,listTheory.EVERY_MEM]
  \\ Cases_on`ls` \\ fs[]);

val peg_eval_list_tok_imp_every = Q.store_thm("peg_eval_list_tok_imp_every",
  `∀ls r z. peg_eval_list G (ls, tok P a) (r,z) ⇒
   ∃l. ls = l ++ r ∧ EVERY P l ∧ (¬NULL r ⇒ ¬P (HD r))`,
  Induct \\ rw[Once peg_eval_list,listTheory.NULL_EQ,peg_eval_tok_SOME]
  \\ fs[peg_eval_tok_NONE]
  \\ res_tac
  \\ rpt var_eq_tac
  \\ qexists_tac`h::l`
  \\ rw[] \\ fs[listTheory.NULL_EQ]);

val peg_eval_list_tok_every_imp = Q.store_thm("peg_eval_list_tok_every_imp",
  `∀ls x rst. EVERY P ls ∧ ¬ P x ⇒
   peg_eval_list G (ls ++ [x] ++ rst, tok P a) ([x] ++ rst, MAP a ls)`,
  Induct \\ simp[] \\ simp[Once peg_eval_list]
  \\ simp[peg_eval_tok_NONE]
  \\ rw[] \\ fs[]
  \\ simp[peg_eval_tok_SOME]);

(* -- *)

val parse_sexp_def = Define`
  parse_sexp s =
    OPTION_BIND (pegparse sexpPEG s)
      (λ(rest,sx). OPTION_IGNORE_BIND (OPTION_GUARD (rest="")) (SOME sx))`;

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

val print_sexp_def = tDefine"print_sexp"`
  (print_sexp (SX_SYM s) = s) ∧
  (print_sexp (SX_NUM n) = toString n) ∧
  (print_sexp (SX_STR s) = "\"" ++ escape_string s ++ "\"") ∧
  (print_sexp s =
   case strip_sxcons s of
   | NONE => (case s of SX_CONS a d => "(" ++ print_sexp a ++ "." ++ print_sexp d ++")" | _ => "")
   | SOME [q; s] => if q = SX_SYM "quote" then "'" ++ print_sexp s
                    else "(" ++ print_sexp q ++ " " ++ print_sexp s ++ ")"
   | SOME ls => "(" ++ print_space_separated (MAP print_sexp ls) ++ ")")`
  (WF_REL_TAC`measure sexp_size` >> rw[] >> simp[sexp_size_def] >>
   fs[Once strip_sxcons_def] >> rw[] >> simp[sexp_size_def] >>
   PROVE_TAC[sxMEM_def,sxMEM_sizelt,arithmeticTheory.LESS_IMP_LESS_ADD,listTheory.MEM,
             DECIDE``(a:num) + (b + c) = b + (a + c)``]);

val FOLDR_STRCAT_destSXSYM = Q.prove(
  `∀ls. FOLDR (λs a. STRCAT (destSXSYM s) a) "" (MAP (λc. SX_SYM (STRING c "")) ls) = ls`,
  Induct >> simp[destSXSYM_def]);

val peg_eval_list_valid_symchars = Q.prove(
  `∀cs. EVERY valid_symchar cs ⇒
        peg_eval_list sexpPEG (cs,tok valid_symchar (λc. SX_SYM [c])) ("",MAP (λc. SX_SYM [c]) cs)`,
  Induct >> simp[Once peg_eval_cases] >> simp[Once peg_eval_cases])

val peg_eval_valid_symchars = Q.prove(
  `∀cs. EVERY valid_symchar cs ⇒
       peg_eval sexpPEG (cs,rpt (tok valid_symchar (λc. SX_SYM (STRING c ""))) (SX_SYM o FOLDR (λs a. STRCAT (destSXSYM s) a) ""))
       (SOME ("",SX_SYM cs))`,
  rw[Once peg_eval_cases] >>
  imp_res_tac peg_eval_list_valid_symchars >>
  metis_tac[FOLDR_STRCAT_destSXSYM]);

val peg_eval_valid_symbol = Q.prove(
  `∀s. valid_symbol s ⇒
       peg_eval sexpPEG (s,sexpPEG.start) (SOME ("",SX_SYM s))`,
  Cases_on`s`>>
  simp[pnt_def, peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied,
       ignoreL_def, ignoreR_def, peg_eval_seq_SOME, peg_eval_rpt] >>
  dsimp[] >> strip_tac >>
  `¬isSpace h` by (strip_tac >> Cases_on `h` >> fs[stringTheory.isGraph_def]) >>
  simp[Once peg_eval_list, SimpL ``$/\``] >>
  simp[peg_eval_tok_SOME, peg_eval_tok_NONE] >>
  simp[peg_eval_choicel_CONS, peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied,
       peg_eval_seq_SOME, peg_eval_tok_SOME, peg_eval_tok_NONE, tokeq_def,
       peg_eval_seq_NONE, pegf_def, pnt_def, destSXSYM_def] >> dsimp[] >>
  simp[Once peg_eval_cases, SimpL ``$/\``] >>
  dsimp[FDOM_sexpPEG, sexpPEG_applied, peg_eval_seq_NONE, pnt_def,
        peg_eval_rpt] >>
  simp[Once peg_eval_cases, SimpL ``$/\``] >>
  dsimp[FDOM_sexpPEG, sexpPEG_applied, peg_eval_seq_NONE, pnt_def,
        peg_eval_rpt, peg_eval_tok_NONE] >>
  IMP_RES_THEN mp_tac peg_eval_valid_symchars >>
  dsimp[peg_eval_rpt] >> qx_gen_tac `l` >> strip_tac >>
  map_every qexists_tac[`""`,`[]`,`l`] >>
  simp[destSXSYM_def] >> rw[] >>
  rw[Once peg_eval_cases] >> simp[peg_eval_tok_NONE]);

val valid_symbol_no_spaces = Q.store_thm("valid_symbol_no_spaces",
  `∀s. valid_symbol s ⇒ EVERY ($~ o isSpace) s`,
  Cases_on`s` \\ rw[valid_symbol_def]
  >- ( fs[stringTheory.isGraph_def,stringTheory.isSpace_def] )
  \\ Induct_on`t`
  \\ rw[]
  >- ( fs[stringTheory.isGraph_def,stringTheory.isSpace_def] ))

val peg_eval_list_num_to_dec_string_no_spaces = Q.prove(
  `peg_eval_list sexpPEG (toString n,tok isSpace ARB) (toString n,[])`,
  match_mp_tac peg_eval_list_tok_nil
  \\ assume_tac EVERY_isDigit_num_to_dec_string
  \\ fs[listTheory.EVERY_MEM] \\ rw[]
  \\ Cases_on`toString n` \\ fs[]
  \\ fs[stringTheory.isDigit_def,stringTheory.isSpace_def]
  \\ spose_not_then strip_assume_tac
  \\ first_x_assum(qspec_then`h`mp_tac)
  \\ simp[]);

val peg_eval_list_digits = Q.store_thm("peg_eval_list_digits",
  `∀s. EVERY isDigit s ⇒
   peg_eval_list sexpPEG (s,nt(mkNT sxnt_digit) I) ("",MAP (SX_NUM o combin$C $- 48 o ORD) s)`,
  Induct \\ simp[Once peg_eval_list]
  >- (
    simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE] )
  \\ rw[] \\ fs[]
  \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
  \\ simp[peg_eval_tok_SOME]);

val peg_eval_number = Q.prove(
  `∀n. peg_eval sexpPEG (toString n,sexpPEG.start) (SOME ("",SX_NUM n))`,
  simp[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       ignoreL_def, ignoreR_def, peg_eval_seq_SOME, peg_eval_rpt,
       Once peg_eval_choicel_CONS,
       PULL_EXISTS]
  \\ srw_tac[boolSimps.DNF_ss][]
  \\ disj1_tac
  \\ part_match_exists_tac (hd o strip_conj) (concl peg_eval_list_num_to_dec_string_no_spaces)
  \\ simp[peg_eval_list_num_to_dec_string_no_spaces]
  \\ simp[peg_eval_tok_SOME,PULL_EXISTS]
  \\ Cases_on`toString n`
  >- (
    pop_assum(mp_tac o Q.AP_TERM`LENGTH`)
    \\ simp[num_to_dec_string_def,n2s_def,numposrepTheory.LENGTH_n2l] )
  \\ simp[]
  \\ assume_tac EVERY_isDigit_num_to_dec_string
  \\ rfs[]
  \\ imp_res_tac peg_eval_list_digits
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
  \\ simp[]
  \\ qexists_tac`[]`
  \\ simp[peg_eval_list_tok_nil]
  \\ simp[pairTheory.UNCURRY]
  \\ simp[destSXCONS_def,destSXNUM_def]
  \\ simp[rich_listTheory.FOLDL_MAP,pairTheory.UNCURRY,destSXNUM_def]
  \\ qmatch_abbrev_tac`n = SND (FOLDL f a t) + _`
  \\ `∀ls a . FST (FOLDL f a ls) = FST a * 10 ** (LENGTH ls)`
  by ( Induct \\ simp[Abbr`f`,arithmeticTheory.EXP] )
  \\ first_x_assum(qspecl_then[`t`,`a`]SUBST_ALL_TAC)
  \\ `FST a = 1` by simp[Abbr`a`] \\ simp[]
  \\ `∀ls a. EVERY isDigit ls ⇒
        SND (FOLDL f a ls) = (10 ** LENGTH ls * SND a + (l2n 10 (MAP (combin$C $- 48 o ORD) (REVERSE ls))))`
  by (
    qunabbrev_tac`f` \\ rpt (pop_assum kall_tac)
    \\ ho_match_mp_tac listTheory.SNOC_INDUCT
    \\ rw[numposrepTheory.l2n_def,listTheory.FOLDL_SNOC,listTheory.EVERY_SNOC,listTheory.REVERSE_SNOC,arithmeticTheory.EXP]
    \\ simp[isDigit_ORD_MOD_10] )
  \\ first_x_assum(qspecl_then[`t`,`a`]mp_tac)
  \\ simp[] \\ disch_then kall_tac
  \\ simp[Abbr`a`]
  \\ simp[GSYM s2n_def]
  \\ fs[s2n_UNHEX_alt]
  \\ imp_res_tac num_to_dec_string_eq_cons
  \\ simp[GSYM num_from_dec_string_def]
  \\ imp_res_tac isDigit_UNHEX_alt \\ fs[]);

val peg_eval_list_chars = Q.store_thm("peg_eval_list_chars",
  `∀l1. EVERY isPrint l1 ⇒
    peg_eval_list sexpPEG (escape_string l1++[#"\""], nt (mkNT sxnt_strchar) I) ("\"",MAP (λc. SX_SYM [c]) l1)`,
  Induct \\ simp[Once escape_string_def]
  >- (
    simp[Once peg_eval_list]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS,pnt_def]
    \\ simp[ignoreL_def,peg_eval_seq_NONE,tokeq_def,peg_eval_tok_NONE]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE] )
  \\ rw[]
  >- (
    fs[]
    \\ simp[Once peg_eval_list]
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ simp[]
    \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS]
    \\ disj1_tac
    \\ simp[ignoreL_def,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_SOME,pnt_def]
    \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_SOME] )
  >- (
    fs[]
    \\ simp[Once peg_eval_list]
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ simp[]
    \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS]
    \\ disj1_tac
    \\ simp[ignoreL_def,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_SOME,pnt_def]
    \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_SOME,peg_eval_tok_NONE])
  \\ fs[]
  \\ simp[Once peg_eval_list]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
  \\ simp[]
  \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ simp[peg_eval_choicel_CONS]
  \\ disj2_tac
  \\ simp[ignoreL_def,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_SOME,pnt_def,peg_eval_seq_NONE,peg_eval_tok_NONE]
  \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ simp[peg_eval_tok_SOME]);

val print_sexp_non_space = Q.store_thm("print_sexp_non_space",
  `∀s. valid_sexp s ⇒ ∃h t. print_sexp s  = h :: t ∧ ¬isSpace h ∧ h ≠ #")"`,
  ho_match_mp_tac(theorem"print_sexp_ind")
  \\ rw[print_sexp_def]
  >- (
    Cases_on`s` \\ fs[valid_symbol_def]
    \\ fs[stringTheory.isSpace_def,stringTheory.isGraph_def] )
  >- (
    assume_tac EVERY_isDigit_num_to_dec_string
    \\ fs[num_to_dec_string_def,n2s_def,Once numposrepTheory.n2l_def]
    \\ qmatch_assum_abbrev_tac`EVERY isDigit ls`
    \\ Cases_on`ls` \\ fs[]
    >- ( pop_assum mp_tac \\ rw[markerTheory.Abbrev_def] )
    \\ fs[stringTheory.isSpace_def,stringTheory.isDigit_def]
    \\ spose_not_then strip_assume_tac \\ fs[])
  >- EVAL_TAC
  \\ BasicProvers.TOP_CASE_TAC >- EVAL_TAC
  \\ BasicProvers.TOP_CASE_TAC >- EVAL_TAC
  \\ BasicProvers.TOP_CASE_TAC >- EVAL_TAC
  \\ BasicProvers.TOP_CASE_TAC
  >- ( rw[] \\ EVAL_TAC )
  \\ EVAL_TAC);

val peg_eval_list_isSpace_print_sexp = Q.store_thm("peg_eval_list_isSpace_print_sexp",
  `valid_sexp s ⇒
   peg_eval_list sexpPEG (print_sexp s ++ ls, tok isSpace ARB) (print_sexp s ++ ls,[])`,
  strip_tac
  \\ imp_res_tac print_sexp_non_space
  \\ simp[Once peg_eval_list]
  \\ simp[peg_eval_tok_NONE]);

val peg_eval_print_sexp_sxnt_sexp = Q.store_thm("peg_eval_print_sexp_sxnt_sexp",
  `valid_sexp s ⇒
   (peg_eval sexpPEG (print_sexp s ++ ls, pnt sxnt_sexp) =
    peg_eval sexpPEG (print_sexp s ++ ls, pnt sxnt_sexp0 <~ rpt (tok isSpace ARB) (K ARB)))`,
  strip_tac \\ simp[FUN_EQ_THM,pnt_def]
  \\ Cases
  >- (
    simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,ignoreR_def,peg_eval_seq_NONE,pnt_def]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,ignoreL_def,peg_eval_seq_NONE,peg_eval_rpt,PULL_EXISTS]
    \\ rw[EQ_IMP_THM] \\ fs[pnt_def]
    \\ metis_tac[peg_deterministic,peg_eval_list_isSpace_print_sexp,pairTheory.PAIR_EQ] )
  \\ qmatch_goalsub_rename_tac`SOME p` \\ Cases_on`p`
  \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,ignoreR_def,peg_eval_seq_SOME,pnt_def]
  \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,ignoreL_def,peg_eval_seq_SOME,peg_eval_rpt,PULL_EXISTS]
  \\ rw[EQ_IMP_THM] \\ fs[pnt_def,peg_eval_seq_SOME,peg_eval_rpt,PULL_EXISTS]
  \\ metis_tac[peg_deterministic,peg_eval_list_isSpace_print_sexp,pairTheory.PAIR_EQ]);

val nt_rank_def = Define`
  (nt_rank sxnt_normstrchar = 0n) ∧
  (nt_rank sxnt_escapedstrchar = 0) ∧
  (nt_rank sxnt_strchar = 0) ∧
  (nt_rank sxnt_strcontents = 1) ∧
  (nt_rank sxnt_sexp0 = 2) ∧
  (nt_rank sxnt_sexp = 3) ∧
  (nt_rank _ = 0)`;
val _ = export_rewrites["nt_rank_def"];

val print_nt_def = tDefine"print_nt"`
  (print_nt (sxnt_normstrchar) (SX_SYM [c]) =
     if isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\" then SOME [c] else NONE) ∧
  (print_nt (sxnt_normstrchar) _ = NONE) ∧
  (print_nt (sxnt_escapedstrchar) (SX_SYM [c]) =
    if c = #"\\" ∨ c = #"\"" then SOME [c] else NONE) ∧
  (print_nt (sxnt_strchar) (SX_SYM [c]) =
    if c = #"\\" ∨ c = #"\"" then SOME (#"\\"::[c]) else
    if isPrint c then SOME [c] else NONE) ∧
  (print_nt sxnt_strcontents (SX_STR str) =
    FOLDR (λc a. OPTION_MAP2 (++) (print_nt sxnt_strchar (SX_SYM [c])) a)
          (SOME "") str) ∧
  (print_nt sxnt_sexp0 (SX_STR str) =
    OPTION_MAP (λs. "\"" ++ s ++ "\"")
      (print_nt sxnt_strcontents (SX_STR str))) ∧
  (print_nt sxnt_sexp sx = print_nt sxnt_sexp0 sx) ∧
  (print_nt _ _ = NONE)`
 (WF_REL_TAC`measure nt_rank LEX measure sexp_size`
  \\ rw[]);

val print_nt_ind = theorem"print_nt_ind";

val print_nt_sexp0_no_leading_space = Q.store_thm("print_nt_sexp0_no_leading_space",
  `print_nt sxnt_sexp0 s = SOME str ⇒ str ≠ [] ∧ ¬ isSpace (HD str)`,
  Cases_on`s` \\ rw[print_nt_def] \\ rw[] \\ EVAL_TAC);

val stoppers_def = Define`
  (stoppers sxnt_normstrchar = UNIV) ∧
  (stoppers sxnt_escapedstrchar = UNIV) ∧
  (stoppers sxnt_strchar = UNIV) ∧
  (stoppers sxnt_strcontents = {#"\""}) ∧
  (stoppers sxnt_sexp0 = UNIV) ∧
  (stoppers sxnt_sexp = UNIV DIFF isSpace)`;

val peg_eval_sexp_sexp0 = Q.store_thm("peg_eval_sexp_sexp0",
  `peg_eval sexpPEG (str ++ rst, pnt sxnt_sexp0) (SOME (rst,s)) ∧
   (str ≠ [] ⇒ ¬isSpace (HD str)) ∧
   (rst ≠ [] ⇒ ¬isSpace (HD rst)) ⇒
   peg_eval sexpPEG (str ++ rst, pnt sxnt_sexp) (SOME (rst,s))`,
  strip_tac
  \\ rw[Ntimes pnt_def 2,Ntimes peg_eval_NT_SOME 2,FDOM_sexpPEG,sexpPEG_applied,
        ignoreR_def,ignoreL_def,peg_eval_seq_SOME,PULL_EXISTS,peg_eval_rpt]
  \\ qspec_then`str++rst`(mp_tac o Q.GEN`a`)
       (Q.ISPECL[`isSpace`,`sexpPEG`](Q.GENL[`G`,`P`]peg_eval_list_tok_nil))
  \\ disch_then(qspec_then`ARB`mp_tac)
  \\ impl_tac
  >- (
    spose_not_then strip_assume_tac
    \\ Cases_on`str` \\ rfs[] )
  \\ strip_tac
  \\ first_assum(part_match_exists_tac(hd o strip_conj) o concl) \\ simp[]
  \\ first_assum(part_match_exists_tac(hd o strip_conj) o concl) \\ simp[]
  \\ qspec_then`rst`(mp_tac o Q.GEN`a`)
       (Q.ISPECL[`isSpace`,`sexpPEG`](Q.GENL[`G`,`P`]peg_eval_list_tok_nil))
  \\ disch_then(qspec_then`ARB`mp_tac)
  \\ impl_tac >- (CCONTR_TAC \\ fs[])
  \\ strip_tac
  \\ first_assum(part_match_exists_tac(hd o strip_conj) o concl) \\ simp[]);

val peg_eval_print_nt = Q.store_thm("peg_eval_print_nt",
  `∀nt s str rst. print_nt nt s = SOME str ∧ (rst ≠ [] ⇒ HD rst ∈ stoppers nt)
  ⇒ peg_eval sexpPEG (str ++ rst, pnt nt) (SOME (rst,s))`,
  ho_match_mp_tac print_nt_ind
  \\ rpt conj_tac
  \\ TRY (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_tok_SOME,peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_NONE,
       ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_seq_NONE] \\ fs[] \\ NO_TAC)
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_rpt,peg_eval_choicel_CONS,ignoreL_def,ignoreR_def,
       peg_eval_seq_NONE,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ qpat_assum`_ = SOME _`mp_tac
    \\ qid_spec_tac`str'`
    \\ Induct_on`str` \\ rw[] \\ fs[]
    >- (
      Cases_on`rst`
      >- (
        simp[Once peg_eval_list]
        \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ simp[peg_eval_choicel_CONS,peg_eval_tok_NONE,tokeq_def,
                ignoreL_def,peg_eval_seq_NONE,pnt_def]
        \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ simp[peg_eval_tok_NONE]
        \\ qexists_tac`[]` \\  simp[])
      \\ fs[]
      \\ simp[Once peg_eval_list]
      \\ fs[stoppers_def]
      \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
              peg_eval_choicel_CONS,ignoreR_def,ignoreL_def]
      \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
      \\ simp[peg_eval_choicel_CONS,peg_eval_tok_NONE,tokeq_def,
              ignoreL_def,peg_eval_seq_NONE,pnt_def]
      \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
      \\ simp[peg_eval_choicel_CONS,peg_eval_tok_NONE,tokeq_def,
              ignoreL_def,peg_eval_seq_NONE,pnt_def]
      \\ qexists_tac`[]` \\ simp[])
    \\ (
      rw[Once peg_eval_list,PULL_EXISTS,
         peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
         peg_eval_choicel_CONS,ignoreR_def,ignoreL_def,
         peg_eval_seq_SOME,peg_eval_seq_NONE,tokeq_def,
         peg_eval_tok_NONE,peg_eval_tok_SOME,pnt_def]
      \\ fs[destSXSYM_def]
      \\ first_assum(part_match_exists_tac(hd o strip_conj) o concl)
      \\ simp[] ))
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_rpt,peg_eval_choicel_CONS,ignoreL_def,ignoreR_def,
       peg_eval_seq_NONE,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ simp[stringTheory.isDigit_def]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_seq_NONE,pnt_def]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE]
    \\ simp[stringTheory.isDigit_def]
    \\ disj1_tac
    \\ REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
    \\ ONCE_REWRITE_TAC[GSYM rich_listTheory.CONS_APPEND]
    \\ first_x_assum match_mp_tac
    \\ simp[stoppers_def] )
  >- (
    rw[print_nt_def] \\ fs[]
    \\ match_mp_tac peg_eval_sexp_sexp0
    \\ conj_tac
    >- (
      first_x_assum match_mp_tac
      \\ simp[stoppers_def] )
    \\ imp_res_tac print_nt_sexp0_no_leading_space
    \\ fs[stoppers_def,IN_DEF]));

val print_nt_print_sexp = Q.store_thm("print_nt_print_sexp",
  `∀s. valid_sexp s ⇒ (print_nt sxnt_sexp s = SOME (print_sexp s)) `,
  ho_match_mp_tac(theorem"print_sexp_ind")
  \\ conj_tac >- cheat
  \\ conj_tac >- cheat
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
    \\ qpat_assum`_ = _`mp_tac
    \\ simp[Once escape_string_def]
    \\ IF_CASES_TAC \\ fs[] \\ strip_tac \\ rpt var_eq_tac
    \\ IF_CASES_TAC \\ fs[] )
  \\ rw[] \\ fs[]
  \\ cheat);

val peg_eval_print_sexp = Q.store_thm("peg_eval_print_sexp",
  `∀s. valid_sexp s ⇒
       peg_eval sexpPEG (print_sexp s,sexpPEG.start) (SOME ("",s))`,
  rw[]
  \\ imp_res_tac print_nt_print_sexp
  \\ imp_res_tac peg_eval_print_nt
  \\ first_x_assum(qspec_then`[]`mp_tac)
  \\ simp[]);

val parse_print = Q.store_thm("parse_print",
  `valid_sexp s ⇒ parse_sexp (print_sexp s) = SOME s`,
  rw[parse_sexp_def,pairTheory.EXISTS_PROD]
  \\ imp_res_tac peg_eval_print_sexp
  \\ simp[pegparse_eq_SOME,wfG_sexpPEG]
  \\ fs[]
  \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
  \\ simp[]);

(*
val cs = listLib.list_compset()
val () = pegLib.add_peg_compset cs
val () = computeLib.add_thms[sexpPEG_exec_thm,pnt_def,ignoreR_def,ignoreL_def,tokeq_def,pegf_def]cs
  simp[MATCH_MP peg_eval_executed
       (CONJ wfG_sexpPEG (EQT_ELIM(SIMP_CONV(srw_ss())[sexpPEG_def,Gexprs_sexpPEG]``sexpPEG.start ∈ Gexprs sexpPEG``)))] >>
  CONV_TAC(computeLib.CBV_CONV cs) >>
  IF_CASES_TAC >- fs[stringTheory.isGraph_def] >>
  simp[choicel_def] >>
  CONV_TAC(computeLib.CBV_CONV cs) >> simp[] >>
*)

val _ = export_theory()
