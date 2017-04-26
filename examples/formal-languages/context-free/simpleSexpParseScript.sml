open HolKernel boolLib bossLib lcsymtacs finite_mapSyntax
open ASCIInumbersTheory simpleSexpTheory
open simpleSexpPEGTheory pegTheory pegexecTheory

val _ = new_theory"simpleSexpParse"

(* TODO: move *)

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

val n2s_not_null = Q.store_thm("n2s_not_null",
  `∀n. ¬NULL(n2s 10 HEX n)`,
  rw[n2s_def,listTheory.NULL_EQ]
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
  `∀ls. (ls = [] ∨ ¬ P(FST(HD ls))) ⇒
   peg_eval_list G (ls, tok P a) (ls,[])`,
  rw[Once peg_eval_list,peg_eval_tok_NONE,listTheory.EVERY_MEM]
  \\ Cases_on`ls` \\ fs[]
  \\ Cases_on`h` \\ fs[]);

val peg_eval_list_tok_imp_every = Q.store_thm("peg_eval_list_tok_imp_every",
  `∀ls r z. peg_eval_list G (ls, tok P a) (r,z) ⇒
   ∃l. ls = l ++ r ∧ EVERY (P o FST) l ∧ (¬NULL r ⇒ ¬P (FST(HD r)))`,
  Induct \\ rw[Once peg_eval_list,listTheory.NULL_EQ,peg_eval_tok_SOME]
  \\ fs[peg_eval_tok_NONE]
  \\ res_tac
  \\ rpt var_eq_tac
  \\ qexists_tac`h::l`
  \\ rw[] \\ fs[listTheory.NULL_EQ]);

val peg_eval_list_tok_every_imp = Q.store_thm("peg_eval_list_tok_every_imp",
  `∀ls x rst. EVERY (P o FST) ls ∧ ¬ (P o FST) x ⇒
   peg_eval_list G (ls ++ [x] ++ rst, tok P a) ([x] ++ rst, MAP a ls)`,
  Induct \\ simp[] \\ simp[Once peg_eval_list]
  \\ simp[peg_eval_tok_NONE]
  \\ rw[]
  \\ Cases_on `x`
  \\ TRY(Cases_on `h`\\ fs[])
  \\ fs[peg_eval_tok_SOME]);

val FOLDR_STRCAT_destSXSYM = Q.prove(
  `∀ls. FOLDR (λs a. STRCAT (destSXSYM s) a) "" (MAP (λc. SX_SYM (STRING c "")) ls) = ls`,
  Induct >> simp[destSXSYM_def]);

val FOLDR_STRCAT_destSXSYM_FST = Q.prove(
  `∀ls. FOLDR (λs a. STRCAT (destSXSYM s) a) "" (MAP (λ(c,l). SX_SYM (STRING c "")) ls) = MAP FST ls`,
  Induct >> simp[destSXSYM_def,pairTheory.FORALL_PROD]);

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

val peg_eval_list_valid_symchars = Q.prove(
  `∀cs. EVERY valid_symchar (MAP FST cs) ⇒
        peg_eval_list sexpPEG (cs,tok valid_symchar (λ(c,l). SX_SYM [c]))
                                  ([],MAP (λc. SX_SYM [c]) (MAP FST cs))`,
  Induct >> simp[Once peg_eval_cases] >> simp[Once peg_eval_cases] >>
  strip_tac >> Cases_on `h` >> simp[])

val peg_eval_valid_symchars = Q.prove(
  `∀cs. EVERY valid_symchar (MAP FST cs) ⇒
       peg_eval sexpPEG
                    (cs,rpt (tok valid_symchar (λ(c,l). SX_SYM (STRING c "")))
                            (SX_SYM o FOLDR (λs a. STRCAT (destSXSYM s) a) []))
                    (SOME ([],SX_SYM (MAP FST cs)))`,
  rw[Once peg_eval_cases] >>
  imp_res_tac peg_eval_list_valid_symchars >>
  metis_tac[FOLDR_STRCAT_destSXSYM]);

val peg_eval_valid_symbol = Q.prove(
  `∀s. valid_symbol (MAP FST s) ⇒
       peg_eval sexpPEG (s,sexpPEG.start) (SOME ([],SX_SYM (MAP FST s)))`,
  Cases_on`s`>>
  simp[pnt_def, peg_eval_NT_SOME, FDOM_sexpPEG, sexpPEG_applied,
       ignoreL_def, ignoreR_def, peg_eval_seq_SOME, peg_eval_rpt] >>
  dsimp[] >> strip_tac >>
  Cases_on`h` >> fs[] >>
  `¬isSpace q` by (strip_tac >> Cases_on `q` >> fs[stringTheory.isGraph_def]) >>
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
  map_every qexists_tac[`[]`,`[]`,`l`] >>
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
  `peg_eval_list sexpPEG (map_loc (toString n) 0,tok isSpace ARB)
                             (map_loc (toString n) 0 ,[])`,
  match_mp_tac peg_eval_list_tok_nil
  \\ assume_tac EVERY_isDigit_num_to_dec_string
  \\ fs[listTheory.EVERY_MEM] \\ rw[]
  \\ Cases_on`toString n` \\ fs[]
  \\ fs[stringTheory.isDigit_def,stringTheory.isSpace_def]
  \\ spose_not_then strip_assume_tac
  \\ fs[locationTheory.map_loc_def]
  \\ first_x_assum(qspec_then`h`mp_tac)
  \\ simp[]);

val peg_eval_list_digits = Q.store_thm("peg_eval_list_digits",
  `∀s. EVERY isDigit (MAP FST s) ∧ (rst ≠ [] ⇒ ¬ isDigit (FST (HD rst))) ⇒
   peg_eval_list sexpPEG (s ++ rst,nt(mkNT sxnt_digit) I) (rst,MAP (SX_NUM o
   combin$C $- 48 o ORD) (MAP FST s))`,
  Induct \\ simp[Once peg_eval_list]
  >- (
    simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE]
    \\ Cases_on`rst` \\ fs[]
    \\ Cases_on`h` \\ fs[] )
  \\ rw[] \\ fs[]
  \\ Cases_on`h` \\ fs[]
  \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
  \\ simp[peg_eval_tok_SOME]);

val peg_eval_list_chars = Q.store_thm("peg_eval_list_chars",
  `∀loc l1 l2. EVERY isPrint l1 ⇒
    escape_string l1 = MAP FST l2  ⇒
    peg_eval_list sexpPEG (l2 ++[(#"\"",loc)], nt (mkNT sxnt_strchar) I)
                          ([(#"\"",loc)],MAP (λc. SX_SYM [c]) l1)`,
  strip_tac
  \\ Induct \\ simp[Once escape_string_def]
  >- (
    simp[Once peg_eval_list]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_choicel_CONS,pnt_def]
    \\ simp[ignoreL_def,peg_eval_seq_NONE,tokeq_def,peg_eval_tok_NONE]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE])
  \\ rw[] \\ fs[] \\ simp[Once peg_eval_list]
  \\ Cases_on`l2` \\ fs[]
  THENL[(Cases_on`t` \\ fs[] \\ `MAP FST t' = MAP FST t'` by simp[]),
        (Cases_on`t` \\ fs[] \\ `MAP FST t' = MAP FST t'` by simp[]),
        `MAP FST t = MAP FST t` by simp[]]
  \\ res_tac
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
  \\ simp[]
  \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  THENL[Cases_on `h'`, Cases_on`h`, Cases_on`h'`]
  \\ simp[peg_eval_choicel_CONS]
  THENL[disj1_tac, disj1_tac, disj2_tac]
  \\ simp[ignoreL_def,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_SOME,pnt_def,peg_eval_seq_NONE,peg_eval_tok_NONE]
  \\ simp[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ simp[peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_SOME,peg_eval_tok_NONE]
  \\ metis_tac[]);


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
    Induct_on`str` \\ rw[listTheory.list_size_def] \\ fs[] \\ NO_TAC)
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
    rw[GSYM listTheory.NULL_EQ,num_to_dec_string_not_null]
    \\ NO_TAC)
  \\ TRY (
    qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[listTheory.NULL_EQ]
    \\ Cases_on`toString n` \\ fs[]
    \\ assume_tac EVERY_isDigit_num_to_dec_string
    \\ rfs[]
    \\ fs[stringTheory.isSpace_def,stringTheory.isDigit_def]
    \\ NO_TAC)
  \\ every_case_tac \\ fs[listTheory.NULL_EQ]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ fs[stringTheory.isGraph_def,stringTheory.isSpace_def]);

val print_nt_sexp0_no_leading_rparen = Q.store_thm("print_nt_sexp0_no_leading_rparen",
  `print_nt sxnt_sexp0 s = SOME str ⇒ str ≠ [] ∧ HD str ≠ #")"`,
  Cases_on`s` \\ rw[print_nt_def] \\ rw[]
  \\ TRY (
    rw[GSYM listTheory.NULL_EQ,num_to_dec_string_not_null]
    \\ NO_TAC)
  \\ TRY (
    qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[listTheory.NULL_EQ]
    \\ Cases_on`toString n` \\ fs[]
    \\ assume_tac EVERY_isDigit_num_to_dec_string
    \\ rfs[]
    \\ spose_not_then strip_assume_tac
    \\ fs[stringTheory.isSpace_def,stringTheory.isDigit_def]
    \\ NO_TAC)
  \\ every_case_tac \\ fs[listTheory.NULL_EQ]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ fs[stringTheory.isGraph_def,stringTheory.isSpace_def]);

val peg_eval_sexp_sexp0 = Q.store_thm("peg_eval_sexp_sexp0",
  `peg_eval sexpPEG (str ++ rst, pnt sxnt_sexp0) (SOME (rst,s)) ∧
   (str ≠ [] ⇒ ¬isSpace (FST(HD str))) ∧
   (rst ≠ [] ⇒ ¬isSpace (FST(HD rst))) ⇒
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

val peg_eval_sexp0_NONE = Q.store_thm("peg_eval_sexp0_NONE",
  `c = #")" ∨ c = #"." ⇒
    ((peg_eval sexpPEG ((c,l)::rst,nt (mkNT sxnt_sexp0) I) res) ⇔ (res = NONE))`,
  rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS]
  \\ rw[tokeq_def,pnt_def,pegf_def,ignoreR_def,ignoreL_def]
  \\ rw[peg_eval_seq_SOME,peg_eval_seq_NONE,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_tok_SOME,peg_eval_tok_NONE]
  \\ rw[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_tok_SOME]
  \\ EVAL_TAC \\ rw[]
  \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_seq_SOME,peg_eval_seq_NONE,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_tok_SOME,peg_eval_tok_NONE]
  \\ rw[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_tok_SOME]
  \\ EVAL_TAC \\ rw[]
  \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_tok_SOME,peg_eval_tok_NONE]
  \\ EVAL_TAC \\ rw[]
  \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_seq_SOME,peg_eval_seq_NONE,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied]
  \\ rw[peg_eval_tok_SOME,peg_eval_tok_NONE]);

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

val peg_eval_print_nt = Q.store_thm("peg_eval_print_nt",
  `∀nt s strl rst str. print_nt nt s = SOME str ∧ (rst ≠ [] ⇒ FST(HD rst) ∈ stoppers nt)
   ⇒ MAP FST strl = str
   ⇒ peg_eval sexpPEG (strl ++ rst, pnt nt) (SOME (rst,s))`,
  ho_match_mp_tac print_nt_ind
  \\ rpt conj_tac
  \\ TRY (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_tok_SOME,peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_NONE,
       ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_seq_NONE] \\ fs[]
       \\ Cases_on`x0`\\ fs[] \\ NO_TAC)
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_tok_SOME,peg_eval_choicel_CONS,tokeq_def,peg_eval_tok_NONE,
       ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_seq_NONE] \\ fs[]
    \\ TRY(Cases_on`strl` \\ fs[]\\ fs[])
    \\ TRY(Cases_on`strl` \\ fs[]\\ fs[])
    \\ Cases_on `h` \\ TRY(Cases_on `x0`) \\ fs[]
    \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[])
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_rpt,peg_eval_choicel_CONS,ignoreL_def,ignoreR_def,
       peg_eval_seq_NONE,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ fs[PULL_EXISTS,pairTheory.EXISTS_PROD] \\ fs[]
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ qid_spec_tac`strl`
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
    \\ TRY (
      Cases_on`strl` \\ fs[]\\ fs[]
      \\ Cases_on `h` \\ fs[]
      \\ Cases_on`t` \\ fs[]\\ fs[]
      \\ Cases_on `h` \\ fs[] \\
      rw[Once peg_eval_list,PULL_EXISTS,
         peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
         peg_eval_choicel_CONS,ignoreR_def,ignoreL_def,
         peg_eval_seq_SOME,peg_eval_seq_NONE,tokeq_def,
         peg_eval_tok_NONE,peg_eval_tok_SOME,pnt_def]
      \\ fs[destSXSYM_def] \\ NO_TAC)
    \\ Cases_on`strl` \\ fs[] \\ rw[]
    \\ rw[Once peg_eval_list,PULL_EXISTS,
          peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
          peg_eval_choicel_CONS,ignoreR_def,ignoreL_def,
          peg_eval_seq_SOME,peg_eval_seq_NONE,tokeq_def,
          peg_eval_tok_NONE,peg_eval_tok_SOME,pnt_def]
    \\ rw[pairTheory.UNCURRY,destSXSYM_def] )
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_seq_SOME,peg_eval_rpt,peg_eval_tok_SOME,PULL_EXISTS]
    \\ Cases_on`strl` \\ fs[destSXSYM_def]
    \\ Cases_on `h` \\ fs[destSXSYM_def]
    \\ Cases_on`rst` \\ fs[]
    >- (
      imp_res_tac peg_eval_list_valid_symchars
      \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
      \\ simp[FOLDR_STRCAT_destSXSYM] )
    \\ fs[stoppers_def]
    \\ pop_assum mp_tac \\ simp_tac std_ss [IN_DEF] \\ strip_tac
    \\ imp_res_tac peg_eval_valid_symchars
    \\ qhdtm_x_assum`EVERY`mp_tac
    \\ simp[listTheory.EVERY_MAP,Once(GSYM combinTheory.o_DEF)]
    \\ strip_tac
    \\ first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
         (Q.ISPEC`sexpPEG`(Q.GEN`G`(Q.ISPEC`λ(c,l:locs). SX_SYM[c]`(Q.GEN`a`peg_eval_list_tok_every_imp))))))
    \\ simp_tac std_ss [combinTheory.o_DEF]
    \\ disch_then(fn th=> first_assum (mp_tac o MATCH_MP th))
    \\ simp[]
    \\ qmatch_goalsub_rename_tac`(c::cs,_)`
    \\ disch_then(qspec_then`cs`mp_tac) \\ rw[]
    \\ ONCE_REWRITE_TAC[rich_listTheory.CONS_APPEND]
    \\ rw[]
    \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
    \\ rw[FOLDR_STRCAT_destSXSYM_FST] )
  >- cheat (*
  >- (
    rw[print_nt_def]
    \\ pairarg_tac \\ fs[] \\ rpt var_eq_tac
    \\ fs[option_sequence_SOME] \\ rw[]
    \\ rw[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS]
    \\ Cases_on`NULL ls` \\ fs[]
    >- (
      fs[listTheory.NULL_EQ,print_space_separated_def]
      \\ Cases_on`n` \\ fs[] \\ rw[]
      \\ disj1_tac
      \\ rw[pegf_def,peg_eval_seq_SOME,tokeq_def,grabWS_def,ignoreL_def,peg_eval_tok_SOME,peg_eval_rpt,PULL_EXISTS]
      \\ fs[Once strip_dot_def]
      \\ Cases_on`s` \\ fs[]
      \\ TRY(pairarg_tac \\ fs[])
      \\ pop_assum mp_tac \\ rw[]
      \\ qexists_tac`[]`
      \\ qexists_tac`x0` \\ rw[]
      \\ match_mp_tac peg_eval_list_tok_nil
      \\ Cases_on `x0` \\ fs[]
      \\ var_eq_tac
      \\ EVAL_TAC)
    \\ disj2_tac
    \\ conj_tac
    >- (
      rw[pegf_def,peg_eval_seq_NONE,grabWS_def,ignoreL_def,peg_eval_rpt,PULL_EXISTS,tokeq_def,peg_eval_tok_NONE]
      \\ Cases_on`ls` \\ fs[optionTheory.IS_SOME_EXISTS]
      \\ imp_res_tac print_nt_sexp0_no_leading_space
      \\ qpat_abbrev_tac`ls = _ ++ rst`
      \\ map_every qexists_tac[`ls`,`[]`]
      \\ simp[Abbr`ls`]
      \\ Cases_on`x` \\ fs[]
      \\ imp_res_tac print_nt_sexp0_no_leading_rparen
      \\ fs[]
      \\ reverse conj_tac
      >- ( Cases_on`t` \\ fs[print_space_separated_def] )
      >- cheat
      \\ match_mp_tac peg_eval_list_tok_nil
      \\ fs[]
      \\ Cases_on`t` \\ fs[print_space_separated_def]
      \\ cheat
      )
    \\ rw[peg_eval_seq_SOME]
    \\ qpat_x_assum`strip_dot _ = _`mp_tac
    \\ simp[Once strip_dot_def]
    \\ CASE_TAC \\ fs[]
    \\ TRY (
      rw[] \\ spose_not_then strip_assume_tac \\ fs[] \\ rw[] \\ fs[] \\ NO_TAC)
    \\ pairarg_tac \\ fs[] \\ rw[] \\ fs[]
    \\ fs[optionTheory.IS_SOME_EXISTS]
    \\ rw[grabWS_def,ignoreL_def,peg_eval_seq_SOME,PULL_EXISTS,peg_eval_rpt]
    \\ fs[pnt_def,stoppers_def]
    \\ qpat_abbrev_tac`ls = _ ++ rst`
    \\ CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["i1''","l"]))
    \\ map_every qexists_tac[`ls`,`[]`]
    \\ simp[RIGHT_EXISTS_AND_THM]
    \\ conj_tac
    >- (
      match_mp_tac peg_eval_list_tok_nil
      \\ simp[Abbr`ls`,print_space_separated_cons]
      \\ imp_res_tac print_nt_sexp0_no_leading_space
      \\ Cases_on`x` \\ fs[] )
    \\ qmatch_asmsub_rename_tac`print_nt sxnt_sexp0 s1 = SOME x1`
    \\ first_assum(qspec_then`s1`mp_tac)
    \\ impl_tac >- rw[]
    \\ disch_then (fn th => first_assum (assume_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]th)))
    \\ simp[Abbr`ls`,print_space_separated_cons]
    \\ REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`x1 ++ rst1`
    \\ qexists_tac`rst1`
    \\ conj_tac
    >- (
      first_x_assum match_mp_tac
      \\ reverse(rw[Abbr`rst1`,IN_DEF])
      >- EVAL_TAC
      \\ Cases_on`n` \\ fs[] \\ rw[]
      \\ EVAL_TAC )
    \\ qmatch_asmsub_rename_tac`EVERY _ (MAP _ ls)`
    \\ fsrw_tac[boolSimps.ETA_ss][]
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ qpat_x_assum`_ = SOME l2`mp_tac
    \\ qpat_x_assum`∀x. SOME x = n ⇒ _`mp_tac
    \\ map_every qid_spec_tac[`n`,`s0`]
    \\ simp[Abbr`rst1`]
    \\ fsrw_tac[boolSimps.DNF_ss][]
    \\ qid_spec_tac`l2`
    \\ Induct_on`ls`
    >- (
      rw[]
      \\ Cases_on`n` \\ fs[] \\ rw[]
      >- (
        rw[Once peg_eval_list,peg_eval_seq_NONE,peg_eval_rpt]
        \\ rw[Once peg_eval_list,peg_eval_tok_NONE,stringTheory.isSpace_def,peg_eval_tok_SOME]
        \\ rw[peg_eval_sexp0_NONE]
        \\ rw[peg_eval_seq_SOME,peg_eval_rpt,PULL_EXISTS]
        \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
        \\ rw[stringTheory.isSpace_def]
        \\ rw[peg_eval_sexp0_NONE]
        \\ rw[peg_eval_choicel_CONS,pegf_def,peg_eval_seq_SOME,
              peg_eval_seq_NONE,peg_eval_rpt,PULL_EXISTS,tokeq_def,
              ignoreR_def,ignoreL_def]
        \\ rw[peg_eval_tok_NONE,peg_eval_tok_SOME]
        \\ rw[replace_nil_def]
        \\ rw[Once peg_eval_list]
        \\ rw[peg_eval_tok_NONE,peg_eval_tok_SOME]
        \\ rw[stringTheory.isSpace_def]
        \\ fs[Once strip_dot_def]
        \\ pop_assum mp_tac \\ CASE_TAC \\ fs[] \\ rw[]
        \\ pairarg_tac \\ fs[] )
      \\ rw[Once peg_eval_list,peg_eval_seq_NONE,peg_eval_rpt,PULL_EXISTS,peg_eval_seq_SOME]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[peg_eval_sexp0_NONE]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[peg_eval_sexp0_NONE]
      \\ rw[peg_eval_choicel_CONS,pegf_def,peg_eval_seq_SOME,
            peg_eval_seq_NONE,peg_eval_rpt,PULL_EXISTS,tokeq_def,
            ignoreR_def,ignoreL_def]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
      \\ rw[replace_nil_def] \\ fs[]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ imp_res_tac print_nt_sexp0_no_leading_space
      \\ Cases_on`z` \\ fs[]
      \\ `s0 = x`
      by (
        qhdtm_x_assum`strip_dot`mp_tac
        \\ simp[Once strip_dot_def]
        \\ CASE_TAC \\ rw[]
        \\ pairarg_tac \\ fs[] )
      \\ rw[]
      \\ first_x_assum(qspec_then`")"++rst`mp_tac)
      \\ simp[]
      \\ impl_tac >- (simp[IN_DEF] \\ EVAL_TAC)
      \\ strip_tac
      \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
      \\ simp[]
      \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ rw[stringTheory.isSpace_def,PULL_EXISTS] )
    \\ rw[] \\ fs[]
    \\ fs[optionTheory.IS_SOME_EXISTS]
    \\ simp[print_space_separated_cons]
    \\ qpat_abbrev_tac`rst2 =  _ ++ rst`
    \\ rw[Once peg_eval_list]
    \\ srw_tac[boolSimps.DNF_ss][]
    \\ disj2_tac
    \\ simp[peg_eval_seq_SOME,peg_eval_rpt,PULL_EXISTS]
    \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ rw[stringTheory.isSpace_def,PULL_EXISTS]
    \\ imp_res_tac print_nt_sexp0_no_leading_space
    \\ simp[Abbr`rst2`]
    \\ REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`x ++ rst2`
    \\ rw[Once peg_eval_list,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ Cases_on`x` \\ fs[]
    \\ last_x_assum(qspec_then`h`mp_tac)
    \\ simp[] \\ disch_then(qspec_then`rst2`mp_tac)
    \\ impl_tac
    >- (
      reverse(rw[Abbr`rst2`])
      >- (simp[IN_DEF] \\ EVAL_TAC)
      \\ Cases_on`n` \\ fs[] \\ rw[]
      \\ simp[IN_DEF] \\ EVAL_TAC )
    \\ rw[]
    \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl)
    \\ rw[]
    \\ rw[replace_nil_def]
    \\ qhdtm_x_assum`strip_dot`mp_tac
    \\ simp[Once strip_dot_def]
    \\ CASE_TAC \\ rw[]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ first_x_assum(qspecl_then[`l2`,`s0'`,`n`]mp_tac)
    \\ simp[])
  *)
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_rpt,peg_eval_choicel_CONS,ignoreL_def,ignoreR_def,
       peg_eval_seq_NONE,peg_eval_seq_SOME,tokeq_def,peg_eval_tok_NONE,peg_eval_tok_SOME]
    \\ Cases_on`strl` \\ fs[]\\ fs[]
    \\ simp[stringTheory.isDigit_def]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_seq_NONE,pnt_def]
    \\ simp[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
    \\ simp[peg_eval_tok_NONE]
    \\ simp[stringTheory.isDigit_def]
    \\ disj1_tac
    \\ `t ≠ []` by (Cases_on`t` \\ fs[])
    \\ imp_res_tac listTheory.APPEND_FRONT_LAST
    \\ pop_assum(SUBST_ALL_TAC o SYM) \\ fs[]
    \\ simp[PULL_EXISTS]
    \\ first_x_assum (qspecl_then[`FRONT t`,`[LAST t] ++ rst`]mp_tac)
    \\ impl_tac >- simp[stoppers_def] \\ rw[]
    \\ metis_tac[])
  >- (
    rw[print_nt_def,pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,
       peg_eval_seq_SOME,peg_eval_rpt,peg_eval_tok_SOME]
    \\ qspec_then`n`mp_tac num_to_dec_string_not_null
    \\ rw[listTheory.NULL_EQ]
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
    \\ fs[pairTheory.UNCURRY,destSXCONS_def,destSXNUM_def,rich_listTheory.FOLDL_MAP]
    \\ qmatch_assum_abbrev_tac`FOLDL f a t = _`
    \\ `∀ls a . FST (FOLDL f a ls) = FST a * 10 ** (LENGTH ls)`
    by ( Induct \\ simp[Abbr`f`,arithmeticTheory.EXP])
    \\ first_x_assum(qspecl_then[`t`,`a`]mp_tac)
    \\ rw[Abbr`a`]
    \\ `∀ls a. EVERY isDigit (MAP FST ls) ⇒
          SND (FOLDL f a ls) = (10 ** LENGTH ls * SND a + (l2n 10 (MAP (combin$C $- 48 o ORD) (REVERSE (MAP FST ls)))))`
    by (
      qunabbrev_tac`f` \\ rpt (pop_assum kall_tac)
      \\ ho_match_mp_tac listTheory.SNOC_INDUCT
      \\ rw[numposrepTheory.l2n_def,listTheory.FOLDL_SNOC,listTheory.EVERY_SNOC,
            listTheory.MAP_SNOC,listTheory.REVERSE_SNOC,arithmeticTheory.EXP]
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
    \\ fs[pairTheory.UNCURRY,destSXSYM_def]
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
            peg_eval_tok_NONE,peg_eval_tok_SOME,stringTheory.isDigit_def,
            tokeq_def,ignoreR_def,ignoreL_def,pegf_def]
      >- (
        rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ rw[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
              pnt_def,peg_eval_seq_SOME,peg_eval_seq_NONE,
              peg_eval_tok_NONE,peg_eval_tok_SOME,stringTheory.isDigit_def,
              tokeq_def,ignoreR_def,ignoreL_def]
        \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied]
        \\ rw[peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS,
              pnt_def,peg_eval_seq_SOME,peg_eval_seq_NONE,
              peg_eval_tok_NONE,peg_eval_tok_SOME,stringTheory.isDigit_def] )
      \\ rw[grabWS_def,ignoreR_def,ignoreL_def,peg_eval_seq_SOME,peg_eval_rpt]
      \\ qmatch_asmsub_rename_tac`dest_quote (SX_CONS a d) = SOME x`
      \\ Cases_on`d` \\ fs[] \\ rw[] \\ rfs[]
      \\ imp_res_tac print_nt_sexp0_no_leading_space
      \\ rw[Once peg_eval_list]
      \\ rw[peg_eval_tok_NONE,peg_eval_tok_SOME]
      \\ Cases_on`t` \\ fs[]
      \\ once_rewrite_tac[rich_listTheory.CONS_APPEND]
      \\ rewrite_tac[listTheory.APPEND_ASSOC]
      \\ rw[])
    \\ fs[option_sequence_SOME] \\ rw[]
    \\ Cases_on`strl` \\ fs[] \\ rw[]
    \\ rw[pnt_def,peg_eval_NT_SOME,FDOM_sexpPEG,sexpPEG_applied,peg_eval_choicel_CONS]
    \\ Cases_on`NULL ls` \\ fs[]
    >- (
      fs[listTheory.NULL_EQ,print_space_separated_def]
      \\ Cases_on`n` \\ fs[] \\ rw[]
      \\ disj1_tac
      \\ rw[pegf_def,peg_eval_seq_SOME,tokeq_def,grabWS_def,ignoreL_def,peg_eval_tok_SOME,peg_eval_rpt,PULL_EXISTS]
      \\ fs[Once strip_dot_def]
      \\ pairarg_tac \\ fs[])
    \\ disj2_tac
    \\ conj_tac
    >- (
      rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_seq_NONE,pnt_def]
      \\ rw[Once peg_eval_cases,FDOM_sexpPEG,sexpPEG_applied,peg_eval_tok_NONE,stringTheory.isDigit_def] )
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
    \\ fs[listTheory.EVERY_MEM,listTheory.MEM_MAP,optionTheory.IS_SOME_EXISTS,PULL_EXISTS]
    \\ conj_tac
    >- (
      rw[]
      \\ last_x_assum(qspec_then`a`mp_tac)
      \\ impl_tac >- metis_tac[markerTheory.Abbrev_def]
      \\ rw[print_nt_def] )
    \\ AP_TERM_TAC
    \\ simp[listTheory.MAP_MAP_o,listTheory.MAP_EQ_f]
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
  \\ fs[listTheory.EVERY_MEM,listTheory.MEM_MAP,PULL_EXISTS]
  \\ simp[print_space_separated_cons,listTheory.NULL_EQ]
  \\ rw[]
  \\ AP_TERM_TAC
  \\ simp[listTheory.MAP_MAP_o,listTheory.MAP_EQ_f]);

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
  rw[parse_sexp_def,pairTheory.EXISTS_PROD]
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
