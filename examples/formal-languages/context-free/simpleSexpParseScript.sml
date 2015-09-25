open HolKernel boolLib bossLib lcsymtacs finite_mapSyntax
open ASCIInumbersTheory simpleSexpTheory
open simpleSexpPEGTheory pegTheory pegexecTheory

val _ = new_theory"simpleSexpParse"

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

(*
val peg_eval_print_sexp = Q.prove(
  `∀s. valid_sexp s ⇒
       peg_eval sexpPEG (print_sexp s,sexpPEG.start) (SOME ("",s))`,
  ho_match_mp_tac(theorem"print_sexp_ind") >>
  strip_tac >- (
    rw[print_sexp_def]

val parse_print = Q.store_thm("parse_print",
  `parse_sexp (print_sexp s) = SOME s`,
  rw[parse_sexp_def] >>
  Cases_on`pegparse sexpPEG (print_sexp s)` >> simp[] >- (
    imp_res_tac pegparse_eq_NONE >> fs[PEG_wellformed] >>
    f"peg_eval"
  reverse(Induct_on`s`)
  >- (
    rw[print_sexp_def] >>
    rw[parse_sexp_def] >>
    pegparse_eq_SOME
*)

val _ = export_theory()
