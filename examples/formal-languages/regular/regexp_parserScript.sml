open HolKernel Parse boolLib bossLib;

open regexpTheory pegTheory pegexecTheory monadsyntax

val _ = new_theory "regexp_parser";

val _ = temp_add_monadsyntax()

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_MAP_DEF",
                                        "option.OPTION_MAP2_DEF",
                                        "option.OPTION_CHOICE_def"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)
val _ = overload_on ("lift", ``option$OPTION_MAP``)


val _ =
 Datatype
   `reNT = Top
         | Alt
         | Concat
         | Star
         | Atom
         | CharSet
         | BslashSpecial`
;

val _ = overload_on("mkNT", ``INL : reNT -> reNT inf``)

val sumID_def = Define`
  sumID (INL x) = x ∧
  sumID (INR y) = y
`;

val choicel_def = Define`
  choicel [] = not (empty NONE) NONE ∧
  choicel (h::t) = choice h (choicel t) sumID
`;

val pegf_def = Define‘
  pegf sym f = seq sym (empty NONE) (λl1 l2. OPTION_MAP f l1)
’

val try_def = Define`
  try sym = choicel [sym; empty NONE]
`;

val pnt_def = Define‘pnt sym = nt (mkNT sym) I’;

val igLeft_def = Define‘
  igLeft s1 s2 = seq s1 s2 (λl1 l2. l2)
’;
val _ = set_mapped_fixity { tok = "*>", term_name = "igLeft", fixity = Infixl 500 }

val igRight_def = Define‘
  igRight s1 s2 = seq s1 s2 (λl1 l2. l1)
’;

val _ = set_mapped_fixity { tok = "<*", term_name = "igRight", fixity = Infixl 500 }

val igtok_def = Define‘igtok P = tok P (K NONE)’

val DigitSet_def = Define‘
  DigitSet = charset_string "0123456789"
’

val EscapableChar_def = Define‘
  EscapableChar c <=> MEM c "\\.^$*+?|~{}[]()" ∨ ORD c = 96’

val OrM_def = Define‘
  OrM roptlist = OPTION_MAP Or (OPT_MMAP I roptlist)
’

(* breaks abstraction, see TODO on mkNT Charset below *)
val charset_char_def = Define`
  charset_char c = Chset (Charset (n2w (ORD c)) 0w 0w 0w)`;
val uncharset_char_def = Define`
  (uncharset_char (Chset (Charset w _ _ _)) = CHR (w2n (w && 255w))) ∧
  (uncharset_char _ = CHR 0)`;
val uncharset_char_charset_char = Q.store_thm("uncharset_char_charset_char[simp]",
  `uncharset_char (charset_char c) = c`,
  rw[charset_char_def,uncharset_char_def]
  \\ once_rewrite_tac[wordsTheory.WORD_AND_COMM]
  \\ `255n = 2 ** 8 - 1` by simp[] \\ pop_assum SUBST1_TAC
  \\ srw_tac[wordsLib.WORD_ss][wordsTheory.WORD_AND_EXP_SUB1]
  \\ qspec_then`c`strip_assume_tac stringTheory.ORD_BOUND
  \\ rw[stringTheory.CHR_ORD]);

val rePEG_def = Define‘
  rePEG = <|
    start := pnt Top ;
    rules := FEMPTY |++ [
      (mkNT Atom,
       choicel [
         tok ((=) #".") (K (SOME (Chset charset_full)));

         igtok ((=) #"(") *> pnt Top <* igtok ((=) #")");

         igtok ((=) #"[") *> pnt CharSet <* igtok ((=) #"]");

         igtok ((=) #"\\") *> pnt BslashSpecial ;

         not (tok EscapableChar (K NONE)) NONE *>
         any (λcl. SOME (Chset (charset_sing (FST cl))))
       ]);

      (mkNT BslashSpecial,
       choicel [
         tok ((=) #"d") (K (SOME (Chset DigitSet)));
         tok EscapableChar (λcl. SOME (Chset (charset_sing (FST cl))))
       ]);

      (mkNT CharSet,
       (* TODO: add complement, ranges, escaped chars, etc. *)
       (* TODO: this might be better if we weren't forced into the regexp type
       (so could accumulate the list of characters easier), maybe use a sum? *)
       rpt (tok ((<>) #"]") (λcl. SOME (charset_char (FST cl))))
         (λls. OPTION_MAP (Chset o charset_string)
                 (OPT_MMAP (OPTION_MAP uncharset_char) ls)));

      (mkNT Star,
       seq (pnt Atom) (try (tok ((=) #"*") (K (SOME (Chset charset_empty)))))
           (λa_m s_m. do
              a <- a_m ;
              (do s <- s_m ; return (Star a) od ++ return a)
            od));

      (mkNT Concat,
       seq (pnt Star) (try (pnt Concat))
           (λs_m c_m. do
              s <- s_m ;
              (do c <- c_m ; return (Cat s c) od ++ return s)
            od));

      (mkNT Alt,
       seq (pnt Concat) (rpt (igtok ((=) #"|") *> pnt Concat) OrM)
           (λc_m rep_m. do
              c <- c_m ;
              rep <- rep_m ;
              case rep of
                  Or (l::ls) => return (Or (c::l::ls))
                | _ => return c
            od));

      (mkNT Top, pnt Alt)
     ]
  |>
’;

val FDOM_rePEG = save_thm("FDOM_rePEG",
  EVAL``FDOM rePEG.rules``);

val wfpeg_BslashSpecial_applied = Q.store_thm("wfpeg_BslashSpecial_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT BslashSpecial))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rpt(rw[Once wfpeg_cases]));

val wfpeg_BslashSpecial = Q.store_thm("wfpeg_BslashSpecial",
  `wfpeg rePEG (nt (mkNT BslashSpecial) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_BslashSpecial_applied]);

val wfpeg_CharSet_applied = Q.store_thm("wfpeg_CharSet_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT CharSet))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ ntac 2 (rw[Once wfpeg_cases]));

val wfpeg_CharSet = Q.store_thm("wfpeg_CharSet",
  `wfpeg rePEG (nt (mkNT CharSet) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_CharSet_applied]);

val wfpeg_Atom_applied = Q.store_thm("wfpeg_Atom_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT Atom))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rpt(rw[Once wfpeg_cases]));

val wfpeg_Atom = Q.store_thm("wfpeg_Atom",
  `wfpeg rePEG (nt (mkNT Atom) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_Atom_applied]);

val wfpeg_Star_applied = Q.store_thm("wfpeg_Star_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT Star))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rw[Once wfpeg_cases,wfpeg_Atom]
  \\ rpt(rw[Once wfpeg_cases]));

val wfpeg_Star = Q.store_thm("wfpeg_Star",
  `wfpeg rePEG (nt (mkNT Star) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_Star_applied])

val wfpeg_Concat_applied = Q.store_thm("wfpeg_Concat_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT Concat))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rw[Once wfpeg_cases]
  >- rw[wfpeg_Star]
  \\ fs[Once peg0_cases]
  \\ fs[EVAL``rePEG.rules ' (mkNT Star)``]
  \\ fs[Once peg0_cases]
  \\ fs[Once peg0_cases]
  \\ fs[EVAL``rePEG.rules ' (mkNT Atom)``]
  \\ rw[] \\ fs[]
  \\ fs[Once peg0_cases]);

val wfpeg_Concat = Q.store_thm("wfpeg_Concat",
  `wfpeg rePEG (nt (mkNT Concat) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_Concat_applied]);

val wfpeg_Alt_applied = Q.store_thm("wfpeg_Alt_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT Alt))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rw[Once wfpeg_cases,wfpeg_Concat]
  \\ ntac 3 (rw[Once wfpeg_cases]));

val wfpeg_Alt = Q.store_thm("wfpeg_Alt",
  `wfpeg rePEG (nt (mkNT Alt) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_Alt_applied]);

val wfpeg_Top_applied = Q.store_thm("wfpeg_Top_applied",
  `wfpeg rePEG (rePEG.rules ' (mkNT Top))`,
  CONV_TAC(RAND_CONV EVAL)
  \\ rw[wfpeg_Alt]);

val wfpeg_Top = Q.store_thm("wfpeg_Top",
  `wfpeg rePEG (nt (mkNT Top) I)`,
  rw[Once wfpeg_cases] >- EVAL_TAC
  \\ rw[wfpeg_Top_applied]);

val wfG_rePEG = Q.store_thm("wfG_rePEG",
  `wfG rePEG`,
  simp[wfG_def,Gexprs_def,finite_mapTheory.IN_FRANGE,PULL_EXISTS,FDOM_rePEG]
  \\ rw[] \\ pop_assum mp_tac
  \\ TRY (
    rename1`rePEG.rules ' (mkNT Atom)`
    \\ CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV EVAL)))
    \\ simp[subexprs_def]
    \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
    \\ rpt(rw[Once wfpeg_cases,wfpeg_Top,wfpeg_Alt,wfpeg_Concat,wfpeg_Star,wfpeg_Atom,wfpeg_BslashSpecial,wfpeg_CharSet]))
  \\ CONV_TAC(LAND_CONV EVAL) \\ rw[]
  \\ rpt(rw[Once wfpeg_cases,wfpeg_Top,wfpeg_Alt,wfpeg_Concat,wfpeg_Star,wfpeg_Atom]));

val add_loc_def = Define`
  add_loc c = (c, Locs (locn 0 0 0) (locn 0 0 0))`;

val parse_regexp_def = Define`
  parse_regexp s =
    case peg_exec rePEG rePEG.start (MAP add_loc s) [] done failed
    of Result (SOME ([],SOME r)) => SOME r | _ => NONE`;

(*
val _ = computeLib.add_persistent_funs ["pegexec.peg_nt_thm"]

val r = EVAL ``parse_regexp "\\d"``
val r = EVAL ``parse_regexp "\\("``
val r = EVAL ``parse_regexp ".\\d"``
val r = EVAL ``parse_regexp "(ab)"``
val r = EVAL ``parse_regexp "(ab"``
val r = EVAL ``parse_regexp "(ab)*ab*"``
val r = EVAL ``parse_regexp "a|b*c|d"``
val r = EVAL ``parse_regexp "a|[aoeu]"``
val r = EVAL ``parse_regexp "a|[aoe]u"``
*)

val _ = export_theory();
