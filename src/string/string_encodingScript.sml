open HolKernel Parse boolLib bossLib;

open stringTheory ASCIInumbersTheory

val _ = new_theory "string_encoding";

(* theory of encoding functions for encoding/decoding arbitrary string values
   as "literals" in various forms.
*)

Datatype: delimiter = DQ | SQ | PIPE
End

Definition del_to_char_def[simp]:
  del_to_char DQ = #"\"" /\
  del_to_char SQ = #"'" /\
  del_to_char PIPE = #"|"
End

Definition char_encode_def:
  char_encode delopt c =
  if ~ isPrint c then
    if c = #"\n" then "\\n"
    else if c = #"\t" then "\\t"
    else if ORD c < 10 then
      "\\00" ++ num_to_dec_string (ORD c)
    else if ORD c < 100 then
      "\\0" ++ num_to_dec_string (ORD c)
    else "\\" ++ num_to_dec_string (ORD c)
  else if c = #"\\" then "\\\\"
  else case delopt of
         NONE => [c]
       | SOME d => if c = del_to_char d then
                     "\\" ++ [c]
                   else [c]
End

Definition char_decode_def:
  char_decode delopt [] = NONE /\
  char_decode delopt (c::s) =
  if c = #"\\" then
    case s of
      [] => NONE
    | c2 :: stl =>
        if c2 = #"n" then SOME (#"\n", stl)
        else if c2 = #"t" then SOME (#"\t", stl)
        else if c2 = #"\\" then SOME (#"\\", stl)
        else if isDigit c2 then
          let d23 = TAKE 2 stl
          in
            if LENGTH d23 = 2 /\ EVERY isDigit d23 then
              let n = num_from_dec_string (c2::d23)
              in
                if n < 256 then SOME (CHR n, DROP 2 stl)
                else NONE
            else NONE
        else
          case delopt of
            NONE => NONE
          | SOME d => if del_to_char d = c2 then SOME (c2, stl)
                      else NONE
  else
    if isPrint c then
      case delopt of
        NONE => SOME (c, s)
      | SOME d => if del_to_char d = c then NONE
                  else SOME (c, s)
    else NONE
End

Theorem char_decode_encode:
  char_decode delopt (char_encode delopt c ++ s) =
  SOME (c, s)
Proof
  rw[char_decode_def, char_encode_def, stringTheory.isDigit_def] >>~-
  ([‘TAKE _ (toString (ORD c) ++ s)’],
   assume_tac (LENGTH_num_to_dec_string |> Q.INST [‘n’ |-> ‘ORD c’]) >>
   qmatch_goalsub_abbrev_tac ‘TAKE n (toString (ORD _) ++ _)’ >>
   ‘n = LENGTH (toString (ORD c))’
     by (simp[] >>
         rw[DECIDE “x:num = x + y <=> y = 0”, logrootTheory.LOG_EQ_0] >>
         simp[Abbr‘n’, DECIDE “n <= y ==> (x + n = y <=> x = y - n)”] >>
         irule logrootTheory.LOG_UNIQUE >> simp[]) >>
   pop_assum SUBST1_TAC >> qpat_x_assum ‘LENGTH (toString _) = _’ kall_tac >>
   simp[rich_listTheory.TAKE_LENGTH_APPEND, toNum_toString,
       EVERY_isDigit_num_to_dec_string]) >>~-
  ([‘DROP _ (toString (ORD c) ++ s)’],
   assume_tac (LENGTH_num_to_dec_string |> Q.INST [‘n’ |-> ‘ORD c’]) >>
   qmatch_goalsub_abbrev_tac ‘DROP n (toString (ORD _) ++ _)’ >>
   ‘n = LENGTH (toString (ORD c))’
     by (simp[] >>
         rw[DECIDE “x:num = x + y <=> y = 0”, logrootTheory.LOG_EQ_0] >>
         simp[Abbr‘n’, DECIDE “n <= y ==> (x + n = y <=> x = y - n)”] >>
         irule logrootTheory.LOG_UNIQUE >> simp[]) >>
   pop_assum SUBST1_TAC >> qpat_x_assum ‘LENGTH (toString _) = _’ kall_tac >>
   simp[rich_listTheory.DROP_LENGTH_APPEND]) >~
  [‘list_CASE (toString (ORD c) ++ s)’]
  >- (Cases_on ‘toString (ORD c)’ >> gs[num_to_dec_string_nil] >>
      qspec_then ‘ORD c’ mp_tac EVERY_isDigit_num_to_dec_string >>
      simp[] >> rw[] >> gs[isDigit_def] >>
      ‘LENGTH t = 2’
        by (assume_tac
              (LENGTH_num_to_dec_string |> Q.INST [‘n’ |-> ‘ORD c’]) >>
            gs[arithmeticTheory.ADD1] >>
            irule logrootTheory.LOG_UNIQUE >>
            qspec_then ‘c’ assume_tac ORD_BOUND >> simp[]) >>
      ‘TAKE 2 (t ++ s) = t /\ DROP 2 (t ++ s) = s’
        by metis_tac[rich_listTheory.TAKE_LENGTH_APPEND,
                     rich_listTheory.DROP_LENGTH_APPEND] >>
      gs[] >> metis_tac[CHR_ORD, toNum_toString, ORD_BOUND]) >>
  Cases_on ‘delopt’>> simp[char_decode_def] >> rw[] >>
  simp[char_decode_def] >>
  rename [‘del_to_char d’] >> Cases_on ‘d’ >> gs[] >>
  simp[isDigit_def]
QED

Theorem char_decode_reduces:
  char_decode delopt s = SOME (c,s') ==> LENGTH s' < LENGTH s
Proof
  Cases_on ‘s’ >> rw[char_decode_def] >> gvs[AllCaseEqs()]
QED

Definition strencode_def:
  strencode delopt s = FLAT (MAP (char_encode delopt) s)
End

Definition strdecode_def:
  strdecode delopt s =
    case char_decode delopt s of
      NONE => (case (s,delopt) of
                 ([], _) => SOME("", [])
               | (_, NONE) => NONE
               | (c::tl, SOME d) => if c = del_to_char d then SOME("", c::tl)
                                    else NONE)
    | SOME(c, rest) => OPTION_MAP (CONS c ## I) (strdecode delopt rest)
Termination
  WF_REL_TAC ‘measure (LENGTH o SND)’ >> metis_tac[char_decode_reduces]
End

Definition delopt_to_str_def[simp]:
  delopt_to_str NONE = "" /\
  delopt_to_str (SOME d) = [del_to_char d]
End

(* reverse not true because \n and \t can be encoded with numeric forms as well
*)
Theorem strdecode_strencode_tail_delimited:
  strdecode delopt (strencode delopt s ++ delopt_to_str delopt) =
  SOME (s, delopt_to_str delopt)
Proof
  simp[strencode_def] >> completeInduct_on ‘LENGTH s’ >> gs[PULL_FORALL] >>
  qx_gen_tac ‘s’ >> rw[] >>
  Cases_on ‘s’ >> simp[] >> rw[]
  >- (Cases_on ‘delopt’ >>
      simp[Once strdecode_def, char_decode_def] >>
      rename [‘char_decode (SOME d)’] >> Cases_on ‘d’ >>
      simp[char_decode_def]) >>
  simp[Once strdecode_def] >>
  REWRITE_TAC[char_decode_encode, GSYM listTheory.APPEND_ASSOC] >>
  simp[pairTheory.EXISTS_PROD]
QED

Theorem strdecode_strencode:
  strdecode delopt (strencode delopt s) = SOME (s, "")
Proof
  simp[strencode_def] >> completeInduct_on ‘LENGTH s’ >> gs[PULL_FORALL] >>
  qx_gen_tac ‘s’ >> rw[] >>
  Cases_on ‘s’ >> simp[] >> rw[]
  >- (simp[Once strdecode_def, char_decode_def]) >>
  simp[Once strdecode_def] >>
  REWRITE_TAC[char_decode_encode, GSYM listTheory.APPEND_ASSOC] >>
  simp[pairTheory.EXISTS_PROD]
QED

Theorem char_encode_isPrintable:
  EVERY isPrint (char_encode delopt c)
Proof
  rw[char_encode_def, isPrint_def] >>~-
  ([‘EVERY isPrint (toString _)’],
   irule listTheory.MONO_EVERY >> qexists ‘isDigit’ >>
   simp[EVERY_isDigit_num_to_dec_string] >>
   simp[isDigit_def, isPrint_def]) >>
   Cases_on ‘delopt’ >> rw[] >> gs[isPrint_def]
QED

Theorem strencode_isPrintable:
  EVERY isPrint (strencode delopt s)
Proof
  simp[strencode_def, listTheory.EVERY_FLAT, listTheory.EVERY_MAP,
       char_encode_isPrintable]
QED



val _ = export_theory();
