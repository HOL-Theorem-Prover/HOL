open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_parse";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory stringTheory relationTheory;

open lisp_sexpTheory;

(* file structure:
     1. we first define how to print s-expressions, then
     2. we define a function which parses printed s-expressions.
*)

val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val TOKEN_OPEN  = ``(Val 0, Val 1)``
val TOKEN_DOT   = ``(Val 1, Val 1)``
val TOKEN_CLOSE = ``(Val 2, Val 1)``
val TOKEN_QUOTE = ``(Val 3, Val 1)``
val TOKEN_SAVE  = ``(Val index, Val 2)``
val TOKEN_LOAD  = ``(Val index, Val 3)``
val NO_TOKEN  = ``(Sym "NIL", Sym "NIL")``

val SExp_print_induct = store_thm("SExp_print_induct",
  ``!P. (!x. (if isQuote x then P (CAR (CDR x)) else
              if isDot x then P (CAR x) /\ P (CDR x) else T) ==> P x) ==>
        !x. P x``,
  REPEAT STRIP_TAC \\ completeInduct_on `LSIZE x`
  \\ REPEAT STRIP_TAC
  \\ Cases_on `isQuote x`
  \\ Q.PAT_X_ASSUM `!x. bbb ==> P x` MATCH_MP_TAC THEN1
   (ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def]
    \\ FULL_SIMP_TAC std_ss [LSIZE_def,ADD1,GSYM ADD_ASSOC])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,CDR_def,LSIZE_def]
  \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,CDR_def,LSIZE_def]
  \\ METIS_TAC [DECIDE ``n < SUC (m + n)``,ADD_COMM]);


(* Part 1 - section 1: print s-expressions *)

val LIST_STRCAT_def = Define `
  (LIST_STRCAT [] = "") /\
  (LIST_STRCAT (x::xs) = STRCAT x (LIST_STRCAT xs))`;

val dec2str_def = Define `dec2str n = STRING (CHR (n + 48)) ""`;

val num2str_def = tDefine "num2str" `
  num2str n =
    if n DIV 10 = 0 then dec2str (n MOD 10) else
      STRCAT (num2str (n DIV 10)) (dec2str (n MOD 10))`
  (Q.EXISTS_TAC `measure I`
   \\ SIMP_TAC std_ss [prim_recTheory.WF_measure]
   \\ SIMP_TAC std_ss [prim_recTheory.measure_thm]
   \\ STRIP_TAC
   \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DA (DECIDE ``0 < 10:num``)))
   \\ ASM_SIMP_TAC std_ss [DIV_MULT]
   \\ DECIDE_TAC);

val number_char_def = Define `
  number_char c = 48 <= ORD c /\ ORD c < 58`;

val space_char_def = Define `
  space_char c = ORD c <= 32`;

val identifier_char_def = Define `
  identifier_char c = 42 <= ORD c /\ ~(ORD c = 46) /\ ~(ORD c = 59) /\ ~(ORD c = 124)`;

val identifier_string_def = Define `
  identifier_string s =
    ~(s = "") /\ EVERY identifier_char s /\ ~number_char (HD s)`;

val sym2str_aux_def = Define `
  (sym2str_aux [] = []) /\
  (sym2str_aux (x::xs) =
     if (ORD x = 0) then (#"\\")::(#"0")::sym2str_aux xs else
     if MEM x [#"|";#"\\"]
     then #"\\"::x::sym2str_aux xs else x::sym2str_aux xs)`;

val is_lower_case_def = Define `
  is_lower_case c = #"a" <= c /\ c <= #"z"`;

val upper_case_def = Define `
  upper_case c = if is_lower_case c then CHR (ORD c - 32) else c`;

val sym2str_def = Define `
  sym2str s =
    if identifier_string s /\ EVERY (\c. ~(is_lower_case c)) s
    then s else "|" ++ sym2str_aux s ++ "|"`;

val sexp2string_aux_def = tDefine "sexp2string_aux" `
  (sexp2string_aux (Val n, b) = num2str n) /\
  (sexp2string_aux (Sym s, b) = sym2str s) /\
  (sexp2string_aux (Dot x y, b) =
     if isQuote (Dot x y) then LIST_STRCAT ["'"; sexp2string_aux (CAR y,T)] else
       let (a,e) = if b then ("(",")") else ("","") in
         if y = Sym "NIL" then LIST_STRCAT [a; sexp2string_aux (x,T); e] else
         if isDot y /\ ~(isQuote y)
         then LIST_STRCAT [a; sexp2string_aux (x,T); " "; sexp2string_aux (y,F); e]
         else LIST_STRCAT [a; sexp2string_aux (x,T); " . "; sexp2string_aux (y,F); e])`
 (WF_REL_TAC `measure (LSIZE o FST)` \\ REWRITE_TAC [LSIZE_def,ADD1]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,LSIZE_def]
  \\ DECIDE_TAC);

val sexp2string_def = Define `sexp2string x = sexp2string_aux (x, T)`;


(* Part 1 - section 2: printing s-expressions with abbreviations *)

val isAtom_def = Define `
  isAtom abbrevs s = ~isDot s \/ isQuote s \/ s IN FDOM abbrevs`;

val sexp2abbrev_aux_def = tDefine "sexp2abbrev_aux" `
  sexp2abbrev_aux s b abbrevs ps =
    let index = abbrevs ' s in
    let prefix = (if s IN FDOM abbrevs then "#" ++ (num2str index) ++ "=" else "") in
      if s IN FDOM abbrevs /\ s IN ps then
        ("#" ++ (num2str index) ++ "#", ps)
      else
        if isVal s then (prefix ++ num2str (getVal s), if s IN FDOM abbrevs then s INSERT ps else ps) else
        if isSym s then (prefix ++ sym2str (getSym s), if s IN FDOM abbrevs then s INSERT ps else ps) else
        if isQuote s then
          let (str2,ps2) = sexp2abbrev_aux (CAR (CDR s)) T abbrevs ps in
            (prefix ++ "'" ++ str2,
             if s IN FDOM abbrevs then s INSERT ps2 else ps2)
        else
          let b = b \/ ~(prefix = "") in
          let (s1,s2) = (if b then ("(",")") else ("","")) in
          let (str1,ps1) = sexp2abbrev_aux (CAR s) T abbrevs ps in
          let (str2,ps2) = sexp2abbrev_aux (CDR s) F abbrevs ps1 in
            ((prefix ++ s1 ++ str1 ++
               (if CDR s = Sym "NIL" then "" else
                  (if isAtom abbrevs (CDR s) then " . " else " ") ++
                     str2) ++ s2),
             if CDR s = Sym "NIL"
             then if s IN FDOM abbrevs then s INSERT ps1 else ps1
             else if s IN FDOM abbrevs then s INSERT ps2 else ps2)`
 (WF_REL_TAC `measure (\(s,b,abbrevs,ps). LSIZE s)` \\ SRW_TAC [] []
  \\ `isDot s` by (Cases_on `s` \\ FULL_SIMP_TAC std_ss [isVal_def,isDot_def,isSym_def])
  \\ FULL_SIMP_TAC std_ss [isQuote_thm,isDot_thm,CDR_def,CAR_def,LSIZE_def]
  \\ FULL_SIMP_TAC std_ss [SExp_11,LSIZE_def,CAR_def,CDR_def]
  \\ DECIDE_TAC);

val sexp_abbrev_fmap_def = Define `
  (sexp_abbrev_fmap [] n = FEMPTY) /\
  (sexp_abbrev_fmap (x::xs) n = sexp_abbrev_fmap xs (n+1) |+ (x:SExp,n))`;

val sexp2abbrev_def = Define `
  sexp2abbrev s abbrevs = FST (sexp2abbrev_aux s T (sexp_abbrev_fmap abbrevs 0) {})`;

val sexp2abbrev_aux_EQ_sexp2string_aux = prove(
  ``!s b. sexp2abbrev_aux s b FEMPTY {} = (sexp2string_aux (s,b),{})``,
  HO_MATCH_MP_TAC SExp_print_induct \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [sexp2abbrev_aux_def]
  \\ SIMP_TAC std_ss [NOT_IN_EMPTY,FDOM_FEMPTY,LET_DEF]
  \\ Cases_on `isVal s` \\ ASM_SIMP_TAC std_ss [APPEND]
  THEN1 (FULL_SIMP_TAC std_ss [isVal_thm,getVal_def,sexp2string_aux_def])
  \\ Cases_on `isSym s` \\ ASM_SIMP_TAC std_ss [APPEND]
  THEN1 (FULL_SIMP_TAC std_ss [isSym_thm,getSym_def,sexp2string_aux_def])
  \\ Cases_on `isQuote s` \\ ASM_SIMP_TAC std_ss [APPEND] THEN1
   (FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [isQuote_thm]
    \\ SIMP_TAC std_ss [sexp2string_aux_def,isQuote_def,CAR_def,CDR_def,
         isDot_def,LIST_STRCAT_def,APPEND_NIL,APPEND])
  \\ `isDot s` by (Cases_on `s` \\ FULL_SIMP_TAC std_ss [isDot_def,isVal_def,isSym_def])
  \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [isDot_thm]
  \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,CAR_def,CDR_def,LIST_STRCAT_def]
  \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [LET_DEF,isAtom_def,FDOM_FEMPTY,NOT_IN_EMPTY]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss []);

val sexp2abbrev_NIL = prove(
  ``!s. sexp2abbrev s [] = sexp2string s``,
  SIMP_TAC std_ss [sexp2abbrev_def,sexp2string_def,sexp_abbrev_fmap_def,
    sexp2abbrev_aux_EQ_sexp2string_aux]);

(*

val list2sexp_def = Define `
  (list2sexp [] = Sym "NIL") /\
  (list2sexp (x::xs) = Dot x (list2sexp xs))`;

val A1 = Define `A1 = list2sexp [Sym "a"; Val 4]`;
val A2 = Define `A2 = list2sexp [Sym "b"; Sym "c"]`;

EVAL  ``sexp2abbrev (list2sexp [A1;Dot A1 A2;list2sexp [Sym "QUOTE"; A2]]) [A1;A2]``

*)

val sexp2abbrevt_aux_def = tDefine "sexp2abbrevt_aux" `
  sexp2abbrevt_aux s b abbrevs ps =
    let index = abbrevs ' s in
    let prefix = (if s IN FDOM abbrevs then [^TOKEN_SAVE] else []) in
      if s IN FDOM abbrevs /\ s IN ps then
        ([(^TOKEN_LOAD)], ps)
      else
        if ~(isDot s) then (prefix ++ [(s,Val 0)], if s IN FDOM abbrevs then s INSERT ps else ps) else
        if isQuote s then
          let (str2,ps2) = sexp2abbrevt_aux (CAR (CDR s)) T abbrevs ps in
            (prefix ++ [^TOKEN_QUOTE] ++ str2,
             if s IN FDOM abbrevs then s INSERT ps2 else ps2)
        else
          let b = b \/ ~(prefix = []) in
          let (s1,s2) = (if b then ([^TOKEN_OPEN],[^TOKEN_CLOSE]) else ([],[])) in
          let (str1,ps1) = sexp2abbrevt_aux (CAR s) T abbrevs ps in
          let (str2,ps2) = sexp2abbrevt_aux (CDR s) F abbrevs ps1 in
            ((prefix ++ s1 ++ str1 ++
               (if CDR s = Sym "NIL" then [] else
                  (if isAtom abbrevs (CDR s) then [^TOKEN_DOT] else []) ++
                     str2) ++ s2),
             if CDR s = Sym "NIL"
             then if s IN FDOM abbrevs then s INSERT ps1 else ps1
             else if s IN FDOM abbrevs then s INSERT ps2 else ps2)`
 (WF_REL_TAC `measure (\(s,b,abbrevs,ps). LSIZE s)` \\ SRW_TAC [] []
  \\ `isDot s` by (Cases_on `s` \\ FULL_SIMP_TAC std_ss [isVal_def,isDot_def,isSym_def])
  \\ FULL_SIMP_TAC std_ss [isQuote_thm,isDot_thm,CDR_def,CAR_def,LSIZE_def]
  \\ FULL_SIMP_TAC std_ss [SExp_11,LSIZE_def,CAR_def,CDR_def]
  \\ DECIDE_TAC)



(* Part 2 - section 1: reading tokens from a string, i.e. lexing or scanning *)

val read_while_def = Define `
  (read_while P "" s = (s,"")) /\
  (read_while P (STRING c cs) s =
     if P c then read_while P cs (STRCAT s (STRING c ""))
            else (s,STRING c cs))`;

val read_while_thm = prove(
  ``!cs s cs' s'.
       (read_while P cs s = (s',cs')) ==> LENGTH cs' <= LENGTH cs + LENGTH s``,
  Induct \\ SIMP_TAC std_ss [read_while_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ REPEAT (Q.PAT_X_ASSUM `STRING c cs = cs'` (ASSUME_TAC o GSYM))
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC);

val str2num_def = Define `
  (str2num "" = 0) /\
  (str2num (STRING c s) = (ORD c - 48) * 10 ** (LENGTH s) + str2num s)`;

val str2num_dec2str = prove(
  ``!n. n < 10 ==> (str2num (dec2str n) = n) /\ ~(dec2str n = "") /\
                   EVERY number_char (dec2str n)``,
  SRW_TAC [] [dec2str_def,str2num_def,LENGTH,ORD_CHR,number_char_def]
  \\ `n + 48 < 256` by DECIDE_TAC
  \\ IMP_RES_TAC ORD_CHR
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val str2num_STRCAT = prove(
  ``!s c. str2num (STRCAT s (STRING c "")) = str2num s * 10 + str2num (STRING c "")``,
  Induct \\ ASM_SIMP_TAC std_ss [str2num_def,STRCAT_def,LENGTH_APPEND,
    LENGTH,EXP_ADD,RIGHT_ADD_DISTRIB,AC MULT_ASSOC MULT_COMM, AC ADD_ASSOC ADD_COMM]);

val dec2str_lemma = prove(
  ``?c. dec2str r = STRING c ""``,
  SRW_TAC [] [dec2str_def,str2num_def,LENGTH]);

val str2num_num2str = store_thm("str2num_num2str",
  ``!n. (str2num (num2str n) = n) /\ ~((num2str n) = "") /\
        EVERY number_char (num2str n)``,
  completeInduct_on `n` \\ Cases_on `n < 10` THEN1
   (IMP_RES_TAC LESS_DIV_EQ_ZERO \\ ONCE_REWRITE_TAC [num2str_def]
    \\ ASM_SIMP_TAC std_ss [str2num_dec2str])
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DA (DECIDE ``0 < 10:num``)))
  \\ ONCE_REWRITE_TAC [num2str_def]
  \\ ASM_SIMP_TAC std_ss [DIV_MULT]
  \\ Cases_on `q = 0` THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [MOD_TIMES,STRCAT_EQ_EMPTY,EVERY_APPEND]
  \\ ASM_SIMP_TAC std_ss [str2num_dec2str,str2num_STRCAT]
  \\ `q < n` by DECIDE_TAC \\ RES_TAC
  \\ STRIP_ASSUME_TAC dec2str_lemma
  \\ ASM_SIMP_TAC std_ss [str2num_STRCAT]
  \\ METIS_TAC [str2num_dec2str]);

val str2sym_aux_def = Define `
  (str2sym_aux [] b = ("",[])) /\
  (str2sym_aux (c::cs) T =
     let (x1,x2) = str2sym_aux cs F in ((if c = #"0" then CHR 0 else c)::x1,x2)) /\
  (str2sym_aux (c::cs) F =
     if c = #"\\" then str2sym_aux cs T else
     if c = #"|" then ("",cs) else
       let (x1,x2) = str2sym_aux cs F in (c::x1,x2))`;

val str2sym_def = Define `
  (str2sym "" = ("","")) /\
  (str2sym (c::cs) =
    if c = #"|" then
       (let (ident,cs) = str2sym_aux cs F
        in
          ((ident,cs)))
     else
       (let (ident,cs1) = read_while identifier_char cs "" in
        let ident = MAP upper_case (c :: ident)
        in
          ((ident,cs1))))`;

val str2sym_aux_sym2str_aux = prove(
  ``!s. str2sym_aux (sym2str_aux s ++ "|" ++ ts) F = (s,ts)``,
  Induct \\ SRW_TAC [] [str2sym_aux_def,sym2str_aux_def,MEM]
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [ORD_CHR]);

val next_token_def = tDefine "next_token" `
  (next_token "" = (^NO_TOKEN,"")) /\
  (next_token (c::cs) =
     if space_char c then next_token cs else
     if c = #"(" then (^TOKEN_OPEN,cs) else
     if c = #"." then (^TOKEN_DOT,cs) else
     if c = #")" then (^TOKEN_CLOSE,cs) else
     if c = #"'" then (^TOKEN_QUOTE,cs) else
     if c = #"#" then
       (let (index_str,cs) = read_while number_char cs "" in
        let index = str2num index_str in
          if cs = "" then (^NO_TOKEN,"") else
          if HD cs = #"#" then (^TOKEN_LOAD,TL cs) else
          if HD cs = #"=" then (^TOKEN_SAVE,TL cs) else (^NO_TOKEN,TL cs)) else
     if number_char c then
       (let (index_str,cs) = read_while number_char cs "" in
        let index = str2num (c::index_str) in
          ((Val index, Val 0),cs)) else
     if c = #";" then
       (let cs = SND (read_while (\x. ~(x = #"\n")) cs "") in
          next_token cs)
     else let (ident,cs) = str2sym (c::cs) in
            ((Sym ident, Val 0),cs))`
 (WF_REL_TAC `measure LENGTH` \\ SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `read_while (\x. x <> #"\n") cs ""` \\ IMP_RES_TAC read_while_thm
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC);

val is_eof_def = tDefine "is_eof" `
  (is_eof "" = (T,"")) /\
  (is_eof (c::cs) =
     if space_char c then is_eof cs else
     if c = #";" then
       (let cs = SND (read_while (\x. ~(x = #"\n")) cs "") in
          is_eof cs)
     else (F,c::cs))`
 (WF_REL_TAC `measure LENGTH` \\ SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `read_while (\x. x <> #"\n") cs ""` \\ IMP_RES_TAC read_while_thm
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC);

val str2sym_aux_LENGTH = prove(
  ``!s b t x. (str2sym_aux s b = (x,t)) ==> LENGTH t <= LENGTH s``,
  Induct \\ SRW_TAC [] [str2sym_aux_def] \\ SRW_TAC [] []
  \\ Cases_on `b`\\ FULL_SIMP_TAC std_ss [str2sym_aux_def]
  \\ POP_ASSUM MP_TAC
  \\ `?a1 a2. str2sym_aux s F = (a1,a2)` by METIS_TAC [PAIR]
  \\ `?b1 b2. str2sym_aux s T = (b1,b2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `bbb = t` (ASSUME_TAC o GSYM))
  THEN1 (RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val str2sym_LENGTH = prove(
  ``!s t x. ~(s = []) /\ (str2sym s = (x,t)) ==> LENGTH t < LENGTH s``,
  SIMP_TAC std_ss [str2sym_def,LET_DEF] \\ NTAC 3 STRIP_TAC \\ Cases_on `s`
  \\ SIMP_TAC std_ss [str2sym_def,LET_DEF]
  \\ `?a1 a2. str2sym_aux t' F = (a1,a2)` by METIS_TAC [PAIR]
  \\ `?y1 y2. read_while identifier_char t' "" = (y1,y2)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC read_while_thm
  \\ ASM_SIMP_TAC std_ss [] \\ IMP_RES_TAC str2sym_aux_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH,HD,LENGTH_NIL,NOT_CONS_NIL,TL]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [TL] \\ DECIDE_TAC);

val next_token_LENGTH = prove(
  ``!s x t. (next_token s = (x,t)) ==> LENGTH t < LENGTH s \/ (s = "")``,
  HO_MATCH_MP_TAC (fetch "-" "next_token_ind") \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [next_token_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `space_char c` \\ ASM_SIMP_TAC std_ss [] THEN1
   (REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss [LENGTH]
    THEN1 (DISJ1_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [next_token_def]
    \\ Q.PAT_X_ASSUM `"" = t` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
    \\ EVAL_TAC)
  \\ `?x1 x2. read_while number_char s "" = (x1,x2)` by METIS_TAC [PAIR]
  \\ `?y1 y2. read_while (\x. x <> #"\n") s "" = (y1,y2)` by METIS_TAC [PAIR]
  \\ `?z1 z2. str2sym (c::s) = (z1,z2)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC str2sym_LENGTH
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ IMP_RES_TAC read_while_thm
  \\ SRW_TAC [] [LENGTH] \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ REPEAT (Cases_on `x2`)
  \\ FULL_SIMP_TAC std_ss [LENGTH,TL,NOT_CONS_NIL,HD,ADD1]
  \\ REPEAT DECIDE_TAC
  \\ RES_TAC \\ REPEAT DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``next_token ""``]
  \\ REPEAT (Q.PAT_X_ASSUM `"" = t` (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ REPEAT DECIDE_TAC);

val sexp_lex_def = tDefine "sexp_lex" `
  sexp_lex s =
    if SND (FST (next_token s)) = Sym "NIL" then ([],"") else
      let (ts,s2) = sexp_lex (SND (next_token s)) in
        (FST (next_token s)::ts,s2)`
 (WF_REL_TAC `measure (LENGTH)` \\ REPEAT STRIP_TAC
  \\ Cases_on `next_token s` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC next_token_LENGTH \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [next_token_def] \\ METIS_TAC []);

val sexp_lex_thm = prove(
  ``sexp_lex s =
      let (t,s) = next_token s in
        if SND t = Sym "NIL" then ([],[]) else
          let (ts,s) = sexp_lex s in
            (t::ts,s)``,
  SIMP_TAC std_ss [Once sexp_lex_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `next_token s` \\ ASM_SIMP_TAC std_ss []);

val sexp2abbrev_aux_SND = prove(
  ``!exp b abbrevs ps xs1 xs2 ps1 ps2.
      ((xs1,ps1) = sexp2abbrev_aux exp b abbrevs ps) ==>
      ((xs2,ps2) = sexp2abbrevt_aux exp b abbrevs ps) ==>
        (ps1 = ps2)``,
  HO_MATCH_MP_TAC SExp_print_induct \\ NTAC 9 STRIP_TAC
  \\ ONCE_REWRITE_TAC [sexp2abbrevt_aux_def,sexp2abbrev_aux_def]
  \\ Q.ABBREV_TAC `index = abbrevs ' exp`
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `t_prefix = if exp IN FDOM abbrevs then [(Val index,Val 2)] else []`
  \\ Q.ABBREV_TAC `s_prefix = if exp IN FDOM abbrevs then STRCAT (STRCAT "#" (num2str index)) "=" else ""`
  \\ `?t_str1 t_ps1. sexp2abbrevt_aux (CAR exp) T abbrevs ps = (t_str1,t_ps1)` by METIS_TAC [PAIR]
  \\ `?t_str2 t_ps2. sexp2abbrevt_aux (CDR exp) F abbrevs t_ps1 = (t_str2,t_ps2)` by METIS_TAC [PAIR]
  \\ `?t_str3 t_ps3. sexp2abbrevt_aux (CAR (CDR exp)) T abbrevs ps = (t_str3,t_ps3)` by METIS_TAC [PAIR]
  \\ `?s_str1 s_ps1. sexp2abbrev_aux (CAR exp) T abbrevs ps = (s_str1,s_ps1)` by METIS_TAC [PAIR]
  \\ `?s_str2 s_ps2. sexp2abbrev_aux (CDR exp) F abbrevs s_ps1 = (s_str2,s_ps2)` by METIS_TAC [PAIR]
  \\ `?s_str3 s_ps3. sexp2abbrev_aux (CAR (CDR exp)) T abbrevs ps = (s_str3,s_ps3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `Abbrev (exp IN FDOM abbrevs /\ exp IN ps)`
  THEN1 (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [markerTheory.Abbrev_def])
  \\ IMP_RES_TAC (METIS_PROVE [] ``~Abbrev b ==> ~b``)
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `isVal exp`
  THEN1 (FULL_SIMP_TAC std_ss [isVal_thm,isDot_def,isVal_def,SExp_11])
  \\ Cases_on `isSym exp`
  THEN1 (FULL_SIMP_TAC std_ss [isSym_thm,isDot_def,isSym_def,SExp_11])
  \\ `isDot exp` by (Cases_on `exp` \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,isDot_def])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isQuote exp` THEN1 (FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss []
  \\ `(t_prefix = []) = (s_prefix = [])` by
        (FULL_SIMP_TAC std_ss [APPEND] \\ METIS_TAC [NOT_CONS_NIL])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `b \/ s_prefix <> ""` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val read_while_eval = (GEN_ALL o RW [APPEND_NIL,APPEND] o Q.SPECL [`xs`,`[]`] o prove)(
  ``!xs zs. EVERY P xs /\ ~P y ==> (read_while P (xs ++ y::ys) zs = (zs ++ xs,y::ys))``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,APPEND,read_while_def,APPEND_NIL]
  \\ SIMP_TAC std_ss [APPEND_NIL,GSYM APPEND_ASSOC,APPEND]);

val read_while_entire = (GEN_ALL o RW [APPEND_NIL,APPEND] o Q.SPECL [`xs`,`[]`] o prove)(
  ``!xs zs. EVERY P xs ==> (read_while P xs zs = (zs ++ xs,""))``,
  Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,APPEND,read_while_def,APPEND_NIL]
  \\ SIMP_TAC std_ss [APPEND_NIL,GSYM APPEND_ASSOC,APPEND]);

val read_while_lemma = prove(
  ``(read_while number_char (num2str index ++ #"#"::xs) "" = (num2str index,#"#"::xs)) /\
    (read_while number_char (num2str index ++ #"="::xs) "" = (num2str index,#"="::xs))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC read_while_eval
  \\ ASM_SIMP_TAC std_ss [str2num_num2str] \\ EVAL_TAC);

val next_token_lemma = prove(
  ``(s <> "" ==> MEM (HD s) " )") ==>
     (next_token (STRCAT (num2str a) s) = ((Val a,Val 0), s)) /\
     (next_token (STRCAT (sym2str t) s) = ((Sym t,Val 0), s))``,
  REPEAT STRIP_TAC THEN1
   (Cases_on `num2str a` THEN1 METIS_TAC [str2num_num2str]
    \\ ASM_SIMP_TAC std_ss [APPEND,next_token_def]
    \\ `EVERY number_char (STRING h t)` by METIS_TAC [str2num_num2str]
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ `~space_char h` by
      (FULL_SIMP_TAC std_ss [number_char_def,space_char_def] \\ DECIDE_TAC)
    \\ `~MEM h "(.)'#"` by
     (FULL_SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [number_char_def])
    \\ FULL_SIMP_TAC std_ss [MEM]
    \\ `read_while number_char (STRCAT t s) "" = (t,s)` by
     (Cases_on `s` \\ FULL_SIMP_TAC std_ss [APPEND_NIL,read_while_entire]
      \\ MATCH_MP_TAC read_while_eval \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL]
      \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ METIS_TAC [str2num_num2str])
  \\ SIMP_TAC std_ss [sym2str_def]
  \\ Cases_on `identifier_string t /\ EVERY (\c. ~is_lower_case c) t`
  \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [identifier_string_def]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [APPEND,EVERY_DEF]
    \\ FULL_SIMP_TAC std_ss [next_token_def,HD]
    \\ FULL_SIMP_TAC std_ss [identifier_char_def,MEM,str2sym_def,HD,NOT_CONS_NIL,TL]
    \\ `read_while identifier_char (STRCAT t' s) "" = (t',s)` by
     (Cases_on `s` \\ FULL_SIMP_TAC std_ss [APPEND_NIL,read_while_entire]
      \\ MATCH_MP_TAC read_while_eval \\ FULL_SIMP_TAC std_ss [HD,NOT_CONS_NIL]
      \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ `~(space_char h)` by (FULL_SIMP_TAC std_ss [space_char_def] \\ DECIDE_TAC)
    \\ Cases_on `h = #"("` THEN1 (CCONTR_TAC \\ Q.PAT_X_ASSUM `42 <= bbb` MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `h = #")"` THEN1 (CCONTR_TAC \\ Q.PAT_X_ASSUM `42 <= bbb` MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `h = #"'"` THEN1 (CCONTR_TAC \\ Q.PAT_X_ASSUM `42 <= bbb` MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `h = #"#"` THEN1 (CCONTR_TAC \\ Q.PAT_X_ASSUM `42 <= bbb` MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `h = #"."` THEN1 (FULL_SIMP_TAC std_ss [EVAL ``ORD #"."``])
    \\ Cases_on `h = #"|"` THEN1 (FULL_SIMP_TAC std_ss [EVAL ``ORD #"|"``])
    \\ Cases_on `h = #";"` THEN1 (FULL_SIMP_TAC std_ss [EVAL ``ORD #";"``])
    \\ ASM_SIMP_TAC std_ss []
    \\ AP_TERM_TAC
    \\ `EVERY (\c. ~is_lower_case c) (h::t')` by ASM_SIMP_TAC std_ss [EVERY_DEF]
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`h::t'`,`xs`)
    \\ Induct \\ ASM_SIMP_TAC std_ss [MAP,EVERY_DEF,upper_case_def])
  \\ SIMP_TAC (srw_ss()) [APPEND,next_token_def,EVAL ``space_char #"|"``,
       EVAL ``number_char #"|"``,str2sym_def,LET_DEF]
  \\ SIMP_TAC std_ss [str2sym_aux_sym2str_aux,LET_DEF]);

val sexp_lex_SPACE = prove(
  ``!xs. sexp_lex (#" "::xs) = sexp_lex xs``,
  ONCE_REWRITE_TAC [sexp_lex_thm]
  \\ SIMP_TAC std_ss [next_token_def,EVAL ``space_char #" "``]);

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM pairTheory.PAIR)
  fun get_conv vs = let
    val (x,y) = dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end
    handle e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

val sexp2abbrev_aux_FST = prove(
  ``!exp s b abbrevs ps xs1 xs2 ps1 ps2.
      (~(s = []) ==> MEM (HD s) " )") ==>
      ((xs1,ps1) = sexp2abbrev_aux exp b abbrevs ps) ==>
      ((xs2,ps2) = sexp2abbrevt_aux exp b abbrevs ps) ==>
        (FST (sexp_lex (xs1 ++ s)) = xs2 ++ FST (sexp_lex s))``,
  HO_MATCH_MP_TAC SExp_print_induct \\ NTAC 10 STRIP_TAC
  \\ ONCE_REWRITE_TAC [sexp2abbrevt_aux_def,sexp2abbrev_aux_def]
  \\ Q.ABBREV_TAC `index = abbrevs ' exp`
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `t_prefix = if exp IN FDOM abbrevs then [(Val index,Val 2)] else []`
  \\ Q.ABBREV_TAC `s_prefix = if exp IN FDOM abbrevs then STRCAT (STRCAT "#" (num2str index)) "=" else ""`
  \\ `?t_str1 t_ps1. sexp2abbrevt_aux (CAR exp) T abbrevs ps = (t_str1,t_ps1)` by METIS_TAC [PAIR]
  \\ `?t_str2 t_ps2. sexp2abbrevt_aux (CDR exp) F abbrevs t_ps1 = (t_str2,t_ps2)` by METIS_TAC [PAIR]
  \\ `?t_str3 t_ps3. sexp2abbrevt_aux (CAR (CDR exp)) T abbrevs ps = (t_str3,t_ps3)` by METIS_TAC [PAIR]
  \\ `?s_str1 s_ps1. sexp2abbrev_aux (CAR exp) T abbrevs ps = (s_str1,s_ps1)` by METIS_TAC [PAIR]
  \\ `?s_str2 s_ps2. sexp2abbrev_aux (CDR exp) F abbrevs s_ps1 = (s_str2,s_ps2)` by METIS_TAC [PAIR]
  \\ `?s_str3 s_ps3. sexp2abbrev_aux (CAR (CDR exp)) T abbrevs ps = (s_str3,s_ps3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `Abbrev (exp IN FDOM abbrevs /\ exp IN ps)`
  THEN1 (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [markerTheory.Abbrev_def]
         \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once sexp_lex_thm]
         \\ SIMP_TAC (srw_ss()) [APPEND,next_token_def,EVAL ``space_char #"#"``]
         \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,read_while_lemma]
         \\ SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL,TL,HD,SExp_distinct]
         \\ Cases_on `sexp_lex s` \\ ASM_SIMP_TAC std_ss [str2num_num2str])
  \\ IMP_RES_TAC (METIS_PROVE [] ``~Abbrev b ==> ~b``)
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ `(t_prefix = []) = (s_prefix = [])` by
        (FULL_SIMP_TAC std_ss [APPEND] \\ METIS_TAC [NOT_CONS_NIL])
  \\ ASM_SIMP_TAC std_ss []
  \\ `!ss ts.
        (FST (sexp_lex (STRCAT s_prefix (STRCAT ss s))) =
         t_prefix ++ (ts ++ FST (sexp_lex s))) =
        (FST (sexp_lex (STRCAT ss s)) = ts ++ FST (sexp_lex s))` by
   (Q.UNABBREV_TAC `t_prefix` \\ Q.UNABBREV_TAC `s_prefix`
    \\ REVERSE (Cases_on `exp IN FDOM abbrevs`) \\ ASM_SIMP_TAC std_ss []
    THEN1 (ASM_SIMP_TAC std_ss [APPEND])
    \\ SIMP_TAC std_ss [Once sexp_lex_thm] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ SIMP_TAC (srw_ss()) [APPEND,next_token_def,EVAL ``space_char #"#"``]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ SIMP_TAC std_ss [APPEND,read_while_lemma,LET_DEF,NOT_CONS_NIL,TL,HD]
    \\ SIMP_TAC std_ss [str2num_num2str,EVAL ``#"=" = #"#"``,SExp_distinct]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `sexp_lex (STRCAT ss s)` \\ ASM_SIMP_TAC std_ss [CONS_11])
  \\ Cases_on `isVal exp`
  THEN1 (FULL_SIMP_TAC std_ss [isVal_thm,isDot_def,isVal_def,SExp_11]
         \\ ASM_SIMP_TAC std_ss [getVal_def,GSYM APPEND_ASSOC]
         \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once sexp_lex_thm] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
         \\ ASM_SIMP_TAC (srw_ss()) [APPEND,next_token_lemma]
         \\ ASM_SIMP_TAC std_ss [LET_DEF,SExp_distinct]
         \\ Cases_on `sexp_lex s` \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `isSym exp`
  THEN1 (FULL_SIMP_TAC std_ss [isSym_thm,isDot_def,isSym_def,SExp_11]
         \\ ASM_SIMP_TAC std_ss [getSym_def,GSYM APPEND_ASSOC]
         \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once sexp_lex_thm] \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
         \\ ASM_SIMP_TAC (srw_ss()) [APPEND,next_token_lemma]
         \\ ASM_SIMP_TAC std_ss [LET_DEF,SExp_distinct]
         \\ Cases_on `sexp_lex s` \\ ASM_SIMP_TAC std_ss [])
  \\ `isDot exp` by (Cases_on `exp` \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,isDot_def])
  \\ ASM_SIMP_TAC std_ss []
  \\ `s_ps1 = t_ps1` by METIS_TAC [sexp2abbrev_aux_SND]
  \\ Cases_on `isQuote exp`
  THEN1 (FULL_SIMP_TAC std_ss []
         \\ Q.PAT_X_ASSUM `!ss ts. bbb` (ASSUME_TAC o Q.SPECL [`"'" ++ s_str3`,`[(Val 3,Val 1)] ++ t_str3`])
         \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ REPEAT STRIP_TAC
         \\ SIMP_TAC std_ss [Once sexp_lex_thm]
         \\ SIMP_TAC (srw_ss()) [APPEND,next_token_def,EVAL ``space_char #"'"``,LET_DEF,SExp_distinct]
         \\ CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
         \\ SIMP_TAC std_ss [FST,CONS_11] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `s1 = if b \/ s_prefix <> "" then ("(") else ("")`
  \\ Q.ABBREV_TAC `s2 = if b \/ s_prefix <> "" then (")") else ("")`
  \\ Q.ABBREV_TAC `t1 = if b \/ s_prefix <> "" then ([(Val 0,Val 1)]) else ([])`
  \\ Q.ABBREV_TAC `t2 = if b \/ s_prefix <> "" then ([(Val 2,Val 1)]) else ([])`
  \\ `(if b \/ s_prefix <> "" then
      ([(Val 0,Val 1)],[(Val 2,Val 1)])
    else
      ([],[])) = (t1,t2)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ `(if b \/ s_prefix <> "" then
      ("(",")")
    else
      ([],[])) = (s1,s2)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `t3 = if CDR exp = Sym "NIL" then []
      else (if isAtom abbrevs (CDR exp) then [(Val 1,Val 1)] else []) ++ t_str2`
  \\ Q.ABBREV_TAC `s3 = if CDR exp = Sym "NIL" then ""
      else STRCAT (if isAtom abbrevs (CDR exp) then " . " else " ") s_str2`
  \\ Q.PAT_X_ASSUM `!ss ts. bbb` (ASSUME_TAC o Q.SPECL [`s1 ++ s_str1 ++ s3 ++ s2`,`t1 ++ t_str1 ++ t3 ++ t2`])
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ POP_ASSUM (K ALL_TAC)
  \\ `FST (sexp_lex (STRCAT (STRCAT (STRCAT (s_str1) s3) s2) s)) =
      t_str1 ++ t3 ++ t2 ++ FST (sexp_lex s)` suffices_by (STRIP_TAC THEN Cases_on `s1 = []`
    THEN1 (`t1 = []` by METIS_TAC [NOT_CONS_NIL] \\ ASM_SIMP_TAC std_ss [APPEND])
    \\ `s1 = "("` by METIS_TAC [NOT_CONS_NIL]
    \\ `t1 = [^TOKEN_OPEN]` by METIS_TAC [NOT_CONS_NIL]
    \\ ASM_SIMP_TAC std_ss [APPEND]
    \\ SIMP_TAC std_ss [Once sexp_lex_thm]
    \\ SIMP_TAC std_ss [next_token_def,EVAL ``space_char #"("``,LET_DEF,SExp_distinct]
    \\ CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    \\ ASM_SIMP_TAC std_ss [FST,CONS_11])
  \\ `~(s3++s2++s = []) ==> MEM (HD (s3++s2++s)) " )"` by
   (Q.UNABBREV_TAC `s3` \\ Q.UNABBREV_TAC `s2`
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [MEM])
  \\ `FST (sexp_lex (STRCAT s_str1 (s3++s2++s))) =
      t_str1 ++ FST (sexp_lex (s3++s2++s))` by
   (Q.PAT_X_ASSUM `!s b abbrevs ps xs1 xs2 ps1 ps2. bbb` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `!s b abbrevs ps xs1 xs2 ps1 ps2. bbb` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
  \\ (sg `FST (sexp_lex (STRCAT (s2) s)) =
      t2 ++ FST (sexp_lex s)`) THEN1
   (Cases_on `s2 = []`
    THEN1 (`t2 = []` by METIS_TAC [NOT_CONS_NIL] \\ ASM_SIMP_TAC std_ss [APPEND])
    \\ `s2 = ")"` by METIS_TAC [NOT_CONS_NIL]
    \\ `t2 = [^TOKEN_CLOSE]` by METIS_TAC [NOT_CONS_NIL]
    \\ ASM_SIMP_TAC std_ss [APPEND]
    \\ SIMP_TAC std_ss [Once sexp_lex_thm]
    \\ SIMP_TAC (srw_ss()) [next_token_def,EVAL ``space_char #")"``,LET_DEF,SExp_distinct]
    \\ CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    \\ SIMP_TAC std_ss [FST])
  \\ Q.UNABBREV_TAC `s3` \\ Q.UNABBREV_TAC `t3`
  \\ Cases_on `CDR exp = Sym "NIL"` \\ ASM_SIMP_TAC std_ss [APPEND]
  \\ `FST (sexp_lex (STRCAT (STRCAT s_str2 s2) s)) =
      t_str2 ++ t2 ++ FST (sexp_lex s)` suffices_by (STRIP_TAC THEN REVERSE (Cases_on `isAtom abbrevs (CDR exp)`)
    \\ ASM_SIMP_TAC std_ss [APPEND,sexp_lex_SPACE]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ SIMP_TAC std_ss [Once sexp_lex_thm]
    \\ SIMP_TAC (srw_ss()) [next_token_def,EVAL ``space_char #"."``,LET_DEF,sexp_lex_SPACE]
    \\ CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    \\ FULL_SIMP_TAC std_ss [FST,APPEND_ASSOC])
  \\ `~(s2++s = []) ==> MEM (HD (s2++s)) " )"` by
   (Q.UNABBREV_TAC `s2` \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [MEM])
  \\ `FST (sexp_lex (STRCAT s_str2 (s2++s))) =
      t_str2 ++ FST (sexp_lex (s2++s))` by
   (Q.PAT_X_ASSUM `!s b abbrevs ps xs1 xs2 ps1 ps2. bbb` (MATCH_MP_TAC o RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]);

val sexp_lex_sexp2abbrev_aux = prove(
  ``!exp b abbrevs ps.
      FST (sexp_lex (FST (sexp2abbrev_aux exp b abbrevs ps))) =
      FST (sexp2abbrevt_aux exp b abbrevs ps)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (Q.SPECL [`exp`,`[]`] sexp2abbrev_aux_FST)
  \\ ASM_SIMP_TAC std_ss [APPEND_NIL,EVAL ``sexp_lex ""``]
  \\ METIS_TAC [PAIR]);


(* Part 2 - section 2: algorithm for parsing a list of tokens *)

val _ = Hol_datatype `
  lisp_parse_mode =
     L_READ
   | L_RETURN of SExp
   | L_COLLECT of SExp`;

val _ = Hol_datatype `
  lisp_parse_action =
     L_CONS of SExp
   | L_STOP
   | L_DOT
   | L_QUOTE
   | L_STORE of num`;

val (R_parse_rules,R_parse_ind,R_parse_cases) = Hol_reln `
  (* from mode: L_READ *)
  (!ts s mem x.
     R_parse ((x, Val 0)::ts,s,L_READ,mem)
             (ts,s,L_RETURN x,mem))
  /\
  (!ts s mem.
     R_parse ((^TOKEN_OPEN)::ts,s,L_READ,mem)
             (ts,L_STOP::s,L_READ,mem))
  /\
  (!ts s mem.
     R_parse ((^TOKEN_DOT)::ts,s,L_READ,mem)
             (ts,L_DOT::s,L_READ,mem))
  /\
  (!ts s mem.
     R_parse ((^TOKEN_QUOTE)::ts,s,L_READ,mem)
             (ts,L_QUOTE::s,L_READ,mem))
  /\
  (!ts s mem.
     R_parse ((^TOKEN_CLOSE)::ts,s,L_READ,mem)
             (ts,s,L_COLLECT (Sym "NIL"),mem))
  /\
  (!ts s mem index.
     R_parse ((^TOKEN_LOAD)::ts,s,L_READ,mem)
             (ts,s,L_RETURN (mem index),mem))
  /\
  (!ts s mem index.
     R_parse ((^TOKEN_SAVE)::ts,s,L_READ,mem)
             (ts,L_STORE index::s,L_READ,mem))
  /\
  (* from mode: L_COLLECT *)
  (!ts s mem exp.
     R_parse (ts,L_STOP::s,L_COLLECT exp,mem)
             (ts,s,L_RETURN exp,mem))
  /\
  (!ts s mem x exp.
     R_parse (ts,L_CONS x::s,L_COLLECT exp,mem)
             (ts,s,L_COLLECT (Dot x exp),mem))
  /\
  (!ts s mem exp.
     R_parse (ts,L_DOT::s,L_COLLECT exp,mem)
             (ts,s,L_COLLECT (CAR exp),mem))
  /\
  (* from mode: L_RETURN *)
  (!ts s mem exp.
     R_parse (ts,L_QUOTE::s,L_RETURN exp,mem)
             (ts,s,L_RETURN (Dot (Sym "QUOTE") (Dot exp (Sym "NIL"))),mem))
  /\
  (!ts s mem n exp.
     R_parse (ts,L_STORE n::s,L_RETURN exp,mem)
             (ts,s,L_RETURN exp,(n =+ exp) mem))
  /\
  (!ts s mem exp.
     ~(s = []) /\ ~(HD s = L_QUOTE) /\ ~(?k. HD s = L_STORE k) ==>
     R_parse (ts,s,L_RETURN exp,mem)
             (ts,L_CONS exp::s,L_READ,mem))`

val READ_L_STORE_def = Define `
  (READ_L_STORE (L_STORE n) = SOME n) /\
  (READ_L_STORE _ = NONE)`;

val READ_L_CONS_def = Define `
  (READ_L_CONS (L_CONS exp) = SOME exp) /\
  (READ_L_CONS _ = NONE)`;

val NOT_NIL_IMP = prove(
  ``!x. ~(x = []) ==> ?x1 x2. x = x1::x2``,
  Cases \\ SRW_TAC [] [])

val sexp_parse_aux_def = tDefine "sexp_parse_aux" `
  (sexp_parse_aux (ts,s,L_READ,mem) =
     if ts = [] then Sym "NIL" else
       let (t,ts) = (HD ts, TL ts) in
         if SND t = Val 0 then sexp_parse_aux (ts,s,L_RETURN (FST t),mem) else
         if (t = ^TOKEN_OPEN) then sexp_parse_aux (ts,L_STOP::s,L_READ,mem) else
         if (t = ^TOKEN_DOT) then sexp_parse_aux (ts,L_DOT::s,L_READ,mem) else
         if (t = ^TOKEN_QUOTE) then sexp_parse_aux (ts,L_QUOTE::s,L_READ,mem) else
         if (t = ^TOKEN_CLOSE) then sexp_parse_aux (ts,s,L_COLLECT (Sym "NIL"),mem) else
         if ~isVal (FST t) then Sym "NIL" else
         if SND t = Val 3 then sexp_parse_aux (ts,s,L_RETURN (mem (getVal (FST t))),mem) else
         if SND t = Val 2 then sexp_parse_aux (ts,L_STORE (getVal (FST t))::s,L_READ,mem) else
           Sym "NIL") /\
  (sexp_parse_aux (ts,s,L_COLLECT exp,mem) =
     if s = [] then Sym "NIL" else
       let (x,s) = (HD s, TL s) in
         if x = L_STOP then sexp_parse_aux (ts,s,L_RETURN exp,mem) else
         if ~(READ_L_CONS x = NONE) then sexp_parse_aux (ts,s,L_COLLECT (Dot (THE (READ_L_CONS x)) exp),mem) else
         if x = L_DOT then sexp_parse_aux (ts,s,L_COLLECT (CAR exp),mem) else
           Sym "NIL") /\
  (sexp_parse_aux (ts,s,L_RETURN exp,mem) =
     if s = [] then exp else
       let (x,s) = (HD s, TL s) in
         if x = L_QUOTE then sexp_parse_aux (ts,s,L_RETURN (Dot (Sym "QUOTE") (Dot exp (Sym "NIL"))),mem) else
         if ~(READ_L_STORE x = NONE) then sexp_parse_aux (ts,s,L_RETURN exp,(THE (READ_L_STORE x) =+ exp) mem) else
           sexp_parse_aux (ts,L_CONS exp::x::s,L_READ,mem))`
  (WF_REL_TAC `measure (\(ts,s,mode,mem).
                  3 * LENGTH ts + LENGTH s + if mode = L_READ then 0 else 2)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC NOT_NIL_IMP
   \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)

val RTC_parse_IMP_sexp_parse_aux = prove(
  ``!x y. RTC R_parse x y ==>
          !exp. (FST (SND (SND y)) = L_RETURN exp) /\ (FST (SND y) = []) ==>
                (sexp_parse_aux x = exp)``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ REPEAT STRIP_TAC THEN1
   (`?ts s mode mem. x = (ts,s,mode,mem)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [sexp_parse_aux_def]
    \\ ASM_SIMP_TAC std_ss [])
  \\ `sexp_parse_aux x = sexp_parse_aux x'` suffices_by (STRIP_TAC THEN METIS_TAC [])
  \\ Q.PAT_X_ASSUM `R_parse x x'` MP_TAC
  \\ ONCE_REWRITE_TAC [R_parse_cases]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once sexp_parse_aux_def]
  \\ FULL_SIMP_TAC (srw_ss()) [isVal_def,isSym_def,LET_DEF,getVal_def,
       DECIDE ``~(SUC (SUC n) < 2)``,READ_L_CONS_def,READ_L_STORE_def]
  \\ IMP_RES_TAC NOT_NIL_IMP
  \\ Cases_on `x1`
  \\ FULL_SIMP_TAC (srw_ss()) [isVal_def,isSym_def,LET_DEF,getVal_def,
       DECIDE ``~(SUC (SUC n) < 2)``,READ_L_CONS_def,READ_L_STORE_def]);

val RTC_UNROLL = prove(
  ``!x y z. R x y /\ RTC R y z ==> RTC R x z``,
  METIS_TAC [RTC_RULES]);

val RTC_UNROLL2 = prove(
  ``!x y z. RTC R x y /\ R y z ==> RTC R x z``,
  METIS_TAC [RTC_RULES_RIGHT1]);

val R_parse_abbrev_def = Define `
  R_parse_abbrev abbrevs ps (mem:num->SExp) =
    !s. s IN ps ==> s IN FDOM abbrevs /\ (mem (abbrevs ' s) = s)`;

val FMAP_11_def = Define `
  FMAP_11 f = !x y. x IN FDOM f /\ y IN FDOM f ==> ((f ' x = f ' y) = (x = y))`;

val cons_atoms_def = tDefine "cons_atoms" `
  cons_atoms abbrevs exp s =
    if isAtom abbrevs exp then L_CONS exp :: s else
    if CDR exp = Sym "NIL" then L_CONS (CAR exp) :: s else
    if isAtom abbrevs (CDR exp) then L_CONS (CDR exp)::L_DOT::L_CONS (CAR exp)::s else
      cons_atoms abbrevs (CDR exp) (L_CONS (CAR exp) :: s)`
 (WF_REL_TAC `measure (LSIZE o FST o SND)`
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [isAtom_def,isDot_thm] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def] \\ DECIDE_TAC)

val cons_atoms_lemma = prove(
  ``~isAtom abbrevs (Dot a1 a2) /\ ~(a2 = Sym "NIL") ==>
    (cons_atoms abbrevs (Dot a1 a2) s =
      if isAtom abbrevs a2 then
        L_CONS a2::L_DOT::L_CONS a1::s
      else
        cons_atoms abbrevs a2 (L_CONS a1::s))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once cons_atoms_def]
  \\ ASM_SIMP_TAC std_ss [CDR_def,CAR_def]);

val MAP_L_CONS_COLLECT = prove(
  ``!xs y.
      RTC R_parse (ts,MAP L_CONS xs ++ [L_STOP] ++ s,L_COLLECT y,mem)
                  (ts,s,L_RETURN (FOLDL (\x y. Dot y x) y xs),mem)``,
  Induct THEN1
   (SIMP_TAC std_ss [MAP,FOLDL,APPEND] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ SIMP_TAC std_ss [MAP,FOLDL,APPEND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC RTC_UNROLL
  \\ Q.EXISTS_TAC `(ts,(MAP L_CONS xs ++ [L_STOP] ++ s),L_COLLECT (Dot h y),mem)`
  \\ STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ ASM_SIMP_TAC std_ss []);

val cons_atoms_FOLDL = prove(
  ``!y xs.
      ~(isAtom abbrevs y) ==>
      RTC R_parse
       (ts,cons_atoms abbrevs y (MAP L_CONS xs ++ [L_STOP] ++ s),L_COLLECT (Sym "NIL"),mem)
       (ts,s,L_RETURN (FOLDL (\x y. Dot y x) y xs),mem)``,
  completeInduct_on `LSIZE y` \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [cons_atoms_def]
  \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  THEN1
   (`isDot y` by METIS_TAC [isAtom_def]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def] \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,MAP L_CONS xs ++ [L_STOP] ++ s, L_COLLECT y,mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ASM_SIMP_TAC std_ss [MAP_L_CONS_COLLECT])
  THEN1
   (`isDot y` by METIS_TAC [isAtom_def]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def] \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,L_DOT::L_CONS a::(MAP L_CONS xs ++ [L_STOP] ++ s), L_COLLECT (Dot b (Sym "NIL")),mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,L_CONS a::(MAP L_CONS xs ++ [L_STOP] ++ s), L_COLLECT b,mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [CAR_def])
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,(MAP L_CONS xs ++ [L_STOP] ++ s), L_COLLECT (Dot a b),mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [CAR_def])
    \\ ASM_SIMP_TAC std_ss [MAP_L_CONS_COLLECT])
  \\ `isDot y` by METIS_TAC [isAtom_def]
  \\ FULL_SIMP_TAC std_ss [isDot_thm]
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def,CAR_def]
  \\ `LSIZE b < SUC (LSIZE a + LSIZE b)` by DECIDE_TAC
  \\ RES_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `b`)
  \\ Q.PAT_X_ASSUM `!m.bb` (K ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `a::xs`)
  \\ SIMP_TAC std_ss [APPEND,MAP,FOLDL]);

val R_parse_lemma = prove(
  ``!exp b ts s mem ps.
      (~b ==> ~(s = []) /\ ~(HD s = L_QUOTE) /\ ~(?k. HD s = L_STORE k)) /\
      FMAP_11 abbrevs /\ R_parse_abbrev abbrevs ps mem ==>
      ?ps5 mem5 str5.
         (sexp2abbrevt_aux exp b abbrevs ps = (str5,ps5)) /\
         RTC R_parse (str5 ++ ts,s,L_READ,mem)
                     (if b then (ts,s,L_RETURN exp,mem5)
                      else (ts,cons_atoms abbrevs exp s,L_READ,mem5)) /\
         R_parse_abbrev abbrevs ps5 mem5``,
  HO_MATCH_MP_TAC SExp_print_induct \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [sexp2abbrevt_aux_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `index = abbrevs ' exp`
  \\ Q.ABBREV_TAC `prefix = if exp IN FDOM abbrevs then [^TOKEN_SAVE] else []`
  \\ Q.ABBREV_TAC `ps0 = if exp IN FDOM abbrevs then exp INSERT ps else ps`
  \\ `(if exp IN FDOM abbrevs then
        ([^TOKEN_SAVE],exp INSERT ps)
      else
        ([],ps)) = (prefix,ps0)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `exp IN ps` \\ ASM_SIMP_TAC std_ss [] THEN1
   (`exp IN FDOM abbrevs` by METIS_TAC [R_parse_abbrev_def]
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `mem`
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ FULL_SIMP_TAC std_ss [R_parse_abbrev_def]
    \\ Q.UNABBREV_TAC `index`
    \\ RES_TAC
    \\ Q.EXISTS_TAC `(ts,s,L_RETURN exp,mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL]
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ ONCE_REWRITE_TAC [cons_atoms_def]
    \\ ASM_SIMP_TAC std_ss [isAtom_def]
    \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `?str1 ps1. sexp2abbrevt_aux (CAR exp) T abbrevs ps = (str1,ps1)` by METIS_TAC [PAIR]
  \\ `?str2 ps2. sexp2abbrevt_aux (CDR exp) F abbrevs ps1 = (str2,ps2)` by METIS_TAC [PAIR]
  \\ `?str3 ps3. sexp2abbrevt_aux (CAR (CDR exp)) T abbrevs ps = (str3,ps3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `s1 = if b \/ prefix <> [] then [^TOKEN_OPEN] else []`
  \\ Q.ABBREV_TAC `s2 = if b \/ prefix <> [] then [^TOKEN_CLOSE] else []`
  \\ `(if b \/ prefix <> [] then ([^TOKEN_OPEN],[^TOKEN_CLOSE])
       else ([],[])) = (s1,s2)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ `!tts. RTC R_parse (prefix ++ tts,s,L_READ,mem)
        (tts,(if exp IN FDOM abbrevs
              then (L_STORE (abbrevs ' exp))::s else s),L_READ,mem)` by
   (Q.UNABBREV_TAC `prefix`
    \\ REVERSE (Cases_on `exp IN FDOM abbrevs`)
    \\ ASM_SIMP_TAC std_ss [APPEND,RTC_REFL]
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC RTC_SINGLE
    \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.ABBREV_TAC `s9 = if exp IN FDOM abbrevs then L_STORE (abbrevs ' exp)::s else s`
  \\ Cases_on `~(isDot exp)` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ONCE_REWRITE_TAC [cons_atoms_def] \\ ASM_SIMP_TAC std_ss [isAtom_def,isDot_def]
    \\ Q.EXISTS_TAC `if exp IN FDOM abbrevs then (abbrevs ' exp =+ exp) mem else mem`
    \\ REVERSE STRIP_TAC THEN1
     (Q.UNABBREV_TAC `ps0` \\ POP_ASSUM (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `exp IN FDOM abbrevs`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [IN_INSERT,R_parse_abbrev_def,APPLY_UPDATE_THM]
      \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``exp2:SExp``)) \\ STRIP_TAC
      \\ Cases_on `exp2 = exp` \\ ASM_SIMP_TAC std_ss []
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [FMAP_11_def])
    \\ Q.ABBREV_TAC `mem2 = if exp IN FDOM abbrevs then (abbrevs ' exp =+ exp) mem else mem`
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `([(exp,Val 0)] ++ ts,s9,L_READ,mem)`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,s9,L_RETURN exp,mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Q.UNABBREV_TAC `s9`
    \\ Q.UNABBREV_TAC `mem2`
    \\ REVERSE (Cases_on `exp IN FDOM abbrevs` \\ ASM_SIMP_TAC std_ss [])
    THEN1 (Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL] \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,s,L_RETURN exp,(abbrevs ' exp =+ exp) mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    THEN1 (Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL] \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) []))
  \\ Cases_on `isQuote exp` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ONCE_REWRITE_TAC [cons_atoms_def] \\ ASM_SIMP_TAC std_ss [isAtom_def,isDot_def]
    \\ FULL_SIMP_TAC std_ss [isQuote_thm] \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!b ts. bbb` (MP_TAC o Q.SPECL [`T`,`ts`,`L_QUOTE::s9`,`mem`,`ps`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `mem6 = if exp IN FDOM abbrevs then (abbrevs ' exp =+ exp) mem5 else mem5`
    \\ Q.EXISTS_TAC `mem6`
    \\ REVERSE STRIP_TAC THEN1
     (Q.UNABBREV_TAC `mem6` \\ POP_ASSUM (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `exp IN FDOM abbrevs`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [IN_INSERT,R_parse_abbrev_def,APPLY_UPDATE_THM]
      \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``exp2:SExp``)) \\ STRIP_TAC
      \\ Cases_on `exp2 = exp` \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_INSERT]
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [FMAP_11_def])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `([^TOKEN_QUOTE] ++ str3 ++ ts,s9,L_READ,mem)`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(str3 ++ ts,L_QUOTE::s9,L_READ,mem)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(ts,L_QUOTE::s9,L_RETURN y,mem5)`
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,s9,L_RETURN exp,mem5)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `s9`
    \\ Q.UNABBREV_TAC `mem6`
    \\ REVERSE (Cases_on `exp IN FDOM abbrevs` \\ ASM_SIMP_TAC std_ss [])
    THEN1 (Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL] \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(ts,s,L_RETURN exp,(abbrevs ' exp =+ exp) mem5)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    THEN1 (Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL] \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) []))
  \\ FULL_SIMP_TAC std_ss []
  \\ `?a1 a2. exp = Dot a1 a2` by METIS_TAC [isDot_thm]
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def]
  \\ Cases_on `a2 = Sym "NIL"` \\ FULL_SIMP_TAC std_ss [APPEND_NIL] THEN1
   (Q.PAT_X_ASSUM `!b ts. bbb` (K ALL_TAC)
    \\ Q.ABBREV_TAC `s8 = if s1 = [] then s9 else L_STOP::s9`
    \\ Q.PAT_X_ASSUM `!b ts. bbb` (MP_TAC o Q.SPECL [`T`,`s2++ts`,`s8`,`mem`,`ps`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `mem6 = if exp IN FDOM abbrevs then (abbrevs ' exp =+ exp) mem5 else mem5`
    \\ Q.EXISTS_TAC `mem6`
    \\ REVERSE STRIP_TAC THEN1
     (Q.UNABBREV_TAC `mem6` \\ POP_ASSUM (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `exp IN FDOM abbrevs`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [IN_INSERT,R_parse_abbrev_def,APPLY_UPDATE_THM]
      \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``exp2:SExp``)) \\ STRIP_TAC
      \\ Cases_on `exp2 = exp` \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_INSERT]
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [FMAP_11_def])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1 ++ str1 ++ s2 ++ ts,s9,L_READ,mem)`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `((str1 ++ (s2 ++ ts)),s8,L_READ,mem)`
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `s8` \\ Cases_on `s1 = []`
      \\ ASM_SIMP_TAC std_ss [APPEND,RTC_REFL]
      \\ Q.UNABBREV_TAC `s1` \\ Cases_on `b \/ prefix <> []`
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s2 ++ ts,s8,L_RETURN a1,mem5)`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(s2 ++ ts,L_CONS a1::s8,L_READ,mem5)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) []
           \\ FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
           \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) [NOT_CONS_NIL,HD]
           \\ METIS_TAC [NOT_CONS_NIL,fetch "-" "lisp_parse_action_distinct",HD,CONS_11])
    \\ Cases_on `s2 = []` THEN1
     (`~b` by METIS_TAC [NOT_CONS_NIL]
      \\ `s1 = []` by METIS_TAC [NOT_CONS_NIL]
      \\ FULL_SIMP_TAC std_ss [APPEND]
      \\ Q.UNABBREV_TAC `s8`
      \\ `(s9 = s) /\ ~(exp IN FDOM abbrevs)` by METIS_TAC [NOT_CONS_NIL]
      \\ POP_ASSUM MP_TAC
      \\ ONCE_REWRITE_TAC [cons_atoms_def] \\ Q.UNABBREV_TAC `mem6`
      \\ ASM_SIMP_TAC std_ss [isAtom_def,CAR_def,CDR_def,RTC_REFL])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(ts,s9,L_RETURN exp,mem5)`
    \\ STRIP_TAC THEN1
     (`s2 = [^TOKEN_CLOSE]` by METIS_TAC [] \\ ASM_SIMP_TAC std_ss [APPEND]
      \\ `s8 = L_STOP::s9` by METIS_TAC [NOT_CONS_NIL] \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC RTC_UNROLL
      \\ Q.EXISTS_TAC `(ts,L_CONS a1::L_STOP::s9,L_COLLECT (Sym "NIL"),mem5)`
      \\ STRIP_TAC
      THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ MATCH_MP_TAC RTC_UNROLL
      \\ Q.EXISTS_TAC `(ts,L_STOP::s9,L_COLLECT (Dot a1 (Sym "NIL")),mem5)`
      \\ STRIP_TAC
      THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ MATCH_MP_TAC RTC_UNROLL
      \\ Q.EXISTS_TAC `(ts,s9,L_RETURN (Dot a1 (Sym "NIL")),mem5)`
      \\ STRIP_TAC
      THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ ASM_SIMP_TAC std_ss [RTC_REFL])
    \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(ts,s,L_RETURN exp,mem6)`
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `s9` \\ Q.UNABBREV_TAC `mem6`
      \\ Cases_on `exp IN FDOM abbrevs` \\ ASM_SIMP_TAC std_ss [RTC_REFL]
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL]
    \\ ONCE_REWRITE_TAC [cons_atoms_def]
    \\ `isAtom abbrevs exp` by METIS_TAC [NOT_CONS_NIL,isAtom_def]
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `!b ts. bbb` MP_TAC
    \\ Q.ABBREV_TAC `s8 = if s1 = [] then s9 else L_STOP::s9`
    \\ Q.ABBREV_TAC `s7 = if isAtom abbrevs a2 then L_DOT::L_CONS a1::s8 else L_CONS a1::s8`
    \\ `~(s7 = [])` by METIS_TAC [NOT_CONS_NIL]
    \\ `~(s8 = [])` by (FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def] \\ Cases_on `b`
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL] \\ METIS_TAC [NOT_CONS_NIL])
    \\ `HD s7 <> L_QUOTE /\ (!k. HD s7 <> L_STORE k)` by
      (METIS_TAC [NOT_CONS_NIL,fetch "-" "lisp_parse_action_distinct",HD,CONS_11])
    \\ Q.PAT_X_ASSUM `!b ts. bbb` (MP_TAC o Q.SPECL [`T`,`((if isAtom (abbrevs:SExp|->num) a2 then [^TOKEN_DOT] else []) ++ str2) ++ s2++ts`,`s8`,`mem`,`ps`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`F`,`s2++ts`,`s7`,`mem5`,`ps1`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `mem6 = if exp IN FDOM abbrevs then (abbrevs ' exp =+ exp) mem5' else mem5'`
    \\ Q.EXISTS_TAC `mem6`
    \\ REVERSE STRIP_TAC THEN1
     (Q.UNABBREV_TAC `mem6` \\ POP_ASSUM (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `exp IN FDOM abbrevs`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [IN_INSERT,R_parse_abbrev_def,APPLY_UPDATE_THM]
      \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``exp2:SExp``)) \\ STRIP_TAC
      \\ Cases_on `exp2 = exp` \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_INSERT,R_parse_abbrev_def]
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [FMAP_11_def])
    \\ Q.ABBREV_TAC `dot = if isAtom abbrevs a2 then [^TOKEN_DOT] else []`
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s1 ++ str1 ++ (dot ++ str2) ++ s2 ++ ts,s9,L_READ,mem)`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(str1 ++ (dot ++ (str2 ++ (s2 ++ ts))),s8,L_READ,mem)`
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `s8` \\ Cases_on `s1 = []`
      \\ ASM_SIMP_TAC std_ss [APPEND,RTC_REFL]
      \\ Q.UNABBREV_TAC `s1` \\ Cases_on `b \/ prefix <> []`
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(dot ++ str2 ++ s2 ++ ts,s8,L_RETURN a1,mem5)`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ MATCH_MP_TAC RTC_UNROLL
    \\ Q.EXISTS_TAC `(dot ++ (str2 ++ (s2 ++ ts)),L_CONS a1::s8,L_READ,mem5)`
    \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) []
           \\ METIS_TAC [NOT_CONS_NIL,fetch "-" "lisp_parse_action_distinct",HD,CONS_11])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(str2 ++ s2 ++ ts,s7,L_READ,mem5)`
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `dot` \\ Q.UNABBREV_TAC `s7`
      \\ Cases_on `isAtom abbrevs a2` \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [RTC_REFL,APPEND,APPEND_ASSOC]
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(s2 ++ ts,cons_atoms abbrevs a2 s7,L_READ,mem5')`
    \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ Cases_on `s2 = []` THEN1
     (`~b` by METIS_TAC [NOT_CONS_NIL]
      \\ `s1 = []` by METIS_TAC [NOT_CONS_NIL]
      \\ FULL_SIMP_TAC std_ss [APPEND]
      \\ Q.UNABBREV_TAC `s8`
      \\ Q.UNABBREV_TAC `s7`
      \\ `(s9 = s) /\ ~(exp IN FDOM abbrevs)` by METIS_TAC [NOT_CONS_NIL]
      \\ POP_ASSUM MP_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `isAtom abbrevs a2` \\ ASM_SIMP_TAC std_ss []
      \\ Q.UNABBREV_TAC `mem6`
      \\ REPEAT STRIP_TAC
      \\ `~(isAtom abbrevs (Dot a1 a2))` by (FULL_SIMP_TAC std_ss [isAtom_def])
      \\ ASM_SIMP_TAC std_ss [cons_atoms_lemma,RTC_REFL]
      \\ ONCE_REWRITE_TAC [cons_atoms_def] \\ ASM_SIMP_TAC std_ss [RTC_REFL])
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(ts,s9,L_RETURN exp,mem5')`
    \\ STRIP_TAC THEN1
     (`s2 = [^TOKEN_CLOSE]` by METIS_TAC [] \\ ASM_SIMP_TAC std_ss [APPEND]
      \\ `s8 = L_STOP::s9` by METIS_TAC [NOT_CONS_NIL] \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC RTC_UNROLL
      \\ Q.EXISTS_TAC `(ts,cons_atoms abbrevs a2 s7,L_COLLECT (Sym "NIL"),mem5')`
      \\ STRIP_TAC
      THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ Q.UNABBREV_TAC `s7` \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `isAtom abbrevs a2` \\ ASM_SIMP_TAC std_ss [] THEN1
       (ONCE_REWRITE_TAC [cons_atoms_def] \\ ASM_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC RTC_UNROLL
        \\ Q.EXISTS_TAC `(ts,L_DOT::L_CONS a1::L_STOP::s9,L_COLLECT (Dot a2 (Sym "NIL")),mem5')`
        \\ STRIP_TAC
        THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
        \\ MATCH_MP_TAC RTC_UNROLL
        \\ Q.EXISTS_TAC `(ts,L_CONS a1::L_STOP::s9,L_COLLECT a2,mem5')`
        \\ STRIP_TAC
        THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [CAR_def])
        \\ MATCH_MP_TAC RTC_UNROLL
        \\ Q.EXISTS_TAC `(ts,L_STOP::s9,L_COLLECT (Dot a1 a2),mem5')`
        \\ STRIP_TAC
        THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [CAR_def])
        \\ MATCH_MP_TAC RTC_UNROLL
        \\ Q.EXISTS_TAC `(ts,s9,L_RETURN (Dot a1 a2),mem5')`
        \\ STRIP_TAC
        THEN1 (ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [CAR_def])
        \\ ASM_SIMP_TAC std_ss [RTC_REFL])
      \\ MATCH_MP_TAC (SIMP_RULE std_ss [MAP,APPEND,FOLDL] (Q.SPECL [`a2`,`[a1]`] cons_atoms_FOLDL))
      \\ ASM_SIMP_TAC std_ss [])
    \\ Q.PAT_X_ASSUM `exp = bbbb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
    \\ Q.EXISTS_TAC `(ts,s,L_RETURN exp,mem6)`
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `s9` \\ Q.UNABBREV_TAC `mem6`
      \\ Cases_on `exp IN FDOM abbrevs` \\ ASM_SIMP_TAC std_ss [RTC_REFL]
      \\ MATCH_MP_TAC RTC_SINGLE
      \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [RTC_REFL]
    \\ `exp IN FDOM abbrevs` by METIS_TAC [NOT_CONS_NIL]
    \\ ASM_SIMP_TAC std_ss [Once cons_atoms_def,isAtom_def]
    \\ MATCH_MP_TAC RTC_SINGLE
    \\ ONCE_REWRITE_TAC [R_parse_cases] \\ FULL_SIMP_TAC (srw_ss()) []);

val R_parse_thm = prove(
  ``!exp ts s mem abbrevs.
      FMAP_11 abbrevs ==>
      ?mem2.
         RTC R_parse (FST (sexp2abbrevt_aux exp T abbrevs {}) ++ ts,s,L_READ,mem)
                     (ts,s,L_RETURN exp,mem2)``,
  REPEAT STRIP_TAC
  \\ `?str ps. sexp2abbrevt_aux exp T abbrevs {} = (str,ps)` by METIS_TAC [PAIR]
  \\ MP_TAC (Q.SPECL [`exp`,`T`,`ts`,`s`,`mem`,`{}`] R_parse_lemma)
  \\ ASM_SIMP_TAC std_ss [R_parse_abbrev_def,NOT_IN_EMPTY] \\ METIS_TAC []);

val sexp_parse_def = Define `
  sexp_parse ts = sexp_parse_aux (ts,[],L_READ,\x.Sym "NIL")`;

val sexp_parse_aux_sexp2abbrevt = prove(
  ``!exp ts abbrevs.
      FMAP_11 abbrevs ==>
      (sexp_parse (FST (sexp2abbrevt_aux exp T abbrevs {}) ++ ts) = exp)``,
  METIS_TAC [R_parse_thm,RTC_parse_IMP_sexp_parse_aux,FST,SND,sexp_parse_def]);

val string2sexp_def = Define `
  string2sexp str = (sexp_parse (FST (sexp_lex str)))`;

val FDOM_sexp_abbrev_fmap_IMP = prove(
  ``!xs x k. x IN FDOM (sexp_abbrev_fmap xs k) ==>
             k <= sexp_abbrev_fmap xs k ' x``,
  Induct \\ SIMP_TAC (srw_ss()) [sexp_abbrev_fmap_def,
    FDOM_FEMPTY,FAPPLY_FUPDATE_THM] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ RES_TAC
  \\ METIS_TAC [LESS_EQ_REFL,DECIDE ``k <= k+1:num``,LESS_EQ_TRANS]);

val FMAP_11_sexp_abbrev_fmap = prove(
  ``!xs k. FMAP_11 (sexp_abbrev_fmap xs k)``,
  Induct \\ SIMP_TAC (srw_ss()) [sexp_abbrev_fmap_def,
    FMAP_11_def,FDOM_FEMPTY,FAPPLY_FUPDATE_THM]
  \\ REVERSE (REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [])
  THEN1 METIS_TAC [FMAP_11_def]
  \\ IMP_RES_TAC FDOM_sexp_abbrev_fmap_IMP \\ DECIDE_TAC);

val string2sexp_sexp2abbrev = store_thm("string2sexp_sexp2abbrev",
  ``!exp abbrevs. string2sexp (sexp2abbrev exp abbrevs) = exp``,
  SIMP_TAC std_ss [string2sexp_def,sexp2abbrev_def,sexp_lex_sexp2abbrev_aux]
  \\ METIS_TAC [sexp_parse_aux_sexp2abbrevt,FMAP_11_sexp_abbrev_fmap,APPEND_NIL]);

val string2sexp_sexp2string = store_thm("string2sexp_sexp2string",
  ``!exp. string2sexp (sexp2string exp) = exp``,
  ASM_SIMP_TAC std_ss [GSYM sexp2abbrev_NIL,string2sexp_sexp2abbrev]);


(* Part 2 - section 3: merge lexer and parser *)

val next_token_IMP = prove(
  ``(((p,Val n),ds) = next_token cs) ==> LENGTH ds < LENGTH cs``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC next_token_LENGTH
  \\ FULL_SIMP_TAC std_ss [next_token_def,SExp_distinct]);

val sexp_lex_parse_def = tDefine "sexp_lex_parse" `
  (sexp_lex_parse (cs,s,L_READ,mem) =
     let (t,cs) = next_token cs in
       if SND t = Sym "NIL" then (Sym "NIL",cs) else (* error or end of input *)
       if SND t = Val 0 then sexp_lex_parse (cs,s,L_RETURN (FST t),mem) else
       if (t = ^TOKEN_OPEN) then sexp_lex_parse (cs,L_STOP::s,L_READ,mem) else
       if (t = ^TOKEN_DOT) then sexp_lex_parse (cs,L_DOT::s,L_READ,mem) else
       if (t = ^TOKEN_QUOTE) then sexp_lex_parse (cs,L_QUOTE::s,L_READ,mem) else
       if (t = ^TOKEN_CLOSE) then sexp_lex_parse (cs,s,L_COLLECT (Sym "NIL"),mem) else
       if ~isVal (FST t) then (Sym "NIL",cs) else
       if SND t = Val 3 then sexp_lex_parse (cs,s,L_RETURN (mem (getVal (FST t))),mem) else
       if SND t = Val 2 then sexp_lex_parse (cs,L_STORE (getVal (FST t))::s,L_READ,mem) else
         (Sym "NIL",cs)) /\
  (sexp_lex_parse (cs,s,L_COLLECT exp,mem) =
     if s = [] then (Sym "NIL",cs) else
       let (x,s) = (HD s, TL s) in
         if x = L_STOP then sexp_lex_parse (cs,s,L_RETURN exp,mem) else
         if ~(READ_L_CONS x = NONE) then sexp_lex_parse (cs,s,L_COLLECT (Dot (THE (READ_L_CONS x)) exp),mem) else
         if x = L_DOT then sexp_lex_parse (cs,s,L_COLLECT (CAR exp),mem) else
           (Sym "NIL",cs)) /\
  (sexp_lex_parse (cs,s,L_RETURN exp,mem) =
     if s = [] then (exp,cs) else
       let (x,s) = (HD s, TL s) in
         if x = L_QUOTE then sexp_lex_parse (cs,s,L_RETURN (Dot (Sym "QUOTE") (Dot exp (Sym "NIL"))),mem) else
         if ~(READ_L_STORE x = NONE) then sexp_lex_parse (cs,s,L_RETURN exp,(THE (READ_L_STORE x) =+ exp) mem) else
           sexp_lex_parse (cs,L_CONS exp::x::s,L_READ,mem))`
  (WF_REL_TAC `measure (\(cs,s,mode,mem).
                  3 * LENGTH cs + LENGTH s + if mode = L_READ then 0 else 2)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC NOT_NIL_IMP
   \\ IMP_RES_TAC next_token_IMP \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val sexp_parse_stream_def = Define `
  sexp_parse_stream cs = sexp_lex_parse (cs,[],L_READ,\x.Sym "NIL")`;


(*

val sexp_lex_parse_thm = prove(
  ``!cs ds s x mem.
      (~(ds = []) ==> MEM (HD ds) " )") ==>
      (sexp_lex_parse (cs++ds,s,x,mem) =
        (sexp_parse_aux (FST (sexp_lex (cs++ds)),s,x,mem),ds))``,

val sexp_parse_stream_thm = store_thm("sexp_parse_stream_thm",
  ``!exp abbrevs s.
      (~(s = []) ==> MEM (HD s) " )") ==>
      (sexp_parse_stream (sexp2abbrev exp abbrevs ++ s) = (exp,s))``,
  SIMP_TAC std_ss [sexp_parse_stream_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC sexp_lex_parse_thm \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [sexp2abbrev_def]
  \\ `?xs1 ps1. sexp2abbrev_aux exp T (sexp_abbrev_fmap abbrevs 0) {} = (xs1,ps1)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ `?xs2 ps2. (xs2,ps2) = sexp2abbrevt_aux exp T (sexp_abbrev_fmap abbrevs 0) {}` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC sexp2abbrev_aux_FST
  \\ ASM_SIMP_TAC std_ss []
  \\ `xs2 = FST (sexp2abbrevt_aux exp T (sexp_abbrev_fmap abbrevs 0) {})` by
   (Cases_on `sexp2abbrevt_aux exp T (sexp_abbrev_fmap abbrevs 0) {}`
    \\ FULL_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [GSYM sexp_parse_def]
  \\ MATCH_MP_TAC sexp_parse_aux_sexp2abbrevt
  \\ ASM_SIMP_TAC std_ss [FMAP_11_sexp_abbrev_fmap]);

*)

val _ = export_theory();
