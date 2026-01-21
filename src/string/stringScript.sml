(* =====================================================================*)
(* FILE         : stringScript.sml                                      *)
(* DESCRIPTION  : A theory of 8-bit characters and strings built        *)
(*                from them.                                            *)
(*                                                                      *)
(* AUTHOR       : Konrad Slind, University of Cambridge, 2001           *)
(* =====================================================================*)

Theory string
Ancestors
  rich_list ternaryComparisons
  list arithmetic pred_set relation
Libs
  numLib numSyntax

(* ---------------------------------------------------------------------*)
(* Characters are represented by the natural numbers <= 255.            *)
(* ---------------------------------------------------------------------*)

val is_char =
 let val n = mk_var("n",num)
     val topnum = mk_numeral (Arbnum.fromInt 256)
 in mk_abs(n,mk_less(n,topnum))
 end;

Theorem CHAR_EXISTS[local]:
   ?n. ^is_char n
Proof Q.EXISTS_TAC `0` THEN REDUCE_TAC
QED

val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS);

val CHAR_TYPE_FACTS =
    (define_new_type_bijections
       {ABS="CHR", REP="ORD",name="char_BIJ", tyax=CHAR_TYPE});

Theorem ORD_11 = prove_rep_fn_one_one CHAR_TYPE_FACTS
Theorem CHR_11[simp] =
                         BETA_RULE (prove_abs_fn_one_one CHAR_TYPE_FACTS);
Theorem ORD_ONTO =
                         BETA_RULE (prove_rep_fn_onto CHAR_TYPE_FACTS);
Theorem CHR_ONTO =
                         BETA_RULE (prove_abs_fn_onto CHAR_TYPE_FACTS);

Theorem CHR_ORD[simp] = CONJUNCT1 CHAR_TYPE_FACTS
Theorem ORD_CHR = BETA_RULE (CONJUNCT2 CHAR_TYPE_FACTS);

Theorem ORD_CHR_RWT[simp]:
  !r. r < 256 ==> (ORD (CHR r) = r)
Proof
 PROVE_TAC [ORD_CHR]
QED

Theorem ORD_CHR_COMPUTE[compute]:
  !n. ORD (CHR n) =
      if n < 256 then n else FAIL ORD ^(mk_var("> 255", bool)) (CHR n)
Proof SRW_TAC [] [combinTheory.FAIL_THM]
QED

Theorem ORD_BOUND:
  !c. ORD c < 256
Proof
 PROVE_TAC [ORD_ONTO]
QED

Theorem char_nchotomy:
   !c. ?n. c = CHR n
Proof
  STRIP_TAC THEN Q.EXISTS_TAC `ORD c` THEN REWRITE_TAC [CHR_ORD]
QED

Theorem ranged_char_nchotomy:
   !c. ?n. (c = CHR n) /\ n < 256
Proof
  STRIP_TAC THEN Q.EXISTS_TAC `ORD c` THEN REWRITE_TAC [CHR_ORD, ORD_BOUND]
QED

val ordn = term_of_int o Char.ord;

Definition isLower_def:
  isLower c <=> ^(ordn #"a") <= ORD c /\ ORD c <= ^(ordn #"z")
End

Definition isUpper_def:
  isUpper c <=> ^(ordn #"A") <= ORD c /\ ORD c <= ^(ordn #"Z")
End

Definition isDigit_def:
  isDigit c <=> ^(ordn #"0") <= ORD c /\ ORD c <= ^(ordn #"9")
End

Definition isAlpha_def:   isAlpha c <=> isLower c \/ isUpper c
End

Definition isHexDigit_def:
  isHexDigit c <=> ^(ordn #"0") <= ORD c /\ ORD c <= ^(ordn #"9") \/
                   ^(ordn #"a") <= ORD c /\ ORD c <= ^(ordn #"f") \/
                   ^(ordn #"A") <= ORD c /\ ORD c <= ^(ordn #"F")
End

Definition isAlphaNum_def:   isAlphaNum c <=> isAlpha c \/ isDigit c
End

Definition isPrint_def:
  isPrint c <=> ^(ordn #" ") <= ORD c /\ ORD c < 127
End

Theorem isAlphaNum_isPrint:
  !x. isAlphaNum x ==> isPrint x
Proof EVAL_TAC \\ rw[]
QED

Theorem isHexDigit_isAlphaNum:
  !x. isHexDigit x ==> isAlphaNum x
Proof EVAL_TAC \\ rw[]
QED

Theorem isHexDigit_isPrint:
  !x. isHexDigit x ==> isPrint x
Proof metis_tac[isAlphaNum_isPrint, isHexDigit_isAlphaNum]
QED

Definition isSpace_def:
  isSpace c <=> (ORD c = ^(ordn #" ")) \/ 9 <= ORD c /\ ORD c <= 13
End

Definition isGraph_def:   isGraph c <=> isPrint c /\ ~isSpace c
End

Definition isPunct_def:   isPunct c <=> isGraph c /\ ~isAlphaNum c
End

Definition isAscii_def:   isAscii c <=> ORD c <= 127
End

Definition isCntrl_def:
  isCntrl c <=> ORD c < ^(ordn #" ") \/ 127 <= ORD c
End

Definition toLower_def:
  toLower c = if isUpper c then CHR (ORD c + 32) else c
End

Definition toUpper_def:
  toUpper c = if isLower c then CHR (ORD c - 32) else c
End

Definition char_lt_def:   char_lt a b <=> ORD a < ORD b
End
Definition char_le_def:   char_le a b <=> ORD a <= ORD b
End
Definition char_gt_def:   char_gt a b <=> ORD a > ORD b
End
Definition char_ge_def:   char_ge a b <=> ORD a >= ORD b
End

Definition char_compare_def:
  char_compare c1 c2 = num_compare (ORD c1) (ORD c2)
End

Overload "<"[inferior] = “char_lt”
Overload ">"[inferior] = “char_gt”
Overload "<="[inferior] = “char_le”
Overload ">="[inferior] = “char_ge”

(*---------------------------------------------------------------------------
    In our development, CHR is not a constructor. Is that really
    important? We can at least prove the following theorem about
    equality of chars.
 ---------------------------------------------------------------------------*)

Theorem CHAR_EQ_THM[compute]:
  !c1 c2. (c1 = c2) = (ORD c1 = ORD c2)
Proof REPEAT GEN_TAC THEN EQ_TAC THEN RW_TAC bool_ss [ORD_11]
QED

Theorem CHAR_INDUCT_THM:
  !P. (!n. n < 256 ==> P (CHR n)) ==> !c. P c
Proof
REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `c` CHR_ONTO)
  THEN RW_TAC bool_ss []
QED

Definition char_size_def:   char_size (c:char) = 0
End

val _ = TypeBase.export [
    TypeBasePure.mk_nondatatype_info (
      “:char”,
      {nchotomy = SOME ranged_char_nchotomy,
       induction = NONE,
       size = SOME(“char_size”,char_size_def),
       encode = NONE}
    )
  ]

(*---------------------------------------------------------------------------
    Some facts about the set of all characters and relations between them.
 ---------------------------------------------------------------------------*)

Theorem UNIV_IMAGE_CHR_count_256:
  UNIV = IMAGE CHR (count 256)
Proof
  rw[EXTENSION]
  \\ qspec_then`x`FULL_STRUCT_CASES_TAC ranged_char_nchotomy
  \\ metis_tac[]
QED

Theorem FINITE_UNIV_char[simp]:
  FINITE (UNIV:char set)
Proof
  simp[UNIV_IMAGE_CHR_count_256]
QED

Theorem RC_char_lt:
  RC (char_lt) = char_le
Proof
  rw[FUN_EQ_THM, RC_DEF, char_le_def, char_lt_def, arithmeticTheory.LESS_OR_EQ]
  \\ metis_tac[ORD_11]
QED

Theorem WF_char_lt[simp]:
  WF char_lt
Proof
  rw[WF_DEF]
  \\ qexists_tac`CHR (LEAST n. (n < 256) /\ B (CHR n))`
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac
  >- (qspec_then`w`FULL_STRUCT_CASES_TAC ranged_char_nchotomy
      \\ fs[] \\ metis_tac[])
  \\ rw[] \\ qspec_then`b`FULL_STRUCT_CASES_TAC ranged_char_nchotomy
  \\ fs[char_lt_def] \\ rfs[]
QED

(*---------------------------------------------------------------------------
      Strings are represented as lists of characters. This gives us
      EXPLODE and IMPLODE as the functions mapping into, and from, the
      representation.
 ---------------------------------------------------------------------------*)

Type string[pp] = ``:char list``

Overload STRING[inferior] = “CONS : char -> string -> string”
Overload EMPTYSTRING[inferior] = “[] : string”
Overload CONCAT[inferior] = “FLAT : string list -> string”

Definition string_compare_def:
  string_compare = list_compare char_compare
End

val _ = new_definition(GrammarSpecials.string_elim_term,
                       “^(mk_var(GrammarSpecials.string_elim_term,
                                  “:string -> string”)) s = s”);
val _ = overload_on(GrammarSpecials.std_stringinjn_name,
                    mk_const(GrammarSpecials.string_elim_term,
                             “:string -> string”))

Definition SUB_def:   SUB (s:string, n) = EL n s
End
Definition STR_def:   STR (c:char) = [c]
End
Definition TOCHAR_def:   TOCHAR [c] = c: char
End

Definition SUBSTRING_def:   SUBSTRING (s:string,i,n) = SEG n i s
End

Definition TRANSLATE_def:   TRANSLATE f (s:string) = CONCAT (MAP f s)
End

Theorem SPLITP_MONO[local]:
   !P l. LENGTH (SND (SPLITP P l)) <= LENGTH l
Proof
  Induct_on `l` THEN SRW_TAC [] [SPLITP, DECIDE ``a <= b ==> a <= SUC b``]
QED

Theorem TAIL_MONO[local]:
   !l. ~(l = []) ==> LENGTH (TL l) < LENGTH l
Proof Cases THEN SRW_TAC [] []
QED

Definition TOKENS_def:
  (TOKENS P ([]:string) = []) /\
  (TOKENS P (h::t) =
      let (l,r) = SPLITP P (h::t) in
        if NULL l then
          TOKENS P (TL r)
        else
          l::TOKENS P r)
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
    THEN SRW_TAC [] [NULL_EQ_NIL, SPLITP]
    THEN METIS_TAC [SPLITP_MONO, DECIDE ``a <= b ==> a < SUC b``]
End

Definition FIELDS_def:
  (FIELDS P ([]:string) = [[]]) /\
  (FIELDS P (h::t) =
      let (l,r) = SPLITP P (h::t) in
        if NULL l then
          []::FIELDS P (TL r)
        else
          if NULL r then [l] else l::FIELDS P (TL r))
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
    THEN SRW_TAC [] [NULL_EQ_NIL, SPLITP]
    THEN METIS_TAC [SPLITP_MONO, TAIL_MONO, arithmeticTheory.LESS_TRANS,
           DECIDE ``a <= b ==> a < 1 + SUC b``]
End

Definition IMPLODE_def[simp]:
  (IMPLODE [] = "") /\
  (IMPLODE (c::cs) = STRING c (IMPLODE cs))
End

Definition EXPLODE_def[simp]:
  (EXPLODE "" = []) /\
  (EXPLODE (STRING c s) = c :: EXPLODE s)
End

Theorem IMPLODE_EXPLODE_I[compute]:
  (EXPLODE s = s) /\ (IMPLODE s = s)
Proof
  Induct_on `s` THEN SRW_TAC [][]
QED

Theorem IMPLODE_EXPLODE[simp]:
    IMPLODE (EXPLODE s) = s
Proof
  Induct_on `s` THEN SRW_TAC [][]
QED

Theorem EXPLODE_IMPLODE[simp]:
    EXPLODE (IMPLODE cs) = cs
Proof
  Induct_on `cs` THEN SRW_TAC [][]
QED

Theorem EXPLODE_ONTO: !cs. ?s. cs = EXPLODE s
Proof METIS_TAC [EXPLODE_IMPLODE, IMPLODE_EXPLODE]
QED
Theorem IMPLODE_ONTO: !s. ?cs. s = IMPLODE cs
Proof METIS_TAC [EXPLODE_IMPLODE, IMPLODE_EXPLODE]
QED
Theorem EXPLODE_11[simp]: (EXPLODE s1 = EXPLODE s2) = (s1 = s2)
Proof METIS_TAC [EXPLODE_IMPLODE, IMPLODE_EXPLODE]
QED
Theorem IMPLODE_11[simp]: (IMPLODE cs1 = IMPLODE cs2) = (cs1 = cs2)
Proof METIS_TAC [EXPLODE_IMPLODE, IMPLODE_EXPLODE]
QED


Theorem TOKENS_APPEND:
  !P l1 x l2.
    P x ==>
      (TOKENS P (l1 ++ x::l2) = TOKENS P l1 ++ TOKENS P l2)
Proof
  ho_match_mp_tac TOKENS_ind
  \\ rw[TOKENS_def] >- (fs[SPLITP])
  \\ pairarg_tac  \\ fs[]
  \\ pairarg_tac  \\ fs[]
  \\ fs[NULL_EQ, SPLITP]
  \\ Cases_on `P h` \\ full_simp_tac bool_ss []
  \\ rw[]
  \\ fs[TL]
  \\ Cases_on `EXISTS P t` \\ rw[SPLITP_APPEND, SPLITP]
  \\ fs[NOT_EXISTS] \\ imp_res_tac (GSYM SPLITP_NIL_SND_EVERY) \\ rw[]
  \\ fs[NOT_EXISTS] \\ imp_res_tac (GSYM SPLITP_NIL_SND_EVERY) \\ rw[]
QED

Theorem TOKENS_NIL:
  !ls. (TOKENS f ls = []) <=> EVERY f ls
Proof
  Induct \\ rw[TOKENS_def]  \\ pairarg_tac
  \\ fs[NULL_EQ, SPLITP]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs[] \\ rw[]
QED

Theorem TOKENS_FRONT:
  ~NULL ls /\ P (LAST ls) ==>
    (TOKENS P (FRONT ls) = TOKENS P ls)
Proof
  Induct_on`ls` \\ rw[]
  \\ Cases_on`ls` \\ fs[]
  >- rw[TOKENS_def,SPLITP]
  \\ rw[TOKENS_def]
  \\ pairarg_tac
  \\ simp[Once SPLITP]
  \\ CASE_TAC \\ fs[NULL_EQ]
  >- (
    imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP
    \\ rfs[] )
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`l` \\ fs[] \\ rpt BasicProvers.VAR_EQ_TAC
  \\ imp_res_tac SPLITP_IMP
  \\ CASE_TAC \\ fs[]
  \\ qmatch_goalsub_rename_tac`SPLITP P (x::xs)`
  \\ `?y ys. x::xs = SNOC y ys` by metis_tac[SNOC_CASES,list_distinct]
  \\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC] \\ rpt BasicProvers.VAR_EQ_TAC
  \\ qmatch_goalsub_rename_tac`SPLITP P (SNOC y (w ++ z))`
  \\ Cases_on`NULL z` \\ fs[NULL_EQ, SNOC_APPEND]
  >- (
    simp[SPLITP_APPEND]
    \\ full_simp_tac std_ss [GSYM NOT_EXISTS]
    \\ simp[SPLITP,TOKENS_def] )
  \\ Cases_on`z` \\ fs[]
  \\ simp[SPLITP_APPEND]
  \\ full_simp_tac std_ss [GSYM NOT_EXISTS]
  \\ simp[SPLITP,TOKENS_def]
  \\ simp[TOKENS_APPEND,TOKENS_NIL]
QED

(*---------------------------------------------------------------------------
    Definability of prim. rec. functions over strings.
 ---------------------------------------------------------------------------*)

Theorem alt_string_Axiom[local]:
  !b g. ?f.  (f (IMPLODE []) = b) /\
       (!c t. f (IMPLODE (c::t)) = g c t (f (IMPLODE t)))
Proof
REPEAT GEN_TAC
  THEN STRIP_ASSUME_TAC
     (prove_rec_fn_exists listTheory.list_Axiom
        ``(list_rec (b:'a) f ([]:char list) = b) /\
          (list_rec b f (h::t) = f h t (list_rec b f t))``)
   THEN Q.EXISTS_TAC`list_rec b g o EXPLODE`
   THEN RW_TAC bool_ss [combinTheory.o_DEF,list_case_def,EXPLODE_IMPLODE]
QED


Theorem STRING_ACYCLIC:
  !s c. ~(STRING c s = s) /\ ~(s = STRING c s)
Proof
 Induct THEN SRW_TAC [][]
QED

(*---------------------------------------------------------------------------
      Size of a string.
 ---------------------------------------------------------------------------*)

Overload STRLEN[inferior] = “LENGTH : string -> num”
val STRLEN_DEF = listTheory.LENGTH

Definition EXTRACT_def:
  (EXTRACT (s,i,NONE) = SUBSTRING(s,i,STRLEN s - i)) /\
  (EXTRACT (s,i,SOME n) = SUBSTRING(s,i,n))
End

Theorem STRLEN_EXPLODE_THM:
    STRLEN s = LENGTH (EXPLODE s)
Proof
  SRW_TAC [][IMPLODE_EXPLODE_I]
QED

(*---------------------------------------------------------------------------*)
(* Destruct a string. This will be used to re-phrase the HOL development     *)
(* with an ML definition of DEST_STRING in terms of the Basis String struct. *)
(*---------------------------------------------------------------------------*)

Definition DEST_STRING_def[simp]:
   (DEST_STRING "" = NONE) /\
   (DEST_STRING (STRING c rst) = SOME(c,rst))
End

Theorem DEST_STRING_LEMS:
  !s. ((DEST_STRING s = NONE) = (s = "")) /\
      ((DEST_STRING s = SOME(c,t)) = (s = STRING c t))
Proof
 Cases THEN SRW_TAC [][]
QED

Theorem EXPLODE_EQNS = EXPLODE_def
Theorem IMPLODE_EQNS = IMPLODE_def

(* ----------------------------------------------------------------------
    More rewrites for IMPLODE and EXPLODE
   ---------------------------------------------------------------------- *)

Theorem IMPLODE_EQ_EMPTYSTRING[simp]:
   ((IMPLODE l = "") = (l = [])) /\
   (("" = IMPLODE l) = (l = []))
Proof
  Cases_on `l` THEN SRW_TAC [][]
QED

Theorem EXPLODE_EQ_NIL[simp]:
   ((EXPLODE s = []) = (s = "")) /\
   (([] = EXPLODE s) = (s = ""))
Proof
  Cases_on `s` THEN SRW_TAC [][]
QED

Theorem EXPLODE_EQ_THM:
  !s h t. ((h::t = EXPLODE s) = (s = STRING h (IMPLODE t))) /\
          ((EXPLODE s = h::t) = (s = STRING h (IMPLODE t)))
Proof
  Cases THEN SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][]
QED

Theorem IMPLODE_EQ_THM:
  !c s l. ((STRING c s = IMPLODE l) = (l = c::EXPLODE s)) /\
          ((IMPLODE l = STRING c s) = (l = c::EXPLODE s))
Proof
 Cases_on `l` THEN SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][]
QED

(*---------------------------------------------------------------------------*)
(* ML-style recursion equations for EXPLODE and IMPLODE                      *)
(*---------------------------------------------------------------------------*)

Theorem EXPLODE_DEST_STRING:
  !s. EXPLODE s = case DEST_STRING s
                   of NONE => []
                    | SOME(c,t) => c::EXPLODE t
Proof
 Cases THEN SRW_TAC [][]
QED

Theorem IMPLODE_STRING:
  !clist.IMPLODE clist = FOLDR STRING "" clist
Proof
 Induct THEN SRW_TAC [][]
QED

(*---------------------------------------------------------------------------*)
(* Main fact about STRLEN                                                    *)
(*---------------------------------------------------------------------------*)

val stringinst = INST_TYPE [alpha |-> ``:char``]

Theorem STRLEN_EQ_0 = stringinst LENGTH_NIL
Theorem STRLEN_THM = stringinst LENGTH
Theorem STRLEN_DEF = STRLEN_THM

(*---------------------------------------------------------------------------
                      String concatenation
 ---------------------------------------------------------------------------*)

Overload STRCAT[inferior] = “list$APPEND : string -> string -> string”


Theorem STRCAT_def = stringinst APPEND

Theorem STRCAT:
    STRCAT s1 s2 = STRCAT s1 s2
Proof
  SRW_TAC [][]
QED

Theorem STRCAT_EQNS:
  (STRCAT "" s = s) /\
  (STRCAT s "" = s) /\
  (STRCAT (STRING c s1) s2 = STRING c (STRCAT s1 s2))
Proof
 SRW_TAC [][STRCAT_def]
QED

Theorem STRCAT_ASSOC = stringinst APPEND_ASSOC

Theorem STRCAT_11 = stringinst APPEND_11

Theorem STRCAT_ACYCLIC:
  !s s1. ((s = STRCAT s s1) = (s1 = "")) /\
         ((s = STRCAT s1 s) = (s1 = ""))
Proof
 PROVE_TAC [STRCAT_EQNS,STRCAT_11]
QED

Theorem STRCAT_EXPLODE:
  !s1 s2. STRCAT s1 s2 = FOLDR STRING s2 (EXPLODE s1)
Proof
  Induct THEN SRW_TAC [][]
QED

Theorem STRCAT_EQ_EMPTY =
                               CONJUNCT2 (stringinst APPEND_eq_NIL)
(*---------------------------------------------------------------------------
     String length and concatenation
 ---------------------------------------------------------------------------*)

Theorem STRLEN_CAT = stringinst LENGTH_APPEND

(*---------------------------------------------------------------------------
       Is one string a prefix of another?
 ---------------------------------------------------------------------------*)

Theorem isPREFIX_DEF:
    !s1 s2.
       isPREFIX s1 s2 =
       case (DEST_STRING s1, DEST_STRING s2)
        of (NONE, _) => T
         | (SOME __, NONE) => F
         | (SOME(c1,t1),SOME(c2,t2)) => (c1=c2) /\ isPREFIX t1 t2
Proof
  Cases_on `s1` THEN Cases_on `s2` THEN SRW_TAC [][]
QED

Theorem isPREFIX_IND:
  !P. (!s1 s2.
         (!c t1 t2.
           (DEST_STRING s1 = SOME (c,t1)) /\
           (DEST_STRING s2 = SOME (c,t2)) ==> P t1 t2) ==> P s1 s2)
       ==> !v v1. P v v1
Proof
 GEN_TAC THEN STRIP_TAC THEN Induct THEN SRW_TAC [][]
QED

Theorem isPREFIX_STRCAT:
  !s1 s2. isPREFIX s1 s2 = ?s3. s2 = STRCAT s1 s3
Proof
 Induct THEN SRW_TAC [][] THEN Cases_on `s2` THEN SRW_TAC [][] THEN
 PROVE_TAC []
QED

(*---------------------------------------------------------------------------
       Orderings
 ---------------------------------------------------------------------------*)

Definition string_lt_def:
  (string_lt s EMPTYSTRING <=> F) /\
  (string_lt EMPTYSTRING (STRING c s) <=> T) /\
  (string_lt (STRING c1 s1) (STRING c2 s2) <=>
     c1 < c2 \/ (c1 = c2) /\ string_lt s1 s2)
End

Definition string_le_def:   string_le s1 s2 <=> (s1 = s2) \/ string_lt s1 s2
End
Definition string_gt_def:   string_gt s1 s2 <=> string_lt s2 s1
End
Definition string_ge_def:   string_ge s1 s2 <=> string_le s2 s1
End

Overload "<"[inferior]  = “string_lt”
Overload ">"[inferior]  = “string_gt”
Overload "<="[inferior] = “string_le”
Overload ">="[inferior] = “string_ge”

Theorem string_lt_nonrefl:
    !s:string. ~(s < s)
Proof
  Induct THEN ASM_SIMP_TAC std_ss [string_lt_def,char_lt_def]
QED

Theorem string_lt_antisym:
    !s t:string. ~(s < t /\ t < s)
Proof
  SIMP_TAC std_ss []
  THEN Induct THEN Cases_on `t` THEN SIMP_TAC std_ss [string_lt_def,char_lt_def]
  THEN REPEAT STRIP_TAC THEN Cases_on `h = h'` THEN ASM_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [GSYM ORD_11] THEN DECIDE_TAC
QED

Theorem string_lt_cases:
    !s t:string. (s = t) \/ s < t \/ t < s
Proof
  Induct THEN Cases_on `t` THEN SIMP_TAC std_ss [string_lt_def,char_lt_def]
  THEN SIMP_TAC std_ss [CONS_11,GSYM ORD_11] THEN STRIP_TAC
  THEN Cases_on `ORD h = ORD h'` THEN ASM_SIMP_TAC std_ss [] THEN DECIDE_TAC
QED

Theorem string_lt_trans:
    !s1 s2 s3:string. s1 < s2 /\ s2 < s3 ==> s1 < s3
Proof
  Induct THEN Cases_on `s2` THEN Cases_on `s3`
  THEN SIMP_TAC std_ss [string_lt_def,char_lt_def,GSYM ORD_11] THEN STRIP_TAC
  THEN Cases_on `ORD h'' < ORD h'` THEN ASM_SIMP_TAC std_ss [IMP_CONJ_THM]
  THEN STRIP_TAC THEN1 (REPEAT STRIP_TAC THEN DECIDE_TAC)
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC arithmeticTheory.LESS_TRANS
  THEN METIS_TAC []
QED

val string_lt_ind = theorem"string_lt_ind";

Theorem string_lt_LLEX:
  string_lt = LLEX char_lt
Proof
  simp[FUN_EQ_THM]
  \\ recInduct string_lt_ind
  \\ rw[string_lt_def]
QED

Theorem not_WF_string_lt:
  ~WF string_lt
Proof
  rw[string_lt_LLEX]
  \\ match_mp_tac LLEX_not_WF
  \\ qexists_tac`CHR 0`
  \\ qexists_tac`CHR 1`
  \\ simp[char_lt_def]
QED

Theorem INFINITE_STR_UNIV :
    INFINITE univ(:string)
Proof
  SRW_TAC [][INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][]
QED

(*---------------------------------------------------------------------------
    Exportation
 ---------------------------------------------------------------------------*)

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles ("help" ^^ "thms")
end;
