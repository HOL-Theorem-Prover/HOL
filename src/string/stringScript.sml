(* =====================================================================*)
(* FILE		: stringScript.sml				        *)
(* DESCRIPTION  : A theory of 8-bit characters and strings built        *)
(*                from them.                                            *)
(*                                                                      *)
(* AUTHOR	: (c) Konrad Slind, University of Cambridge, 2001       *)
(* =====================================================================*)

(* interactive use:
  app load ["numLib", "listTheory", "listSyntax",
            "BasicProvers", "Q", "SingleStep"];
  open numLib numSyntax BasicProvers listTheory listSyntax SingleStep;
*)

open HolKernel boolLib numLib numSyntax BasicProvers SingleStep listTheory;

infix THEN ; infixr -->;

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "string";

(* ---------------------------------------------------------------------*)
(* Characters are represented by the natural numbers <= 255.            *)
(* ---------------------------------------------------------------------*)

val is_char =
 let val n = mk_var("n",num)
     val topnum = mk_numeral (Arbnum.fromInt 256)
 in mk_abs(n,mk_less(n,topnum))
 end;

val CHAR_EXISTS = Q.prove (`?n. ^is_char n`, Q.EXISTS_TAC `0` THEN REDUCE_TAC);

val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS);

val CHAR_TYPE_FACTS =
  define_new_type_bijections
      {ABS="CHR", REP="ORD",name="char_BIJ", tyax=CHAR_TYPE};

val CHR_ORD  = save_thm("CHR_ORD", CONJUNCT1 CHAR_TYPE_FACTS);
val ORD_CHR  = save_thm("ORD_CHR",BETA_RULE (CONJUNCT2 CHAR_TYPE_FACTS));

val ORD_11   = save_thm("ORD_11",prove_rep_fn_one_one CHAR_TYPE_FACTS)
val CHR_11   = save_thm("CHR_11",
                         BETA_RULE (prove_abs_fn_one_one CHAR_TYPE_FACTS));
val ORD_ONTO = save_thm("ORD_ONTO",
                         BETA_RULE (prove_rep_fn_onto CHAR_TYPE_FACTS));
val CHR_ONTO = save_thm("CHR_ONTO",
                         BETA_RULE (prove_abs_fn_onto CHAR_TYPE_FACTS));

val ORD_BOUND = Q.store_thm
("ORD_BOUND",
 `!c. ORD c < 256`,
 PROVE_TAC [ORD_ONTO]);

(*---------------------------------------------------------------------------
    In our development, CHR is not a constructor. Is that really
    important? We can at least prove the following theorem about
    equality of chars.
 ---------------------------------------------------------------------------*)

val CHAR_EQ_THM = Q.store_thm
("CHAR_EQ_THM",
 `!c1 c2. (c1 = c2) = (ORD c1 = ORD c2)`,
 REPEAT GEN_TAC
   THEN EQ_TAC
   THEN RW_TAC bool_ss [ORD_11]);


val CHAR_INDUCT_THM = Q.store_thm
("CHAR_INDUCT_THM",
 `!P. (!n. n < 256 ==> P (CHR n)) ==> !c. P c`,
REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `c` CHR_ONTO)
  THEN RW_TAC bool_ss []);


(*---------------------------------------------------------------------------
      Strings are represented as lists of characters. This gives us
      EXPLODE and IMPLODE as the functions mapping into, and from, the
      representation.
 ---------------------------------------------------------------------------*)

val is_string =
 let val char_ty = mk_type("char",[])
 in mk_abs(mk_var("x",listSyntax.mk_list_type char_ty),T)
 end;

val STRING_EXISTS = Q.prove
(`?l. ^is_string l`, Q.EXISTS_TAC `[]` THEN BETA_TAC);

val STRING_TYPE = new_type_definition("string", STRING_EXISTS);

val STRING_TYPE_FACTS =
  define_new_type_bijections
      {ABS="IMPLODE", REP="EXPLODE",name="string_bij", tyax=STRING_TYPE};

val IMPLODE_EXPLODE =
  save_thm("IMPLODE_EXPLODE", CONJUNCT1 STRING_TYPE_FACTS);

val EXPLODE_IMPLODE =
  save_thm ("EXPLODE_IMPLODE",
    GEN_ALL (EQ_MP (SPEC_ALL(BETA_RULE (CONJUNCT2 STRING_TYPE_FACTS))) TRUTH));

val EXPLODE_11 = save_thm("EXPLODE_11",prove_rep_fn_one_one STRING_TYPE_FACTS)

val EXPLODE_ONTO =
  save_thm("EXPLODE_ONTO",
    GEN_ALL
     (EQ_MP(SPEC_ALL(BETA_RULE (prove_rep_fn_onto STRING_TYPE_FACTS))) TRUTH));

val IMPLODE_11 =
  save_thm("IMPLODE_11",
    REWRITE_RULE [] (BETA_RULE (prove_abs_fn_one_one STRING_TYPE_FACTS)));

val IMPLODE_ONTO =
  save_thm("IMPLODE_ONTO",
       REWRITE_RULE [] (BETA_RULE (prove_abs_fn_onto STRING_TYPE_FACTS)));


(*---------------------------------------------------------------------------
    Definability of prim. rec. functions over strings.
 ---------------------------------------------------------------------------*)

val alt_string_Axiom = Q.store_thm
("alt_string_Axiom",
 `!b g. ?f.  (f (IMPLODE []) = b) /\
       (!c t. f (IMPLODE (c::t)) = g c t (f (IMPLODE t)))`,
REPEAT GEN_TAC
  THEN STRIP_ASSUME_TAC
     (prove_rec_fn_exists listTheory.list_Axiom
       (Term `(list_rec (b:'a) f ([]:char list) = b) /\
              (list_rec b f (h::t) = f h t (list_rec b f t))`))
   THEN Q.EXISTS_TAC`list_rec b g o EXPLODE`
   THEN RW_TAC bool_ss [combinTheory.o_DEF,list_case_def,EXPLODE_IMPLODE]);


(*---------------------------------------------------------------------------
    Case expression.
 ---------------------------------------------------------------------------*)

val ALT_STRING_CASE_DEF =
new_recursive_definition
 {name="ALT_STRING_CASE_DEF",
  def = Term `(alt_string_case f (IMPLODE [])     = f []) /\
              (alt_string_case f (IMPLODE (c::t)) = f (c::t))`,
  rec_axiom = alt_string_Axiom};

val ALT_STRING_CASE_THM  = Q.store_thm
("ALT_STRING_CASE_THM",
 `!l f. alt_string_case f (IMPLODE l) = f l`,
 GEN_TAC
   THEN STRUCT_CASES_TAC (Q.ISPEC `l:char list` listTheory.list_CASES)
   THEN RW_TAC bool_ss [ALT_STRING_CASE_DEF]);

(*---------------------------------------------------------------------------
    Standard constructors for strings, defined using IMPLODE and EXPLODE.
    The parser and prettyprinter are set up to handle string literals,
    e.g., `"foo"` or `""`.
 ---------------------------------------------------------------------------*)

val EMPTYSTRING_DEF =
 Q.new_definition("EMPTYSTRING_DEF", `EMPTYSTRING:string = IMPLODE []`);

val STRING_DEF =
 Q.new_definition("STRING_DEF", `STRING c str = IMPLODE (c::EXPLODE str)`);

(*---------------------------------------------------------------------------
     One-one and distinctness
 ---------------------------------------------------------------------------*)

val STRING_11 = Q.store_thm
("STRING_11",
 `!c1 c2 s1 s2. (STRING c1 s1 = STRING c2 s2) = (c1=c2) /\ (s1=s2)`,
 RW_TAC bool_ss [STRING_DEF,IMPLODE_11,EXPLODE_11]);

val STRING_DISTINCT = Q.store_thm
("STRING_DISTINCT",
 `(!c s. ~("" = STRING c s)) /\
  (!c s. ~(STRING c s = ""))`,
 RW_TAC bool_ss [STRING_DEF,EMPTYSTRING_DEF,IMPLODE_11,NOT_NIL_CONS]);

(*---------------------------------------------------------------------------
   Prim. rec. phrased in terms of the standard constructors.
 ---------------------------------------------------------------------------*)

val string_Axiom = Q.store_thm
("string_Axiom",
 `!b g. ?f.  (f "" = b) /\
       (!c t. f (STRING c t) = g c t (f t))`,
 REPEAT GEN_TAC
   THEN STRIP_ASSUME_TAC (BETA_RULE
         (Q.SPECL [`b`, `\c l a. g c (IMPLODE l) a`] alt_string_Axiom))
   THEN PROVE_TAC [EMPTYSTRING_DEF, STRING_DEF, IMPLODE_EXPLODE]);


(*---------------------------------------------------------------------------
     Induction for strings.
 ---------------------------------------------------------------------------*)

val ALT_STRING_INDUCT_THM = Q.store_thm
("ALT_STRING_INDUCT_THM",
 `!P. P (IMPLODE []) /\
     (!c cl. P (IMPLODE cl) ==> P (IMPLODE (c::cl))) ==> !s. P s`,
 RW_TAC bool_ss []
   THEN CHOOSE_THEN SUBST_ALL_TAC (Q.SPEC `s` IMPLODE_ONTO)
   THEN Induct_on `r` THEN PROVE_TAC []);

val STRING_INDUCT_THM = Q.store_thm
("STRING_INDUCT_THM",
 `!P. P "" /\ (!c s. P s ==> P (STRING c s)) ==> !s. P s`,
 REWRITE_TAC [EMPTYSTRING_DEF, STRING_DEF]
   THEN GEN_TAC THEN STRIP_TAC
   THEN HO_MATCH_MP_TAC ALT_STRING_INDUCT_THM
   THEN PROVE_TAC [EXPLODE_IMPLODE]);


val STRING_ACYCLIC = Q.store_thm
("STRING_ACYCLIC",
 `!s c. ~(STRING c s = s) /\ ~(s = STRING c s)`,
 HO_MATCH_MP_TAC STRING_INDUCT_THM 
   THEN RW_TAC bool_ss [STRING_11,STRING_DISTINCT]);


(*---------------------------------------------------------------------------
     Nchotomy for strings.
 ---------------------------------------------------------------------------*)

val ALT_STRING_CASES = Q.store_thm
("ALT_STRING_CASES",
 `!s. (s = IMPLODE []) \/ (?c cl. s = IMPLODE (c::cl))`,
 HO_MATCH_MP_TAC ALT_STRING_INDUCT_THM THEN PROVE_TAC[]);

val STRING_CASES = Q.store_thm
("STRING_CASES",
 `!s. (s = "") \/ (?c str. s = STRING c str)`,
 HO_MATCH_MP_TAC STRING_INDUCT_THM THEN PROVE_TAC[]);


(*---------------------------------------------------------------------------
     Case expressions over strings.
 ---------------------------------------------------------------------------*)

val STRING_CASE_DEF =
new_recursive_definition
 {name="STRING_CASE_DEF",
  def = Term `(string_case b f ""  = b) /\
              (string_case b f (STRING c s) = f c s)`,
  rec_axiom = string_Axiom};


val STRING_CASE_CONG =
 save_thm("STRING_CASE_CONG", case_cong_thm STRING_CASES STRING_CASE_DEF);

(*---------------------------------------------------------------------------
     Recursion equations for EXPLODE and IMPLODE
 ---------------------------------------------------------------------------*)

val EXPLODE_EQNS = Q.store_thm
("EXPLODE_EQNS",
 `(EXPLODE "" = []) /\
  !c s. EXPLODE (STRING c s) = c::EXPLODE s`,
 REWRITE_TAC [EMPTYSTRING_DEF,EXPLODE_IMPLODE,IMPLODE_EXPLODE,STRING_DEF]);

val IMPLODE_EQNS = Q.store_thm
("IMPLODE_EQNS",
 `(IMPLODE [] = "") /\
  !c s. IMPLODE (c::t) = STRING c (IMPLODE t)`,
 REWRITE_TAC [EMPTYSTRING_DEF,EXPLODE_IMPLODE,IMPLODE_EXPLODE,STRING_DEF]);

(*---------------------------------------------------------------------------
      Size of a string.
 ---------------------------------------------------------------------------*)

val STRLEN_DEF = new_recursive_definition
   {def = Term`(STRLEN "" = 0) /\
               (STRLEN (STRING c s) = 1 + STRLEN s)`,
    name="STRLEN_DEF", rec_axiom = string_Axiom};

val STRLEN_THM = Q.store_thm
("STRLEN_THM",
 `!s. STRLEN s = LENGTH (EXPLODE s)`,
 HO_MATCH_MP_TAC STRING_INDUCT_THM
  THEN RW_TAC bool_ss [STRLEN_DEF,EXPLODE_EQNS,LENGTH,
                       ONCE_REWRITE_RULE [arithmeticTheory.ADD_SYM]
                         arithmeticTheory.ADD1]);

(*---------------------------------------------------------------------------
       String concatenation
 ---------------------------------------------------------------------------*)

val STRCAT = 
  new_definition
   ("STRCAT", 
    Term `STRCAT s1 s2 = IMPLODE(APPEND (EXPLODE s1) (EXPLODE s2))`);

val STRCAT_EQNS = Q.store_thm
("STRCAT_EQNS",
 `(STRCAT "" s = s) /\
  (STRCAT s "" = s) /\
  (STRCAT (STRING c s1) s2 = STRING c (STRCAT s1 s2))`,
 RW_TAC bool_ss [STRCAT,APPEND,APPEND_NIL,EXPLODE_EQNS,
                 IMPLODE_EQNS,IMPLODE_EXPLODE]);

val STRCAT_ASSOC = Q.store_thm 
("STRCAT_ASSOC",
 `!s1 s2 s3. STRCAT s1 (STRCAT s2 s3) = STRCAT (STRCAT s1 s2) s3`,
 RW_TAC bool_ss [STRCAT,IMPLODE_11,EXPLODE_IMPLODE,APPEND_ASSOC]);

val STRCAT_11 = Q.store_thm
("STRCAT_11",
 `!s1 s2 s3. ((STRCAT s1 s2 = STRCAT s1 s3) = (s2=s3)) /\
             ((STRCAT s1 s3 = STRCAT s2 s3) = (s1=s2))`,
 RW_TAC bool_ss [STRCAT,IMPLODE_11,EXPLODE_11,listTheory.APPEND_11]);

val STRCAT_ACYCLIC = Q.store_thm
("STRCAT_ACYCLIC",
 `!s s1. ((s = STRCAT s s1) = (s1 = "")) /\
         ((s = STRCAT s1 s) = (s1 = ""))`,
 PROVE_TAC [STRCAT_EQNS,STRCAT_11]);


(*---------------------------------------------------------------------------
     String length and concatenation
 ---------------------------------------------------------------------------*)

val STRLEN_CAT = Q.store_thm 
("STRLEN_CAT",
 `!x y. STRLEN (STRCAT x y) = (STRLEN x + STRLEN y)`,
 REWRITE_TAC[STRCAT,STRLEN_THM,LENGTH_APPEND,EXPLODE_IMPLODE]);


(*---------------------------------------------------------------------------
       Is one string a prefix of another?
 ---------------------------------------------------------------------------*)

val isPREFIX =
 Q.new_definition
   ("isPREFIX", 
    `isPREFIX s1 s2 = ?s3. s2 = STRCAT s1 s3`);


(*---------------------------------------------------------------------------
      Raises unary list operators to string operators.
 ---------------------------------------------------------------------------*)
(*
val BY_LISTOP_DEF = Q.new_definition
 ("BY_LIST_OP",
  `BY_LIST_OP f s = IMPLODE (f (EXPLODE s))`);
*)

(*---------------------------------------------------------------------------
    Exportation
 ---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "val _ = TypeBase.write";
   S "  (TypeBasePure.mk_tyinfo";
   S "     {ax=TypeBasePure.ORIG string_Axiom,";
   S "      case_def=STRING_CASE_DEF,";
   S "      case_cong=STRING_CASE_CONG,";
   S "      induction=TypeBasePure.ORIG STRING_INDUCT_THM,";
   S "      nchotomy=STRING_CASES,";
   S "      size=SOME(Parse.Term`STRLEN`,TypeBasePure.ORIG STRLEN_DEF),";
   S "      one_one=SOME STRING_11,";
   S "      distinct=SOME (CONJUNCT1 STRING_DISTINCT)});";
   S " ";
   S "val _ = computeLib.add_funs";
   S "        [STRING_CASE_DEF,STRLEN_DEF,EXPLODE_EQNS,IMPLODE_EQNS];"
 end)};

val _ = export_theory();
