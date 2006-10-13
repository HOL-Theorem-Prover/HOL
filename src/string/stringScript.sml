(* =====================================================================*)
(* FILE		: stringScript.sml				        *)
(* DESCRIPTION  : A theory of 8-bit characters and strings built        *)
(*                from them.                                            *)
(*                                                                      *)
(* AUTHOR	: Konrad Slind, University of Cambridge, 2001           *)
(* =====================================================================*)

(* interactive use:
  app load ["numLib", "listTheory", "listSyntax",
            "BasicProvers", "Q", "SingleStep", "metisLib"];
*)

open HolKernel boolLib
     numLib numSyntax BasicProvers SingleStep listTheory bossLib metisLib;

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
    (define_new_type_bijections
       {ABS="CHR", REP="ORD",name="char_BIJ", tyax=CHAR_TYPE});

val ORD_11   = save_thm("ORD_11",prove_rep_fn_one_one CHAR_TYPE_FACTS)
val CHR_11   = save_thm("CHR_11",
                         BETA_RULE (prove_abs_fn_one_one CHAR_TYPE_FACTS));
val _ = export_rewrites ["CHR_11"]
val ORD_ONTO = save_thm("ORD_ONTO",
                         BETA_RULE (prove_rep_fn_onto CHAR_TYPE_FACTS));
val CHR_ONTO = save_thm("CHR_ONTO",
                         BETA_RULE (prove_abs_fn_onto CHAR_TYPE_FACTS));

val CHR_ORD  = save_thm("CHR_ORD", CONJUNCT1 CHAR_TYPE_FACTS);
val ORD_CHR  = save_thm("ORD_CHR",BETA_RULE (CONJUNCT2 CHAR_TYPE_FACTS));

val ORD_CHR_RWT = Q.store_thm
("ORD_CHR_RWT",
 `!r. r < 256 ==> (ORD (CHR r) = r)`,
 PROVE_TAC [ORD_CHR]);

val ORD_CHR_COMPUTE = Q.store_thm
("ORD_CHR_COMPUTE",
 `!r. ORD (CHR r) = if r < 256 then r else ORD (CHR r)`,
 PROVE_TAC [ORD_CHR_RWT]);

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

val EXPLODE_ONTO =
  save_thm("EXPLODE_ONTO",
    GEN_ALL
     (EQ_MP(SPEC_ALL(BETA_RULE (prove_rep_fn_onto STRING_TYPE_FACTS))) TRUTH));

val IMPLODE_ONTO =
  save_thm("IMPLODE_ONTO",
       REWRITE_RULE [] (BETA_RULE (prove_abs_fn_onto STRING_TYPE_FACTS)));

val EXPLODE_11 = save_thm("EXPLODE_11",prove_rep_fn_one_one STRING_TYPE_FACTS)

val IMPLODE_11 =
  save_thm("IMPLODE_11",
    REWRITE_RULE [] (BETA_RULE (prove_abs_fn_one_one STRING_TYPE_FACTS)));

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
     One-one and distinctness of the constructors
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
    Definability of prim. rec. functions over strings.
 ---------------------------------------------------------------------------*)

val alt_string_Axiom = Q.prove
(`!b g. ?f.  (f (IMPLODE []) = b) /\
       (!c t. f (IMPLODE (c::t)) = g c t (f (IMPLODE t)))`,
REPEAT GEN_TAC
  THEN STRIP_ASSUME_TAC
     (prove_rec_fn_exists listTheory.list_Axiom
        ``(list_rec (b:'a) f ([]:char list) = b) /\
          (list_rec b f (h::t) = f h t (list_rec b f t))``)
   THEN Q.EXISTS_TAC`list_rec b g o EXPLODE`
   THEN RW_TAC bool_ss [combinTheory.o_DEF,list_case_def,EXPLODE_IMPLODE]);


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

val ALT_STRING_INDUCT_THM = Q.prove
(`!P. P (IMPLODE []) /\
     (!c cl. P (IMPLODE cl) ==> P (IMPLODE (c::cl))) ==> !s. P s`,
 RW_TAC bool_ss []
   THEN CHOOSE_THEN SUBST_ALL_TAC (Q.SPEC `s` IMPLODE_ONTO)
   THEN Induct_on `r` THEN PROVE_TAC []);

val STRING_INDUCT_THM = Q.store_thm
("STRING_INDUCT_THM",
 `!P. P "" /\ (!s. P s ==> !c. P (STRING c s)) ==> !s. P s`,
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

(*
val ALT_STRING_CASES = Q.prove
(`!s. (s = IMPLODE []) \/ (?c cl. s = IMPLODE (c::cl))`,
 HO_MATCH_MP_TAC ALT_STRING_INDUCT_THM THEN PROVE_TAC[]);
*)

val STRING_CASES = Q.store_thm
("STRING_CASES",
 `!s. (s = "") \/ (?c str. s = STRING c str)`,
 HO_MATCH_MP_TAC STRING_INDUCT_THM THEN PROVE_TAC[]);


(*---------------------------------------------------------------------------
     Case expressions over strings.
 ---------------------------------------------------------------------------*)

val STRING_CASE_DEF = new_recursive_definition
 {name="STRING_CASE_DEF",
  def = ``(string_case b f ""  = b) /\
          (string_case b f (STRING c s) = f c s)``,
  rec_axiom = string_Axiom};


val STRING_CASE_CONG = save_thm
("STRING_CASE_CONG",
 case_cong_thm STRING_CASES STRING_CASE_DEF);


(*---------------------------------------------------------------------------
      Size of a string.
 ---------------------------------------------------------------------------*)

val STRLEN_DEF = new_recursive_definition
   {def = ``(STRLEN "" = 0) /\
            (STRLEN (STRING c s) = 1 + STRLEN s)``,
    name = "STRLEN_DEF",
    rec_axiom = string_Axiom};


val _ = TypeBase.write
     [TypeBasePure.mk_datatype_info
       {ax=TypeBasePure.ORIG string_Axiom,
        case_def=STRING_CASE_DEF,
        case_cong=STRING_CASE_CONG,
        induction=TypeBasePure.ORIG STRING_INDUCT_THM,
        nchotomy=STRING_CASES,
        size=SOME(``STRLEN``,TypeBasePure.ORIG STRLEN_DEF),
        encode=NONE, lift=NONE,
        one_one=SOME STRING_11,
        fields = [],
        accessors = [],
        updates = [],
       distinct=SOME (CONJUNCT1 STRING_DISTINCT)}];

(*---------------------------------------------------------------------------*)
(* Destruct a string. This will be used to re-phrase the HOL development     *)
(* with an ML definition of DEST_STRING in terms of the Basis String struct. *)
(*---------------------------------------------------------------------------*)

val DEST_STRING =
 new_recursive_definition
   {name = "DEST_STRING",
    def = ``(DEST_STRING "" = NONE) /\
            (DEST_STRING (STRING c rst) = SOME(c,rst))``,
    rec_axiom = string_Axiom};


val DEST_STRING_LEMS = Q.store_thm
("DEST_STRING_LEMS",
 `!s. ((DEST_STRING s = NONE) = (s = "")) /\
      ((DEST_STRING s = SOME(c,t)) = (s = STRING c t))`,
 GEN_TAC
   THEN STRIP_ASSUME_TAC (SPEC_ALL STRING_CASES)
   THEN RW_TAC list_ss [DEST_STRING]);



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

(* ----------------------------------------------------------------------
    More rewrites for IMPLODE and EXPLODE
   ---------------------------------------------------------------------- *)

val IMPLODE_EQ_EMPTYSTRING = Q.store_thm(
  "IMPLODE_EQ_EMPTYSTRING",
  `((IMPLODE l = "") = (l = [])) /\
   (("" = IMPLODE l) = (l = []))`,
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  REWRITE_TAC [] THEN
  RW_TAC bool_ss [EQ_IMP_THM, IMPLODE_EQNS, IMPLODE_EXPLODE] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `EXPLODE`) THEN
  RW_TAC bool_ss [EXPLODE_EQNS, EXPLODE_IMPLODE]);

val EXPLODE_EQ_NIL = Q.store_thm(
  "EXPLODE_EQ_NIL",
  `((EXPLODE s = []) = (s = "")) /\
   (([] = EXPLODE s) = (s = ""))`,
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  REWRITE_TAC [] THEN
  RW_TAC bool_ss [EQ_IMP_THM, EXPLODE_EQNS, EXPLODE_IMPLODE] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `IMPLODE`) THEN
  RW_TAC bool_ss [IMPLODE_EQNS, IMPLODE_EXPLODE]);

val EXPLODE_EQ_THM = Q.store_thm
("EXPLODE_EQ_THM",
 `!s h t. ((h::t = EXPLODE s) = (s = STRING h (IMPLODE t))) /\
          ((EXPLODE s = h::t) = (s = STRING h (IMPLODE t)))`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  RW_TAC bool_ss [EQ_IMP_THM,EXPLODE_EQNS,IMPLODE_EQNS,EXPLODE_IMPLODE] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `IMPLODE`) THEN
  simpLib.SIMP_TAC bool_ss [IMPLODE_EQNS, IMPLODE_EXPLODE]);

val IMPLODE_EQ_THM = Q.store_thm
("IMPLODE_EQ_THM",
 `!c s l. ((STRING c s = IMPLODE l) = (l = c::EXPLODE s)) /\
          ((IMPLODE l = STRING c s) = (l = c::EXPLODE s))`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))) THEN
  RW_TAC bool_ss [EQ_IMP_THM,EXPLODE_EQNS,IMPLODE_EQNS,IMPLODE_EXPLODE] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `EXPLODE`) THEN
  simpLib.SIMP_TAC bool_ss [EXPLODE_EQNS, EXPLODE_IMPLODE]);

(*---------------------------------------------------------------------------*)
(* ML-style recursion equations for EXPLODE and IMPLODE                      *)
(*---------------------------------------------------------------------------*)

val EXPLODE_DEST_STRING = Q.store_thm
("EXPLODE_DEST_STRING",
 `!s. EXPLODE s = case DEST_STRING s
                   of NONE -> []
                   || SOME(c,t) -> c::EXPLODE t`,
 GEN_TAC THEN STRIP_ASSUME_TAC (Q.SPEC `s` STRING_CASES)
 THEN RW_TAC std_ss [EXPLODE_EQNS,DEST_STRING]);


val IMPLODE_STRING = Q.store_thm
("IMPLODE_STRING",
 `!clist.IMPLODE clist = FOLDR STRING "" clist`,
INDUCT_THEN listTheory.list_INDUCT ASSUME_TAC
  THEN RW_TAC std_ss [IMPLODE_EQNS,listTheory.FOLDR]);

(*---------------------------------------------------------------------------*)
(* Main fact about STRLEN                                                    *)
(*---------------------------------------------------------------------------*)

val STRLEN_THM = Q.store_thm
("STRLEN_THM",
 `!s. STRLEN s = LENGTH (EXPLODE s)`,
 HO_MATCH_MP_TAC STRING_INDUCT_THM
  THEN RW_TAC bool_ss [STRLEN_DEF,EXPLODE_EQNS,LENGTH,
                       ONCE_REWRITE_RULE [arithmeticTheory.ADD_SYM]
                         arithmeticTheory.ADD1]);

val STRLEN_EQ_0 = Q.store_thm
("STRLEN_EQ_0",
 `!x. (STRLEN x = 0) = (x="")`,
 Cases THEN RW_TAC std_ss [STRLEN_DEF]);

(*---------------------------------------------------------------------------
                      String concatenation
 ---------------------------------------------------------------------------*)

val STRCAT =
  new_definition
   ("STRCAT",
    ``STRCAT s1 s2 = IMPLODE(APPEND (EXPLODE s1) (EXPLODE s2))``);

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


val STRCAT_EXPLODE = Q.store_thm
("STRCAT_EXPLODE",
 `!s1 s2. STRCAT s1 s2 = FOLDR STRING s2 (EXPLODE s1)`,
HO_MATCH_MP_TAC STRING_INDUCT_THM
  THEN RW_TAC std_ss [STRCAT_EQNS,EXPLODE_EQNS,listTheory.FOLDR]);

val STRCAT_EQ_EMPTY = Q.store_thm
("STRCAT_EQ_EMPTY",
 `!x y. (STRCAT x y = "") = (x="") /\ (y="")`,
 Cases THEN Cases THEN RW_TAC std_ss [STRCAT_EQNS]);

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

val isPREFIX_defn = Hol_defn "isPREFIX"
   `isPREFIX s1 s2 =
       case (DEST_STRING s1, DEST_STRING s2)
        of (NONE, _) -> T
        || (SOME __, NONE) -> F
        || (SOME(c1,t1),SOME(c2,t2)) -> (c1=c2) /\ isPREFIX t1 t2`;

val (isPREFIX_DEF,isPREFIX_IND_0) =
 Defn.tprove
   (isPREFIX_defn,
    WF_REL_TAC `measure (STRLEN o FST)`
      THEN RW_TAC std_ss []
      THEN FULL_SIMP_TAC std_ss [DEST_STRING_LEMS]
      THEN RW_TAC arith_ss [STRLEN_DEF]);

val isPREFIX_DEF = save_thm("isPREFIX_DEF",isPREFIX_DEF);

val isPREFIX_IND = Q.store_thm
("isPREFIX_IND",
 `!P. (!s1 s2.
         (!c1 c2 t1 t2.
           (DEST_STRING s1 = SOME (c1,t1)) /\
           (DEST_STRING s2 = SOME (c2,t2)) ==> P t1 t2) ==> P s1 s2)
       ==> !v v1. P v v1`,
 METIS_TAC [pairTheory.ABS_PAIR_THM,isPREFIX_IND_0]);


val isPREFIX_STRCAT = Q.store_thm
("isPREFIX_STRCAT",
 `!s1 s2. isPREFIX s1 s2 = ?s3. s2 = STRCAT s1 s3`,
 recInduct isPREFIX_IND
   THEN REPEAT STRIP_TAC
   THEN RW_TAC list_ss [Once isPREFIX_DEF]
   THEN REPEAT CASE_TAC
   THEN FULL_SIMP_TAC list_ss [DEST_STRING_LEMS,STRCAT_EQNS]
   THEN RW_TAC std_ss []
   THEN PROVE_TAC[]);


(*---------------------------------------------------------------------------*)
(* Emit a vacuous theorem specifying that num is a datatype.                 *)
(*---------------------------------------------------------------------------*)

val DATATYPE_STRING = Q.store_thm
("DATATYPE_STRING",
 `DATATYPE (string "" STRING)`,
 REWRITE_TAC [DATATYPE_TAG_THM]);



(*---------------------------------------------------------------------------
    Exportation
 ---------------------------------------------------------------------------*)

val _ = export_rewrites
   ["ORD_CHR_RWT","IMPLODE_EXPLODE", "EXPLODE_IMPLODE",
    "IMPLODE_11", "EXPLODE_11","EXPLODE_EQNS", "IMPLODE_EQNS",
    "EXPLODE_EQ_THM", "IMPLODE_EQ_THM", "STRLEN_DEF",
    "IMPLODE_EQ_EMPTYSTRING", "EXPLODE_EQ_NIL"];


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "val _ = TypeBase.write";
   S "  [TypeBasePure.mk_datatype_info";
   S "     {ax=TypeBasePure.ORIG string_Axiom,";
   S "      case_def=STRING_CASE_DEF,";
   S "      case_cong=STRING_CASE_CONG,";
   S "      induction=TypeBasePure.ORIG STRING_INDUCT_THM,";
   S "      nchotomy=STRING_CASES,";
   S "      size=SOME(Parse.Term`STRLEN`,TypeBasePure.ORIG STRLEN_DEF),";
   S "      encode=NONE,";
   S "      lift=SOME(mk_var(\"stringSyntax.lift_string\",Parse.Type`:'type -> string -> 'term`)),";
   S "      one_one=SOME STRING_11,";
   S "      fields = [],";
   S "      accessors = [],";
   S "      updates = [],";
   S "      distinct=SOME (CONJUNCT1 STRING_DISTINCT)}];";
   S " ";
   S "val _ = computeLib.add_funs";
   S "        [CHR_ORD,ORD_CHR_COMPUTE,STRING_CASE_DEF,STRLEN_DEF,";
   S "         EXPLODE_EQNS,IMPLODE_EQNS,STRCAT_EQNS];"
 end)};

val _ = ConstMapML.insert(prim_mk_const{Name="DEST_STRING",Thy="string"});
val _ = ConstMapML.insert(prim_mk_const{Name="STRING",Thy="string"});
val _ = ConstMapML.prim_insert(prim_mk_const{Name="EMPTYSTRING",Thy="string"},
                               ("","\"\"",Parse.Type`:string`));

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in S "val _ = ConstMapML.insert (prim_mk_const{Name=\"CHR\",Thy=\"string\"});";
     NL();
     S "val _ = ConstMapML.insert (prim_mk_const{Name=\"ORD\",Thy=\"string\"});";
     NL();
     S "val _ = ConstMapML.insert (prim_mk_const{Name=\"DEST_STRING\",Thy=\"string\"});";
     NL();
     S "val _ = ConstMapML.insert (prim_mk_const{Name=\"STRING\",Thy=\"string\"});";
     NL();
     S "val _ = ConstMapML.prim_insert(prim_mk_const{Name=\"EMPTYSTRING\",Thy=\"string\"},"; NL();
     S "                   (\"\",\"\\\"\\\"\",mk_type(\"string\",[])));";
     NL()
  end)}

val _ =
 let open EmitML
 in emitML (!Globals.emitMLDir)
   ("string",
    OPEN ["num", "list", "option"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type char = Char.char"
    :: MLSIG "type string = String.string"
    :: MLSIG "val CHR : num -> char"
    :: MLSIG "val ORD : char -> num"
    :: MLSTRUCT "type char = Char.char;"
    :: MLSTRUCT "type string = String.string;"
    :: MLSTRUCT "fun CHR n = Char.chr(valOf(Int.fromString(numML.toDecString n)));"
    :: MLSTRUCT "fun ORD c = numML.fromDecString(Int.toString(Char.ord c));"
    :: MLSTRUCT "fun STRING c s = String.^(Char.toString c,s);"
    :: MLSTRUCT "fun DEST_STRING s = if s= \"\" then NONE \n\
        \          else SOME(String.sub(s,0),String.extract(s,1,NONE));"
    :: map (DEFN o PURE_REWRITE_RULE [arithmeticTheory.NUMERAL_DEF])
       [EXPLODE_DEST_STRING, IMPLODE_STRING, STRLEN_THM, STRCAT_EXPLODE, isPREFIX_DEF])
 end;

val _ = export_theory();

val _ = let
  val ^^ = Path.concat
  infix ^^
in
  export_theory_as_docfiles ("help" ^^ "thms")
end;
