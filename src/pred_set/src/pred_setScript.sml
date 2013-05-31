(* =====================================================================*)
(* LIBRARY: pred_set							*)
(* FILE:    mk_pred_set.sml						*)
(* DESCRIPTION: a simple theory of predicates-as-sets			*)
(*									*)
(* AUTHOR:  T. Kalker							*)
(* DATE:    8 June 1989  			         		*)
(*									*)
(* REVISED: Tom Melham (extensively revised and extended)		*)
(* DATE:    January 1992						*)
(* =====================================================================*)

(* interactive use
app load ["pairLib", "numLib", "PGspec", "PSet_ind", "Q",
          "Defn", "TotalDefn", "metisLib"];
*)
open HolKernel Parse boolLib Prim_rec pairLib numLib
     pairTheory numTheory prim_recTheory arithmeticTheory whileTheory
     BasicProvers metisLib mesonLib simpLib boolSimps;

val AP = numLib.ARITH_PROVE
val ARITH_ss = numSimps.ARITH_ss
val arith_ss = bool_ss ++ ARITH_ss

fun store_thm(r as(n,t,tac)) = let
  val th = Tactical.store_thm r
in
  if String.isPrefix "IN_" n then let
      val stem = String.extract(n,3,NONE)
    in
      if isSome (CharVector.find (equal #"_") stem) then th
      else
        case Lib.total (#1 o strip_comb o lhs o #2 o strip_forall o concl) th of
          NONE => th
        | SOME t =>
            if same_const t IN_tm then let
                val applied_thm = SIMP_RULE bool_ss [SimpLHS, IN_DEF] th
                val applied_name = stem ^ "_applied"
              in
                save_thm(applied_name, applied_thm)
              ; export_rewrites [applied_name]
              ; th
              end
            else th
    end
  else th
end


(* ---------------------------------------------------------------------*)
(* Create the new theory.						*)
(* ---------------------------------------------------------------------*)

val _ = new_theory "pred_set";

val _ = type_abbrev ("set", ``:'a -> bool``);
val _ = disable_tyabbrev_printing "set";

local open OpenTheoryMap
  val ns = ["Set"]
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="pred_set",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end

(* =====================================================================*)
(* Membership. 								*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* The axiom of specification: x IN {y | P y} iff P x			*)
(* ---------------------------------------------------------------------*)

val SPECIFICATION = store_thm(
  "SPECIFICATION",
  --`!P x. $IN (x:'a) (P:'a set) = P x`--,
  REWRITE_TAC [IN_DEF] THEN BETA_TAC THEN REWRITE_TAC []);

val IN_ABS = store_thm (
  "IN_ABS",
  ``!x P. (x IN \x. P x) = P x``,
  SIMP_TAC bool_ss [IN_DEF]);
val _ = export_rewrites ["IN_ABS"]

(* ---------------------------------------------------------------------*)
(* Axiom of extension: (s = t) iff !x. x IN s = x IN t			*)
(* ---------------------------------------------------------------------*)

val EXTENSION = store_thm
   ("EXTENSION",
    (--`!s t. (s=t) = (!x:'a. x IN s = x IN t)`--),
    REPEAT GEN_TAC THEN
    REWRITE_TAC [SPECIFICATION,SYM (FUN_EQ_CONV (--`f:'a->'b = g`--))]);

val NOT_EQUAL_SETS =
    store_thm
    ("NOT_EQUAL_SETS",
	     (--`!s:'a set. !t. ~(s = t) = ?x. x IN t = ~(x IN s)`--),
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN
      ASM_CASES_TAC (--`(x:'a) IN s`--) THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
      STRIP_TAC THEN EXISTS_TAC (--`x:'a`--) THEN
      ASM_CASES_TAC (--`(x:'a) IN s`--) THEN ASM_REWRITE_TAC []]);

(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)

val NUM_SET_WOP =
    store_thm
    ("NUM_SET_WOP",
     (--`!s. (?n. n IN s) = ?n. n IN s /\ (!m. m IN s ==> n <= m)`--),
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [let val th = BETA_RULE (ISPEC (--`\n:num. n IN s`--) WOP)
      in IMP_RES_THEN (X_CHOOSE_THEN (--`N:num`--) STRIP_ASSUME_TAC) th
      end THEN EXISTS_TAC (--`N:num`--) THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC,
       GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
       ASM_REWRITE_TAC [GSYM NOT_LESS]],
      EXISTS_TAC (--`n:num`--) THEN FIRST_ASSUM ACCEPT_TAC]);

(* ===================================================================== *)
(* Generalized set specification.					 *)
(* ===================================================================== *)
val GSPEC_DEF_LEMMA =
    TAC_PROOF
    (([], (--`?g:('b->('a#bool))-> 'a set.
           !f. !v:'a. v IN (g f) = ?x:'b. (v,T) = f x`--)),
     EXISTS_TAC (--`\f. \y:'a. ?x:'b. (y,T) = f x`--) THEN
     REPEAT GEN_TAC THEN
     PURE_ONCE_REWRITE_TAC [SPECIFICATION] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REFL_TAC);

(* --------------------------------------------------------------------- *)
(* generalized axiom of specification:					 *)
(*									 *)
(*   GSPECIFICATION = |- !f v. v IN (GSPEC f) = (?x. v,T = f x)		 *)
(* --------------------------------------------------------------------- *)

val GSPECIFICATION = new_specification
  ("GSPECIFICATION", ["GSPEC"], GSPEC_DEF_LEMMA);
val _ = TeX_notation {hol = "|", TeX = ("\\HOLTokenBar{}", 1)}
val _ = ot0 "GSPEC" "specification"

(* --------------------------------------------------------------------- *)
(* load generalized specification code.					 *)
(* --------------------------------------------------------------------- *)

val SET_SPEC_CONV = PGspec.SET_SPEC_CONV GSPECIFICATION;

val SET_SPEC_ss = SSFRAG
  {name=SOME"SET_SPEC",
   ac=[], congs=[], dprocs=[], filter=NONE, rewrs=[],
   convs = [{conv = K (K SET_SPEC_CONV),
   key = SOME([], ``x IN GSPEC f``),
   name = "SET_SPEC_CONV", trace = 2}]}

val _ = augment_srw_ss [SET_SPEC_ss]


(* --------------------------------------------------------------------- *)
(* activate generalized specification parser/pretty-printer.		 *)
(* --------------------------------------------------------------------- *)
(* define_set_abstraction_syntax "GSPEC"; *)
(* set_flag("print_set",true); *)

val _ = add_rule{term_name = "gspec special", fixity = Closefix,
                 pp_elements = [TOK "{", TM, HardSpace 1, TOK "|",
                                BreakSpace(1,0),TM, TOK "}"],
                 paren_style = OnlyIfNecessary,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))};

val _ = add_rule{term_name = "gspec2 special", fixity = Closefix,
                 pp_elements = [TOK "{",TM, TOK "|", TM, TOK "|", TM, TOK "}"],
                 paren_style = OnlyIfNecessary,
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))}

(* the phrase "gspec special" is dealt with in the translation from
   pre-pre-terms to terms *)

(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)

val lemma =
    TAC_PROOF
    (([], (--`!s x. x IN s ==>  !f:'a->'b. (f x) IN {f x | x IN s}`--)),
     REPEAT STRIP_TAC THEN CONV_TAC SET_SPEC_CONV THEN
     EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[]);

val SET_MINIMUM =
    store_thm
    ("SET_MINIMUM",
     (--`!s:'a -> bool. !M.
      (?x. x IN s) = ?x. x IN s /\ !y. y IN s ==> M x <= M y`--),
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [IMP_RES_THEN (ASSUME_TAC o ISPEC (--`M:'a->num`--)) lemma THEN
      let val th = SET_SPEC_CONV (--`(n:num) IN {M x | (x:'a) IN s}`--)
      in IMP_RES_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [th]) NUM_SET_WOP
      end THEN EXISTS_TAC (--`x':'a`--) THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC,
       FIRST_ASSUM (SUBST_ALL_TAC o SYM) THEN
       REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC (--`y:'a`--) THEN CONJ_TAC THENL
       [REFL_TAC, FIRST_ASSUM ACCEPT_TAC]],
      EXISTS_TAC (--`x:'a`--) THEN FIRST_ASSUM ACCEPT_TAC]);


(* ===================================================================== *)
(* The empty set							 *)
(* ===================================================================== *)

val EMPTY_DEF = new_definition
    ("EMPTY_DEF", (--`EMPTY = (\x:'a.F)`--));
open Unicode
val _ = overload_on (UChar.emptyset, ``pred_set$EMPTY``)
val _ = TeX_notation {hol = UChar.emptyset, TeX = ("\\HOLTokenEmpty{}", 1)}
val _ = ot0 "EMPTY" "{}"

val NOT_IN_EMPTY =
    store_thm
    ("NOT_IN_EMPTY",
     (--`!x:'a.~(x IN EMPTY)`--),
     PURE_REWRITE_TAC [EMPTY_DEF,SPECIFICATION] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC);

val _ = export_rewrites ["NOT_IN_EMPTY"]

val MEMBER_NOT_EMPTY =
    store_thm
    ("MEMBER_NOT_EMPTY",
     (--`!s:'a set. (?x. x IN s) = ~(s = EMPTY)`--),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REWRITE_TAC [NOT_CLAUSES]);

val EMPTY_applied = store_thm(
  "EMPTY_applied",
  ``EMPTY x <=> F``,
  REWRITE_TAC [EMPTY_DEF])
val _ = export_rewrites ["EMPTY_applied"]

(* ===================================================================== *)
(* The set of everything						 *)
(* ===================================================================== *)

val UNIV_DEF = new_definition
    ("UNIV_DEF",(--`UNIV = (\x:'a.T)`--));

val _ = ot0 "UNIV" "universe"

val IN_UNIV =
    store_thm
    ("IN_UNIV",
     (--`!x:'a. x IN UNIV`--),
     GEN_TAC THEN PURE_REWRITE_TAC [UNIV_DEF,SPECIFICATION] THEN
     CONV_TAC BETA_CONV THEN ACCEPT_TAC TRUTH);
val _ = export_rewrites ["IN_UNIV"]

val UNIV_NOT_EMPTY =
    store_thm
    ("UNIV_NOT_EMPTY",
     (--`~(UNIV:'a set = EMPTY)`--),
     REWRITE_TAC [EXTENSION,IN_UNIV,NOT_IN_EMPTY]);
val _ = export_rewrites ["UNIV_NOT_EMPTY"]

val EMPTY_NOT_UNIV =
    store_thm
    ("EMPTY_NOT_UNIV",
     (--`~(EMPTY = (UNIV:'a set))`--),
     REWRITE_TAC [EXTENSION,IN_UNIV,NOT_IN_EMPTY]);

val EQ_UNIV =
    store_thm
    ("EQ_UNIV",
     (--`(!x:'a. x IN s) = (s = UNIV)`--),
     REWRITE_TAC [EXTENSION,IN_UNIV]);

val _ = overload_on ("univ", ``\x:'a itself. UNIV : 'a set``)
val _ = set_fixity "univ" (Prefix 2200)

val _ = overload_on (UnicodeChars.universal_set, ``\x:'a itself. UNIV: 'a set``)
val _ = set_fixity UnicodeChars.universal_set (Prefix 2200)

fun univ_printer (tyg, tmg) backend printer ppfns gravs depth tm = let
  open smpp infix >>
  val ppfns = ppfns : term_pp_types.ppstream_funs
  val (elty, _) = dom_rng (type_of tm)
  val itself_t = Term.inst [alpha |-> elty] boolSyntax.the_value
  val U = if get_tracefn "Unicode" () = 1 then UnicodeChars.universal_set
          else "univ"
in
  #add_string ppfns U >>
  printer gravs depth itself_t
end

val _ = temp_add_user_printer("UNIVprinter", ``UNIV: 'a set``, univ_printer)
val _ = TeX_notation {hol = "univ", TeX = ("\\ensuremath{\\cal{U}}", 1)}
val _ = TeX_notation {hol = UnicodeChars.universal_set,
                      TeX = ("\\ensuremath{\\cal{U}}", 1)}


(* ===================================================================== *)
(* Set inclusion.							 *)
(* ===================================================================== *)

val SUBSET_DEF = new_definition(
  "SUBSET_DEF",
  ``$SUBSET s t = !x:'a. x IN s ==> x IN t``);
val _ = set_fixity "SUBSET" (Infix(NONASSOC, 450))
val _ = unicode_version { u = UChar.subset, tmnm = "SUBSET"};
val _ = TeX_notation {hol = "SUBSET", TeX = ("\\HOLTokenSubset{}", 1)}
val _ = TeX_notation {hol = UChar.subset, TeX = ("\\HOLTokenSubset{}", 1)}
val _ = ot0 "SUBSET" "subset"

val SUBSET_TRANS = store_thm
    ("SUBSET_TRANS",
     (--`!(s:'a set) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`--),
     REWRITE_TAC [SUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN
     REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

val SUBSET_REFL = store_thm
    ("SUBSET_REFL",
     (--`!(s:'a set). s SUBSET s`--),
     REWRITE_TAC[SUBSET_DEF]);

val SUBSET_ANTISYM = store_thm
    ("SUBSET_ANTISYM",
     (--`!(s:'a set) t. (s SUBSET t) /\ (t SUBSET s) ==> (s = t)`--),
     REWRITE_TAC [SUBSET_DEF, EXTENSION] THEN
     REPEAT STRIP_TAC THEN
     EQ_TAC THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC);

val EMPTY_SUBSET =
    store_thm
    ("EMPTY_SUBSET",
     (--`!s:'a set. EMPTY SUBSET s`--),
     REWRITE_TAC [SUBSET_DEF,NOT_IN_EMPTY]);
val _ = export_rewrites ["EMPTY_SUBSET"]

val SUBSET_EMPTY =
    store_thm
    ("SUBSET_EMPTY",
     (--`!s:'a set. s SUBSET EMPTY = (s = EMPTY)`--),
     PURE_REWRITE_TAC [SUBSET_DEF,NOT_IN_EMPTY] THEN
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY]);

val _ = export_rewrites ["SUBSET_EMPTY"]

val SUBSET_UNIV =
    store_thm
    ("SUBSET_UNIV",
     (--`!s:'a set. s SUBSET UNIV`--),
     REWRITE_TAC [SUBSET_DEF,IN_UNIV]);
val  _ = export_rewrites ["SUBSET_UNIV"]

val UNIV_SUBSET =
    store_thm
    ("UNIV_SUBSET",
     (--`!s:'a set. UNIV SUBSET s = (s = UNIV)`--),
     REWRITE_TAC [SUBSET_DEF,IN_UNIV,EXTENSION]);
val _ = export_rewrites ["UNIV_SUBSET"]

(* ===================================================================== *)
(* Proper subset.							 *)
(* ===================================================================== *)

val PSUBSET_DEF =  new_definition(
  "PSUBSET_DEF",
  ``PSUBSET (s:'a set) t <=> s SUBSET t /\ ~(s = t)``);
val _ = set_fixity "PSUBSET" (Infix(NONASSOC, 450))
val _ = unicode_version { u = UTF8.chr 0x2282, tmnm = "PSUBSET"}
val _ = TeX_notation {hol = "PSUBSET", TeX = ("\\HOLTokenPSubset", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2282, TeX = ("\\HOLTokenPSubset", 1)}
val _ = ot0 "PSUBSET" "properSubset"

val PSUBSET_TRANS = store_thm ("PSUBSET_TRANS",
   (--`!s:'a set. !t u. (s PSUBSET t /\ t PSUBSET u) ==> (s PSUBSET u)`--),
     PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [IMP_RES_TAC SUBSET_TRANS,
      DISCH_THEN SUBST_ALL_TAC THEN
      IMP_RES_TAC SUBSET_ANTISYM THEN
      RES_TAC]);

val PSUBSET_IRREFL =
    store_thm
    ("PSUBSET_IRREFL",
     (--`!s:'a set. ~(s PSUBSET s)`--),
     REWRITE_TAC [PSUBSET_DEF,SUBSET_REFL]);

val NOT_PSUBSET_EMPTY =
    store_thm
    ("NOT_PSUBSET_EMPTY",
     (--`!s:'a set. ~(s PSUBSET EMPTY)`--),
     REWRITE_TAC [PSUBSET_DEF,SUBSET_EMPTY,NOT_AND]);

val NOT_UNIV_PSUBSET =
    store_thm
    ("NOT_UNIV_PSUBSET",
     (--`!s:'a set. ~(UNIV PSUBSET s)`--),
     REWRITE_TAC [PSUBSET_DEF,UNIV_SUBSET,DE_MORGAN_THM] THEN
     GEN_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
     PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
     MATCH_ACCEPT_TAC EXCLUDED_MIDDLE);

val PSUBSET_UNIV =
    store_thm
    ("PSUBSET_UNIV",
     (--`!s:'a set. (s PSUBSET UNIV) = ?x:'a. ~(x IN s)`--),
     REWRITE_TAC [PSUBSET_DEF,SUBSET_UNIV,EXTENSION,IN_UNIV] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN GEN_TAC THEN REFL_TAC);

(* ===================================================================== *)
(* Union								 *)
(* ===================================================================== *)

val UNION_DEF = new_infixl_definition
     ("UNION_DEF", (--`UNION s t = {x:'a | x IN s \/ x IN t}`--),500);
val _ = unicode_version{ u = UChar.union, tmnm = "UNION"}
val _ = TeX_notation {hol = "UNION", TeX = ("\\HOLTokenUnion{}", 1)}
val _ = TeX_notation {hol = UChar.union, TeX = ("\\HOLTokenUnion{}", 1)}
val _ = ot0 "UNION" "union"

val IN_UNION = store_thm
     ("IN_UNION",
      (--`!s t (x:'a). x IN (s UNION t) = x IN s \/ x IN t`--),
      PURE_ONCE_REWRITE_TAC [UNION_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);
val _ = export_rewrites ["IN_UNION"]

val UNION_ASSOC = store_thm
    ("UNION_ASSOC",
     (--`!(s:'a set) t u. s UNION (t UNION u) = (s UNION t) UNION u`--),
     REWRITE_TAC [EXTENSION, IN_UNION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC[]);

val UNION_IDEMPOT = store_thm
    ("UNION_IDEMPOT",
     (--`!(s:'a set). s UNION s = s`--),
     REWRITE_TAC[EXTENSION, IN_UNION]);

val UNION_COMM = store_thm
    ("UNION_COMM",
     (--`!(s:'a set) t. s UNION t = t UNION s`--),
     REWRITE_TAC[EXTENSION, IN_UNION] THEN
     REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM);

val SUBSET_UNION =
    store_thm
    ("SUBSET_UNION",
     (--`(!s:'a set. !t. s SUBSET (s UNION t)) /\
      (!s:'a set. !t. s SUBSET (t UNION s))`--),
     PURE_REWRITE_TAC [SUBSET_DEF,IN_UNION] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);

val UNION_SUBSET = store_thm(
    "UNION_SUBSET",
  ``!s t u. (s UNION t) SUBSET u = s SUBSET u /\ t SUBSET u``,
  PROVE_TAC [IN_UNION, SUBSET_DEF]);

val SUBSET_UNION_ABSORPTION =
    store_thm
    ("SUBSET_UNION_ABSORPTION",
     (--`!s:'a set. !t. s SUBSET t = (s UNION t = t)`--),
     REWRITE_TAC [SUBSET_DEF,EXTENSION,IN_UNION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [RES_TAC,ASM_REWRITE_TAC[],RES_TAC]);

val UNION_EMPTY =
    store_thm
    ("UNION_EMPTY",
     (--`(!s:'a set. EMPTY UNION s = s) /\
      (!s:'a set. s UNION EMPTY = s)`--),
     REWRITE_TAC [IN_UNION,EXTENSION,NOT_IN_EMPTY]);

val _ = export_rewrites ["UNION_EMPTY"]

val UNION_UNIV =
    store_thm
    ("UNION_UNIV",
     (--`(!s:'a set. UNIV UNION s = UNIV) /\
      (!s:'a set. s UNION UNIV = UNIV)`--),
     REWRITE_TAC [IN_UNION,EXTENSION,IN_UNIV]);

val _ = export_rewrites ["UNION_UNIV"]

val EMPTY_UNION = store_thm("EMPTY_UNION",
(--`!s:'a set. !t. (s UNION t = EMPTY) = ((s = EMPTY) /\ (t = EMPTY))`--),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY,IN_UNION,DE_MORGAN_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC);
val _ = export_rewrites ["EMPTY_UNION"]



(* ===================================================================== *)
(* Intersection								 *)
(* ===================================================================== *)

val INTER_DEF = new_infixl_definition
     ("INTER_DEF",
      (--`INTER s t = {x:'a | x IN s /\ x IN t}`--), 600);
val _ = unicode_version{ u = UChar.inter, tmnm = "INTER"};
val _ = TeX_notation {hol = "INTER", TeX = ("\\HOLTokenInter{}", 1)}
val _ = TeX_notation {hol = UChar.inter, TeX = ("\\HOLTokenInter{}", 1)}
val _ = ot0 "INTER" "intersect"

val IN_INTER = store_thm
     ("IN_INTER",
      (--`!s t (x:'a). x IN (s INTER t) = x IN s /\ x IN t`--),
      PURE_ONCE_REWRITE_TAC [INTER_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);
val _ = export_rewrites ["IN_INTER"]

val INTER_ASSOC = store_thm
    ("INTER_ASSOC",
     (--`!(s:'a set) t u. s INTER (t INTER u) = (s INTER t) INTER u`--),
     REWRITE_TAC [EXTENSION, IN_INTER, CONJ_ASSOC]);

val INTER_IDEMPOT = store_thm
    ("INTER_IDEMPOT",
     (--`!(s:'a set). s INTER s = s`--),
     REWRITE_TAC[EXTENSION, IN_INTER]);

val INTER_COMM = store_thm
    ("INTER_COMM",
     (--`!(s:'a set) t. s INTER t = t INTER s`--),
     REWRITE_TAC[EXTENSION, IN_INTER] THEN
     REPEAT GEN_TAC THEN
     MATCH_ACCEPT_TAC CONJ_SYM);

val INTER_SUBSET =
    store_thm
    ("INTER_SUBSET",
     (--`(!s:'a set. !t. (s INTER t) SUBSET s) /\
      (!s:'a set. !t. (t INTER s) SUBSET s)`--),
     PURE_REWRITE_TAC [SUBSET_DEF,IN_INTER] THEN
     REPEAT STRIP_TAC);

val SUBSET_INTER = Q.store_thm
("SUBSET_INTER",
 `!s t u. s SUBSET (t INTER u) = s SUBSET t /\ s SUBSET u`,
  PROVE_TAC [IN_INTER, SUBSET_DEF]);

val SUBSET_INTER_ABSORPTION =
    store_thm
    ("SUBSET_INTER_ABSORPTION",
     (--`!s:'a set. !t. s SUBSET t = (s INTER t = s)`--),
     REWRITE_TAC [SUBSET_DEF,EXTENSION,IN_INTER] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM ACCEPT_TAC, RES_TAC, RES_TAC]);

val INTER_EMPTY =
    store_thm
    ("INTER_EMPTY",
     (--`(!s:'a set. EMPTY INTER s = EMPTY) /\
      (!s:'a set. s INTER EMPTY = EMPTY)`--),
     REWRITE_TAC [IN_INTER,EXTENSION,NOT_IN_EMPTY]);

val _ = export_rewrites ["INTER_EMPTY"]

val INTER_UNIV =
    store_thm
    ("INTER_UNIV",
     (--`(!s:'a set. UNIV INTER s = s) /\
      (!s:'a set. s INTER UNIV = s)`--),
     REWRITE_TAC [IN_INTER,EXTENSION,IN_UNIV]);


(* ===================================================================== *)
(* Distributivity							 *)
(* ===================================================================== *)

val UNION_OVER_INTER = store_thm
   ("UNION_OVER_INTER",
    (--`!s:'a set. !t u.
      s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`--),
    REWRITE_TAC [EXTENSION,IN_INTER,IN_UNION] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_REWRITE_TAC[]);

val INTER_OVER_UNION = store_thm
   ("INTER_OVER_UNION",
    (--`!s:'a set. !t u.
      s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`--),
    REWRITE_TAC [EXTENSION,IN_INTER,IN_UNION] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_REWRITE_TAC[]);

(* ===================================================================== *)
(* Disjoint sets.							 *)
(* ===================================================================== *)

val DISJOINT_DEF = new_definition ("DISJOINT_DEF",
(--`DISJOINT (s:'a set) t = ((s INTER t) = EMPTY)`--));

val IN_DISJOINT =
    store_thm
    ("IN_DISJOINT",
     (--`!s:'a set. !t. DISJOINT s t = ~(?x. x IN s /\ x IN t)`--),
     REWRITE_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     REPEAT GEN_TAC THEN REFL_TAC);

val DISJOINT_SYM =
    store_thm
    ("DISJOINT_SYM",
     (--`!s:'a set. !t. DISJOINT s t = DISJOINT t s`--),
     PURE_ONCE_REWRITE_TAC [DISJOINT_DEF] THEN REPEAT GEN_TAC THEN
     SUBST1_TAC (SPECL [--`s:'a set`--, --`t:'a set`--] INTER_COMM) THEN
     REFL_TAC);

(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)
val DISJOINT_EMPTY =
    store_thm
    ("DISJOINT_EMPTY",
     (--`!s:'a set. DISJOINT EMPTY s /\ DISJOINT s EMPTY`--),
     REWRITE_TAC [DISJOINT_DEF,INTER_EMPTY]);

val DISJOINT_EMPTY_REFL =
    store_thm
    ("DISJOINT_EMPTY_REFL",
     (--`!s:'a set. (s = EMPTY) = (DISJOINT s s)`--),
     REWRITE_TAC [DISJOINT_DEF,INTER_IDEMPOT]);
val DISJOINT_EMPTY_REFL_RWT = save_thm(
  "DISJOINT_EMPTY_REFL_RWT",
  ONCE_REWRITE_RULE [EQ_SYM_EQ] DISJOINT_EMPTY_REFL)

(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)
val DISJOINT_UNION = store_thm ("DISJOINT_UNION",
--`!(s:'a set) t u. DISJOINT (s UNION t) u = DISJOINT s u /\ DISJOINT t u`--,
     REWRITE_TAC [IN_DISJOINT,IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
     REWRITE_TAC [DE_MORGAN_THM,RIGHT_AND_OVER_OR] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN
     DISCH_THEN(fn th => GEN_TAC THEN
                         STRIP_ASSUME_TAC (SPEC (--`x:'a`--) th)) THEN
     ASM_REWRITE_TAC []);

val DISJOINT_UNION_BOTH = Q.store_thm
("DISJOINT_UNION_BOTH",
 `!s t u:'a set.
        (DISJOINT (s UNION t) u = DISJOINT s u /\ DISJOINT t u) /\
        (DISJOINT u (s UNION t) = DISJOINT s u /\ DISJOINT t u)`,
  PROVE_TAC [DISJOINT_UNION, DISJOINT_SYM]);

val DISJOINT_SUBSET = Q.store_thm
("DISJOINT_SUBSET",
  `!s t u. DISJOINT s t /\ u SUBSET t ==> DISJOINT s u`,
  REWRITE_TAC [DISJOINT_DEF, SUBSET_DEF, IN_INTER, NOT_IN_EMPTY,
               EXTENSION] THEN
  PROVE_TAC []);


(* ===================================================================== *)
(* Set difference							 *)
(* ===================================================================== *)

val DIFF_DEF = new_infixl_definition
    ("DIFF_DEF",
     (--`DIFF s t = {x:'a | x IN s /\ ~ (x IN t)}`--),500);
val _ = ot0 "DIFF" "difference"

val IN_DIFF = store_thm
    ("IN_DIFF",
     (--`!(s:'a set) t x. x IN (s DIFF t) = x IN s /\ ~(x IN t)`--),
     REPEAT GEN_TAC THEN
     PURE_ONCE_REWRITE_TAC [DIFF_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
     REFL_TAC);

val _ = export_rewrites ["IN_DIFF"]

val DIFF_EMPTY =
    store_thm
    ("DIFF_EMPTY",
     (--`!s:'a set. s DIFF EMPTY = s`--),
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY,IN_DIFF,EXTENSION]);

val EMPTY_DIFF =
    store_thm
    ("EMPTY_DIFF",
     (--`!s:'a set. EMPTY DIFF s = EMPTY`--),
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY,IN_DIFF,EXTENSION]);
val _ = export_rewrites ["EMPTY_DIFF"]

val DIFF_UNIV =
    store_thm
    ("DIFF_UNIV",
     (--`!s:'a set. s DIFF UNIV = EMPTY`--),
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY,IN_DIFF,IN_UNIV,EXTENSION]);

val DIFF_DIFF =
    store_thm
    ("DIFF_DIFF",
     (--`!s:'a set. !t. (s DIFF t) DIFF t = s DIFF t`--),
     REWRITE_TAC [EXTENSION,IN_DIFF,SYM(SPEC_ALL CONJ_ASSOC)]);

val DIFF_EQ_EMPTY =
    store_thm
    ("DIFF_EQ_EMPTY",
     (--`!s:'a set. s DIFF s = EMPTY`--),
     REWRITE_TAC [EXTENSION,IN_DIFF,NOT_IN_EMPTY,DE_MORGAN_THM] THEN
     PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
     REWRITE_TAC [EXCLUDED_MIDDLE]);

val DIFF_SUBSET = Q.store_thm
("DIFF_SUBSET",
  `!s t. (s DIFF t) SUBSET s`,
  REWRITE_TAC [SUBSET_DEF, IN_DIFF] THEN PROVE_TAC []);

val UNION_DIFF = store_thm(
  "UNION_DIFF",
  ``s SUBSET t ==> (s UNION (t DIFF s) = t) /\ ((t DIFF s) UNION s = t)``,
  SRW_TAC [][EXTENSION, SUBSET_DEF] THEN PROVE_TAC []);

val DIFF_UNION = store_thm(
"DIFF_UNION",
``!x y z. x DIFF (y UNION z) = x DIFF y DIFF z``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

val DIFF_COMM = store_thm(
"DIFF_COMM",
``!x y z. x DIFF y DIFF z = x DIFF z DIFF y``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

val DIFF_SAME_UNION = store_thm(
"DIFF_SAME_UNION",
``!x y. ((x UNION y) DIFF x = y DIFF x) /\ ((x UNION y) DIFF y = x DIFF y)``,
SRW_TAC[][EXTENSION,EQ_IMP_THM])

(* ===================================================================== *)
(* The insertion function.					         *)
(* ===================================================================== *)

val INSERT_DEF =
    new_infixr_definition
    ("INSERT_DEF", (--`INSERT (x:'a) s = {y | (y = x) \/ y IN s}`--),490);
val _ = ot0 "INSERT" "insert"

(* --------------------------------------------------------------------- *)
(* set up sets as a list-form  the {x1;...;xn} notation                  *)
(* --------------------------------------------------------------------- *)

val _ = add_listform {leftdelim = [TOK "{"], rightdelim = [TOK "}"],
                      separator = [TOK ";", BreakSpace(1,0)],
                      cons = "INSERT", nilstr = "EMPTY",
                      block_info = (PP.INCONSISTENT, 0)};

(* --------------------------------------------------------------------- *)
(* Theorems about INSERT.						 *)
(* --------------------------------------------------------------------- *)

val IN_INSERT =
     store_thm
     ("IN_INSERT",
      (--`!x:'a. !y s. x IN (y INSERT s) = ((x=y) \/ x IN s)`--),
      PURE_ONCE_REWRITE_TAC [INSERT_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);

val _ = export_rewrites ["IN_INSERT"]

val COMPONENT =
     store_thm
     ("COMPONENT",
      (--`!x:'a. !s. x IN (x INSERT s)`--),
      REWRITE_TAC [IN_INSERT]);

val SET_CASES = store_thm("SET_CASES",
(--`!s:'a set.
       (s = EMPTY) \/
       ?x:'a. ?t. ((s = x INSERT t) /\ ~(x IN t))`--),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY] THEN GEN_TAC THEN
     DISJ_CASES_THEN MP_TAC (SPEC (--`?x:'a. x IN s`--) EXCLUDED_MIDDLE) THENL
     [STRIP_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [--`x:'a`--, --`{y:'a | y IN s /\ ~(y = x)}`--] THEN
      REWRITE_TAC [IN_INSERT] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      ASM_REWRITE_TAC[EXCLUDED_MIDDLE],
      CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      STRIP_TAC THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

val DECOMPOSITION =
    store_thm
    ("DECOMPOSITION",
     (--`!s:'a set. !x. x IN s = ?t. (s = x INSERT t) /\ ~(x IN t)`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC (--`{y:'a | y IN s /\ ~(y = x)}`--) THEN
      ASM_REWRITE_TAC [EXTENSION,IN_INSERT] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REWRITE_TAC [] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      ASM_REWRITE_TAC [EXCLUDED_MIDDLE],
      STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]]);

val ABSORPTION =
    store_thm
    ("ABSORPTION",
     (--`!x:'a. !s. (x IN s) = (x INSERT s = s)`--),
     REWRITE_TAC [EXTENSION,IN_INSERT] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC [] THEN
     FIRST_ASSUM (fn th => fn g => PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL th)] g)
     THEN DISJ1_TAC THEN REFL_TAC);

val ABSORPTION_RWT = store_thm(
  "ABSORPTION_RWT",
  ``!x:'a s. x IN s ==> (x INSERT s = s)``,
  METIS_TAC [ABSORPTION]);

val INSERT_INSERT =
    store_thm
    ("INSERT_INSERT",
     (--`!x:'a. !s. x INSERT (x INSERT s) = x INSERT s`--),
     REWRITE_TAC [IN_INSERT,EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC[]);

val INSERT_COMM =
    store_thm
    ("INSERT_COMM",
     (--`!x:'a. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`--),
     REWRITE_TAC [IN_INSERT,EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC[]);

val INSERT_UNIV =
    store_thm
    ("INSERT_UNIV",
     (--`!x:'a. x INSERT UNIV = UNIV`--),
     REWRITE_TAC [EXTENSION,IN_INSERT,IN_UNIV]);

val NOT_INSERT_EMPTY =
    store_thm
    ("NOT_INSERT_EMPTY",
     (--`!x:'a. !s. ~(x INSERT s = EMPTY)`--),
     REWRITE_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY,IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN
     REWRITE_TAC []);

val NOT_EMPTY_INSERT =
    store_thm
    ("NOT_EMPTY_INSERT",
     (--`!x:'a. !s. ~(EMPTY = x INSERT s)`--),
     REWRITE_TAC [EXTENSION,IN_INSERT,NOT_IN_EMPTY,IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN
     REWRITE_TAC []);

val _ = export_rewrites ["NOT_INSERT_EMPTY"];
(* don't need both because simplifier's rewrite creator automatically gives
   both senses to inequalities *)

val INSERT_UNION = store_thm (
  "INSERT_UNION",
  (--`!(x:'a) s t.
        (x INSERT s) UNION t =
        (if x IN t then s UNION t else x INSERT (s UNION t))`--),
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC [EXTENSION,IN_UNION,IN_INSERT] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC []);

val INSERT_UNION_EQ =
    store_thm
    ("INSERT_UNION_EQ",
     (--`!x:'a. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`--),
     REPEAT GEN_TAC THEN
     REWRITE_TAC [EXTENSION,IN_UNION,IN_INSERT,DISJ_ASSOC]);

val INSERT_INTER =
    store_thm
    ("INSERT_INTER",
     (--`!x:'a. !s t.
      (x INSERT s) INTER t =
      (if x IN t then x INSERT (s INTER t) else s INTER t)`--),
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC [EXTENSION,IN_INTER,IN_INSERT] THEN
     GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC [],
      STRIP_TAC THEN ASM_REWRITE_TAC [],
      PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
      DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [],
      STRIP_TAC THEN ASM_REWRITE_TAC []]);

val DISJOINT_INSERT = store_thm("DISJOINT_INSERT",
(--`!(x:'a) s t. DISJOINT (x INSERT s) t = (DISJOINT s t) /\ ~(x IN t)`--),
     REWRITE_TAC [IN_DISJOINT,IN_INSERT] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     REWRITE_TAC [DE_MORGAN_THM] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [let val v = genvar (==`:'a`==)
          val GTAC = X_GEN_TAC v
      in DISCH_THEN (fn th => CONJ_TAC THENL [GTAC,ALL_TAC] THEN MP_TAC th)
         THENL [DISCH_THEN (STRIP_ASSUME_TAC o SPEC v) THEN ASM_REWRITE_TAC [],
                DISCH_THEN (MP_TAC o SPEC (--`x:'a`--)) THEN REWRITE_TAC[]]
      end,
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (--`x':'a = x`--) THENL
      [ASM_REWRITE_TAC[], ASM_REWRITE_TAC[]]]);

val INSERT_SUBSET =
    store_thm
    ("INSERT_SUBSET",
     (--`!x:'a. !s t. (x INSERT s) SUBSET t = (x IN t /\ s SUBSET t)`--),
     REWRITE_TAC [IN_INSERT,SUBSET_DEF] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN REFL_TAC,
      FIRST_ASSUM MATCH_MP_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      ASM_REWRITE_TAC [],
      RES_TAC]);

val SUBSET_INSERT =
    store_thm
    ("SUBSET_INSERT",
     (--`!x:'a. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) = s SUBSET t`--),
     PURE_REWRITE_TAC [SUBSET_DEF,IN_INSERT] THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN
      let fun tac th g = SUBST_ALL_TAC th g
                         handle  _ => STRIP_ASSUME_TAC th g
      in RES_THEN (STRIP_THM_THEN tac) THEN RES_TAC
      end,
      REPEAT STRIP_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]);

val INSERT_DIFF =
    store_thm
    ("INSERT_DIFF",
     (--`!s t. !x:'a. (x INSERT s) DIFF t =
     		  (if x IN t then s DIFF t else (x INSERT (s DIFF t)))`--),
     REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [EXTENSION,IN_DIFF,IN_INSERT] THEN
      GEN_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       FIRST_ASSUM (fn th => fn g => SUBST_ALL_TAC th g) THEN RES_TAC,
       STRIP_TAC THEN ASM_REWRITE_TAC[]],
      ASM_REWRITE_TAC [EXTENSION,IN_DIFF,IN_INSERT] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (fn th => fn g => SUBST_ALL_TAC th g) THEN RES_TAC]);

(* with INSERT to hand, it's easy to talk about concrete sets *)
val UNIV_BOOL = store_thm(
  "UNIV_BOOL",
  ``univ(:bool) = {T; F}``,
  SRW_TAC [][EXTENSION]);
val _ = export_rewrites ["UNIV_BOOL"]

(* ===================================================================== *)
(* Removal of an element						 *)
(* ===================================================================== *)

val DELETE_DEF =
    new_infixl_definition
    ("DELETE_DEF", (--`DELETE s (x:'a) = s DIFF {x}`--),500);

val IN_DELETE =
    store_thm
    ("IN_DELETE",
     (--`!s. !x:'a. !y. x IN (s DELETE y) = (x IN s /\ ~(x = y))`--),
     PURE_ONCE_REWRITE_TAC [DELETE_DEF] THEN
     REWRITE_TAC [IN_DIFF,IN_INSERT,NOT_IN_EMPTY]);
val _ = export_rewrites ["IN_DELETE"]

val DELETE_NON_ELEMENT =
    store_thm
    ("DELETE_NON_ELEMENT",
     (--`!x:'a. !s. ~(x IN s) = (s DELETE x = s)`--),
     PURE_REWRITE_TAC [EXTENSION,IN_DELETE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM ACCEPT_TAC,
      FIRST_ASSUM (fn th => fn g => SUBST_ALL_TAC th g handle _ => NO_TAC g)
      THEN RES_TAC,
      RES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC]);

val IN_DELETE_EQ =
    store_thm
    ("IN_DELETE_EQ",
     (--`!s x. !x':'a.
      (x IN s = x' IN s) = (x IN (s DELETE x') = x' IN (s DELETE x))`--),
     REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x:'a = x'`--) THENL
     [ASM_REWRITE_TAC [],
      FIRST_ASSUM (ASSUME_TAC o NOT_EQ_SYM) THEN
      ASM_REWRITE_TAC [IN_DELETE]]);

val EMPTY_DELETE =
    store_thm
    ("EMPTY_DELETE",
     (--`!x:'a. EMPTY DELETE x = EMPTY`--),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY,IN_DELETE]);

val _ = export_rewrites ["EMPTY_DELETE"];

val DELETE_DELETE =
    store_thm
    ("DELETE_DELETE",
     (--`!x:'a. !s. (s DELETE x) DELETE x = s DELETE x`--),
     REWRITE_TAC [EXTENSION,IN_DELETE,SYM(SPEC_ALL CONJ_ASSOC)]);

val DELETE_COMM =
    store_thm
    ("DELETE_COMM",
     (--`!x:'a. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`--),
     PURE_REWRITE_TAC [EXTENSION,IN_DELETE,CONJ_ASSOC] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val DELETE_SUBSET =
    store_thm
    ("DELETE_SUBSET",
     (--`!x:'a. !s. (s DELETE x) SUBSET s`--),
     PURE_REWRITE_TAC [SUBSET_DEF,IN_DELETE] THEN
     REPEAT STRIP_TAC);

val SUBSET_DELETE =
    store_thm
    ("SUBSET_DELETE",
     (--`!x:'a. !s t. s SUBSET (t DELETE x) = (~(x IN s) /\ (s SUBSET t))`--),
     REWRITE_TAC [SUBSET_DEF,IN_DELETE,EXTENSION] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THENL
      [ASSUME_TAC (REFL (--`x:'a`--)) THEN RES_TAC, RES_TAC],
      REPEAT STRIP_TAC THENL
      [RES_TAC, FIRST_ASSUM (fn th => fn g => SUBST_ALL_TAC th g) THEN
       RES_TAC]]);

val SUBSET_INSERT_DELETE =
    store_thm
    ("SUBSET_INSERT_DELETE",
     (--`!x:'a. !s t. s SUBSET (x INSERT t) = ((s DELETE x) SUBSET t)`--),
     REPEAT GEN_TAC THEN
     REWRITE_TAC [SUBSET_DEF,IN_INSERT,IN_DELETE] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THENL
     [RES_TAC THEN RES_TAC,
      ASM_CASES_TAC (--`x':'a = x`--) THEN
      ASM_REWRITE_TAC[] THEN RES_TAC]);

val DIFF_INSERT =
    store_thm
    ("DIFF_INSERT",
     (--`!s t. !x:'a. s DIFF (x INSERT t) = (s DELETE x) DIFF t`--),
     PURE_REWRITE_TAC [EXTENSION,IN_DIFF,IN_INSERT,IN_DELETE] THEN
     REWRITE_TAC [DE_MORGAN_THM,CONJ_ASSOC]);

val PSUBSET_INSERT_SUBSET =
    store_thm
    ("PSUBSET_INSERT_SUBSET",
     (--`!s t. s PSUBSET t = ?x:'a. ~(x IN s) /\ (x INSERT s) SUBSET t`--),
     PURE_REWRITE_TAC [PSUBSET_DEF,NOT_EQUAL_SETS] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ASM_CASES_TAC (--`(x:'a) IN s`--) THENL
      [ASM_CASES_TAC (--`(x:'a) IN t`--) THENL
       [RES_TAC, IMP_RES_TAC SUBSET_DEF THEN RES_TAC],
       EXISTS_TAC (--`x:'a`--) THEN RES_TAC THEN
       ASM_REWRITE_TAC [INSERT_SUBSET]],
      IMP_RES_TAC INSERT_SUBSET,
      IMP_RES_TAC INSERT_SUBSET THEN
      EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[]]);

val lemma =
    TAC_PROOF(([], (--`~(a:bool = b) = (b = ~a)`--)),
    BOOL_CASES_TAC (--`b:bool`--) THEN REWRITE_TAC[]);

val PSUBSET_MEMBER = store_thm("PSUBSET_MEMBER",
(--`!s:'a set.
    !t. s PSUBSET t = (s SUBSET t /\ ?y. y IN t /\ ~(y IN s))`--),
     REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     PURE_ONCE_REWRITE_TAC [EXTENSION,SUBSET_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     PURE_ONCE_REWRITE_TAC [lemma] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [RES_TAC,
      EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (--`(x:'a) IN s`--) THENL
       [RES_TAC THEN RES_TAC,FIRST_ASSUM ACCEPT_TAC],
      RES_TAC,
      EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[]]);

val DELETE_INSERT = store_thm("DELETE_INSERT",
(--`!(x:'a) y s.
    (x INSERT s) DELETE y = (if (x=y) then s DELETE y
                             else x INSERT (s DELETE y))`--),
     REWRITE_TAC [EXTENSION,IN_DELETE,IN_INSERT] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN DISCH_TAC THEN
      let fun tac th g = SUBST_ALL_TAC th g handle _ => ASSUME_TAC th g
      in DISCH_THEN (STRIP_THM_THEN tac) THENL
         [ASM_REWRITE_TAC [IN_INSERT],
         COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_DELETE,IN_INSERT]]
      end,
      COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_DELETE,IN_INSERT] THENL
      [STRIP_TAC THEN ASM_REWRITE_TAC [],
       STRIP_TAC THEN ASM_REWRITE_TAC []]]);

val INSERT_DELETE =
    store_thm
    ("INSERT_DELETE",
     (--`!x:'a. !s. x IN s ==> (x INSERT (s DELETE x) = s)`--),
     PURE_REWRITE_TAC [EXTENSION,IN_INSERT,IN_DELETE] THEN
     REPEAT GEN_TAC THEN DISCH_THEN (fn th => GEN_TAC THEN MP_TAC th) THEN
     ASM_CASES_TAC (--`x':'a = x`--) THEN ASM_REWRITE_TAC[]);

(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)
val DELETE_INTER =
    store_thm
    ("DELETE_INTER",
     (--`!s t. !x:'a. (s DELETE x) INTER t = (s INTER t) DELETE x`--),
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [IN_INTER,IN_DELETE] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC,RES_TAC]);


(* --------------------------------------------------------------------- *)
(* A theorem from homeier@org.aero.uniblab (Peter Homeier)		 *)
(* --------------------------------------------------------------------- *)
val DISJOINT_DELETE_SYM =
    store_thm
    ("DISJOINT_DELETE_SYM",
     (--`!s t. !x:'a. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`--),
     REWRITE_TAC [DISJOINT_DEF,EXTENSION,NOT_IN_EMPTY] THEN
     REWRITE_TAC [IN_INTER,IN_DELETE,DE_MORGAN_THM] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN
     let val X = (--`X:'a`--)
     in DISCH_THEN (fn th => X_GEN_TAC X THEN STRIP_ASSUME_TAC (SPEC X th))
        THEN ASM_REWRITE_TAC []
     end);

(* ===================================================================== *)
(* Choice								 *)
(* ===================================================================== *)

val CHOICE_EXISTS =
    TAC_PROOF
    (([], (--`?CHOICE. !s:'a set. ~(s = EMPTY) ==> (CHOICE s) IN s`--)),
     REWRITE_TAC [EXTENSION,NOT_IN_EMPTY] THEN
     EXISTS_TAC (--`\s. @x:'a. x IN s`--) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REWRITE_TAC []);

val CHOICE_DEF = new_specification("CHOICE_DEF",["CHOICE"],CHOICE_EXISTS);
val _ = ot0 "CHOICE" "choice"

(* ===================================================================== *)
(* The REST of a set after removing a chosen element.			 *)
(* ===================================================================== *)

val REST_DEF =
    new_definition
    ("REST_DEF", (--`REST (s:'a set) = s DELETE (CHOICE s)`--));

val CHOICE_NOT_IN_REST =
    store_thm
    ("CHOICE_NOT_IN_REST",
     (--`!s:'a set. ~(CHOICE s IN REST s)`--),
     REWRITE_TAC [IN_DELETE,REST_DEF]);

val CHOICE_INSERT_REST = store_thm("CHOICE_INSERT_REST",
(--`!s:'a set. ~(s = EMPTY) ==> ((CHOICE s) INSERT (REST s) = s)`--),
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC [EXTENSION,IN_INSERT,REST_DEF,IN_DELETE] THEN
     GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [IMP_RES_TAC CHOICE_DEF THEN ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC [EXCLUDED_MIDDLE]]);

val REST_SUBSET =
    store_thm
    ("REST_SUBSET",
     (--`!s:'a set. (REST s) SUBSET s`--),
     REWRITE_TAC [SUBSET_DEF,REST_DEF,IN_DELETE] THEN REPEAT STRIP_TAC);

val lemma =
    TAC_PROOF(([], (--`(P /\ Q = P) = (P ==> Q)`--)),
    	      BOOL_CASES_TAC (--`P:bool`--) THEN REWRITE_TAC[]);

val REST_PSUBSET =
    store_thm
    ("REST_PSUBSET",
     (--`!s:'a set. ~(s = EMPTY) ==> (REST s) PSUBSET s`--),
     REWRITE_TAC [PSUBSET_DEF,REST_SUBSET] THEN
     GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC [EXTENSION,REST_DEF,IN_DELETE] THEN
     CONV_TAC NOT_FORALL_CONV THEN
     REWRITE_TAC [DE_MORGAN_THM,lemma,NOT_IMP] THEN
     EXISTS_TAC (--`CHOICE (s:'a set)`--) THEN
     IMP_RES_TAC CHOICE_DEF THEN
     ASM_REWRITE_TAC []);

(* ===================================================================== *)
(* Singleton set.							 *)
(* ===================================================================== *)

val SING_DEF =
    new_definition
    ("SING_DEF", (--`SING s = ?x:'a. s = {x}`--));
val _ = ot0 "SING" "singleton"

val SING =
    store_thm
    ("SING",
     (--`!x:'a. SING {x}`--),
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN REFL_TAC);
val _ = export_rewrites ["SING"]

val SING_EMPTY = store_thm(
  "SING_EMPTY",
  ``SING {} = F``,
  SRW_TAC [][SING_DEF]);
val _ = export_rewrites ["SING_EMPTY"]

val SING_INSERT = store_thm(
  "SING_INSERT",
  ``SING (x INSERT s) = (s = {}) \/ (s = {x})``,
  SRW_TAC [][SimpLHS, SING_DEF, EXTENSION] THEN
  SRW_TAC [][EQ_IMP_THM, DISJ_IMP_THM, FORALL_AND_THM, EXTENSION] THEN
  METIS_TAC []);
val _ = export_rewrites ["SING_INSERT"]

val SING_UNION = store_thm(
  "SING_UNION",
  ``SING (s UNION t) = SING s /\ (t = {}) \/ SING t /\ (s = {}) \/
                       SING s /\ SING t /\ (s = t)``,
  SRW_TAC [][SING_DEF, EXTENSION, EQ_IMP_THM, FORALL_AND_THM,
             DISJ_IMP_THM] THEN METIS_TAC []);

val IN_SING =
    store_thm
    ("IN_SING",
     (--`!x y. x IN {y:'a} = (x = y)`--),
     REWRITE_TAC [IN_INSERT,NOT_IN_EMPTY]);

val NOT_SING_EMPTY =
    store_thm
    ("NOT_SING_EMPTY",
     (--`!x:'a. ~({x} = EMPTY)`--),
     REWRITE_TAC [EXTENSION,IN_SING,NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN REWRITE_TAC[]);

val NOT_EMPTY_SING =
    store_thm
    ("NOT_EMPTY_SING",
     (--`!x:'a. ~(EMPTY = {x})`--),
     REWRITE_TAC [EXTENSION,IN_SING,NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN REWRITE_TAC[]);

val EQUAL_SING =
    store_thm
    ("EQUAL_SING",
     (--`!x:'a. !y. ({x} = {y}) = (x = y)`--),
     REWRITE_TAC [EXTENSION,IN_SING] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (fn th => REWRITE_TAC [SYM(SPEC_ALL th)]),
      DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC]);
val _ = export_rewrites ["EQUAL_SING"]

val DISJOINT_SING_EMPTY =
    store_thm
    ("DISJOINT_SING_EMPTY",
     (--`!x:'a. DISJOINT {x} EMPTY`--),
     REWRITE_TAC [DISJOINT_DEF,INTER_EMPTY]);

val INSERT_SING_UNION =
    store_thm
    ("INSERT_SING_UNION",
     (--`!s. !x:'a. x INSERT s = {x} UNION s`--),
     REWRITE_TAC [EXTENSION,IN_INSERT,IN_UNION,NOT_IN_EMPTY]);

val SING_DELETE =
    store_thm
    ("SING_DELETE",
    (--`!x:'a. {x} DELETE x = EMPTY`--),
    REWRITE_TAC [EXTENSION,NOT_IN_EMPTY,IN_DELETE,IN_INSERT] THEN
    PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [DE_MORGAN_THM,EXCLUDED_MIDDLE]);
val _ = export_rewrites ["SING_DELETE"]

val DELETE_EQ_SING =
    store_thm
    ("DELETE_EQ_SING",
     (--`!s. !x:'a. (x IN s) ==> ((s DELETE x = EMPTY) = (s = {x}))`--),
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     REWRITE_TAC [NOT_IN_EMPTY,DE_MORGAN_THM,IN_INSERT,IN_DELETE] THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN
      FIRST_ASSUM (fn th=>fn g => STRIP_ASSUME_TAC (SPEC (--`x':'a`--) th) g)
      THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN RES_TAC,
      let val th = PURE_ONCE_REWRITE_RULE [DISJ_SYM] EXCLUDED_MIDDLE
      in DISCH_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [th]
      end]);

val CHOICE_SING =
    store_thm
    ("CHOICE_SING",
     (--`!x:'a. CHOICE {x} = x`--),
     GEN_TAC THEN
     MP_TAC (MATCH_MP CHOICE_DEF (SPEC (--`x:'a`--) NOT_SING_EMPTY)) THEN
     REWRITE_TAC [IN_SING]);
val _ = export_rewrites ["CHOICE_SING"]

val REST_SING =
    store_thm
    ("REST_SING",
     (--`!x:'a. REST {x} = EMPTY`--),
     REWRITE_TAC [CHOICE_SING,REST_DEF,SING_DELETE]);
val _ = export_rewrites ["REST_SING"]

val SING_IFF_EMPTY_REST =
    store_thm
    ("SING_IFF_EMPTY_REST",
     (--`!s:'a set. SING s = ~(s = EMPTY) /\ (REST s = EMPTY)`--),
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC [REST_SING] THEN
      REWRITE_TAC [EXTENSION,NOT_IN_EMPTY,IN_INSERT] THEN
      CONV_TAC NOT_FORALL_CONV THEN
      EXISTS_TAC (--`x:'a`--) THEN REWRITE_TAC [],
      EXISTS_TAC (--`CHOICE s:'a`--) THEN
      IMP_RES_THEN (SUBST1_TAC o SYM) CHOICE_INSERT_REST THEN
      ASM_REWRITE_TAC [EXTENSION,IN_SING,CHOICE_SING]]);



(* ===================================================================== *)
(* The image of a function on a set.					 *)
(* ===================================================================== *)

val IMAGE_DEF =
    new_definition
    ("IMAGE_DEF", (--`IMAGE (f:'a->'b) s = {f x | x IN s}`--));

val _ = ot0 "IMAGE" "image"

val IN_IMAGE =
    store_thm
    ("IN_IMAGE",
     (--`!y:'b. !s f. (y IN (IMAGE f s)) = ?x:'a. (y = f x) /\ x IN s`--),
      PURE_ONCE_REWRITE_TAC [IMAGE_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);
val _ = export_rewrites ["IN_IMAGE"]

val IMAGE_IN =
    store_thm
    ("IMAGE_IN",
     (--`!x s. (x IN s) ==> !(f:'a->'b). f x IN (IMAGE f s)`--),
     PURE_ONCE_REWRITE_TAC [IN_IMAGE] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC (--`x:'a`--) THEN
     CONJ_TAC THENL [REFL_TAC, FIRST_ASSUM ACCEPT_TAC]);

val IMAGE_EMPTY =
     store_thm
     ("IMAGE_EMPTY",
      (--`!f:'a->'b. IMAGE f EMPTY = EMPTY`--),
      REWRITE_TAC[EXTENSION,IN_IMAGE,NOT_IN_EMPTY]);
val _ = export_rewrites ["IMAGE_EMPTY"]

val IMAGE_ID =
    store_thm
    ("IMAGE_ID",
     (--`!s:'a set. IMAGE (\x:'a.x) s = s`--),
     REWRITE_TAC [EXTENSION,IN_IMAGE] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ALL_TAC,EXISTS_TAC (--`x:'a`--)] THEN
     ASM_REWRITE_TAC []);

val o_THM = combinTheory.o_THM;

val IMAGE_COMPOSE =
    store_thm
    ("IMAGE_COMPOSE",
     (--`!f:'b->'c. !g:'a->'b. !s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`--),
     PURE_REWRITE_TAC [EXTENSION,IN_IMAGE,o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC (--`g (x':'a):'b`--) THEN
      CONJ_TAC THENL [ALL_TAC,EXISTS_TAC (--`x':'a`--)] THEN
      ASM_REWRITE_TAC [],
      EXISTS_TAC (--`x'':'a`--) THEN ASM_REWRITE_TAC[]]);

val IMAGE_INSERT =
    store_thm
    ("IMAGE_INSERT",
     (--`!(f:'a->'b) x s. IMAGE f (x INSERT s) = f x INSERT (IMAGE f s)`--),
     PURE_REWRITE_TAC [EXTENSION,IN_INSERT,IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ALL_TAC,DISJ2_TAC THEN EXISTS_TAC (--`x'':'a`--),
      EXISTS_TAC (--`x:'a`--),EXISTS_TAC (--`x'':'a`--)] THEN
     ASM_REWRITE_TAC[]);
val _ = export_rewrites ["IMAGE_INSERT"]

val IMAGE_EQ_EMPTY =
    store_thm
    ("IMAGE_EQ_EMPTY",
     (--`!s. !f:'a->'b. ((IMAGE f s) = EMPTY) = (s = EMPTY)`--),
     GEN_TAC THEN
     STRIP_ASSUME_TAC (SPEC (--`s:'a set`--) SET_CASES) THEN
     ASM_REWRITE_TAC [IMAGE_EMPTY,IMAGE_INSERT,NOT_INSERT_EMPTY]);
val _ = export_rewrites ["IMAGE_EQ_EMPTY"]

val IMAGE_DELETE = store_thm("IMAGE_DELETE",
(--`!(f:'a->'b) x s. ~(x IN s) ==> (IMAGE f (s DELETE x) = (IMAGE f s))`--),
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     PURE_REWRITE_TAC [EXTENSION,IN_DELETE,IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     EXISTS_TAC (--`x'':'a`--) THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST_ALL_TAC THEN RES_TAC);

val IMAGE_UNION = store_thm("IMAGE_UNION",
(--`!(f:'a->'b) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`--),
     PURE_REWRITE_TAC [EXTENSION,IN_UNION,IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [DISJ1_TAC,DISJ2_TAC,ALL_TAC,ALL_TAC] THEN
     EXISTS_TAC (--`x':'a`--) THEN ASM_REWRITE_TAC []);

val IMAGE_SUBSET =
    store_thm
    ("IMAGE_SUBSET",
     (--`!s t. (s SUBSET t) ==> !f:'a->'b. (IMAGE f s) SUBSET (IMAGE f t)`--),
     PURE_REWRITE_TAC [SUBSET_DEF,IN_IMAGE] THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     EXISTS_TAC (--`x':'a`--) THEN ASM_REWRITE_TAC []);

val IMAGE_INTER = store_thm ("IMAGE_INTER",
--`!(f:'a->'b) s t. IMAGE f (s INTER t) SUBSET (IMAGE f s INTER IMAGE f t)`--,
     REPEAT GEN_TAC THEN
     REWRITE_TAC [SUBSET_DEF,IN_IMAGE,IN_INTER] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC (--`x':'a`--) THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val IMAGE_11 = store_thm(
  "IMAGE_11",
  ``(!x y. (f x = f y) <=> (x = y)) ==>
    ((IMAGE f s1 = IMAGE f s2) <=> (s1 = s2))``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [EQ_IMP_THM] THEN
  SRW_TAC [boolSimps.DNF_ss][EXTENSION, EQ_IMP_THM]);

val IMAGE_CONG = store_thm(
"IMAGE_CONG",
``!f s f' s'. (s = s') /\ (!x. x IN s' ==> (f x = f' x))
==> (IMAGE f s = IMAGE f' s')``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])
val _ = DefnBase.export_cong"IMAGE_CONG"

(* ===================================================================== *)
(* Injective functions on a set.					 *)
(* ===================================================================== *)

val INJ_DEF =
    new_definition
    ("INJ_DEF",
     (--`INJ (f:'a->'b) s t =
          (!x. x IN s ==> (f x) IN t) /\
          (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y))`--));

val INJ_IFF = store_thm(
  "INJ_IFF",
  ``INJ (f:'a -> 'b) s t <=>
      (!x. x IN s ==> f x IN t) /\
      (!x y. x IN s /\ y IN s ==> ((f x = f y) <=> (x = y)))``,
  METIS_TAC[INJ_DEF]);

val INJ_ID =
    store_thm
    ("INJ_ID",
     (--`!s. INJ (\x:'a.x) s s`--),
     PURE_ONCE_REWRITE_TAC [INJ_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC);

val INJ_COMPOSE =
    store_thm
    ("INJ_COMPOSE",
     (--`!f:'a->'b. !g:'b->'c.
      !s t u. (INJ f s t  /\ INJ g t u) ==> INJ (g o f) s u`--),
     PURE_REWRITE_TAC [INJ_DEF,o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC,
      RES_TAC THEN RES_TAC]);

val INJ_EMPTY =
    store_thm
    ("INJ_EMPTY",
     (--`!f:'a->'b. (!s. INJ f {} s) /\ (!s. INJ f s {} = (s = {}))`--),
     REWRITE_TAC [INJ_DEF,NOT_IN_EMPTY,EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC);

val INJ_DELETE = Q.store_thm
("INJ_DELETE",
 `!s t f. INJ f s t ==> !e. e IN s ==> INJ f (s DELETE e) (t DELETE (f e))`,
RW_TAC bool_ss [INJ_DEF, DELETE_DEF] THENL
[`~(e = x)` by FULL_SIMP_TAC bool_ss
                 [DIFF_DEF,DIFF_INSERT, DIFF_EMPTY, IN_DELETE] THEN
  FULL_SIMP_TAC bool_ss [DIFF_DEF,DIFF_INSERT, DIFF_EMPTY, IN_DELETE] THEN
  METIS_TAC [],
METIS_TAC [IN_DIFF]]);

val INJ_INSERT = store_thm(
"INJ_INSERT",
``!f x s t. INJ f (x INSERT s) t =
   INJ f s t /\ (f x) IN t /\
   (!y. y IN s /\ (f x = f y) ==> (x = y))``,
SRW_TAC[][INJ_DEF] THEN METIS_TAC[])

val INJ_SUBSET = store_thm(
"INJ_SUBSET",
``!f s t s0 t0. INJ f s t /\ s0 SUBSET s /\ t SUBSET t0 ==> INJ f s0 t0``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

(* ===================================================================== *)
(* Surjective functions on a set.					 *)
(* ===================================================================== *)

val SURJ_DEF =
    new_definition
    ("SURJ_DEF",
     (--`SURJ (f:'a->'b) s t =
           (!x. x IN s ==> (f x) IN t) /\
           (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`--));

val SURJ_ID =
    store_thm
    ("SURJ_ID",
     (--`!s. SURJ (\x:'a.x) s s`--),
     PURE_ONCE_REWRITE_TAC [SURJ_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC (--`x:'a`--) THEN
     ASM_REWRITE_TAC []);

val SURJ_COMPOSE =
    store_thm
    ("SURJ_COMPOSE",
     (--`!f:'a->'b. !g:'b->'c.
      !s t u. (SURJ f s t  /\ SURJ g t u) ==> SURJ (g o f) s u`--),
     PURE_REWRITE_TAC [SURJ_DEF,o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC,
      RES_TAC THEN RES_TAC THEN
      EXISTS_TAC (--`y'':'a`--) THEN
      ASM_REWRITE_TAC []]);

val SURJ_EMPTY = store_thm ("SURJ_EMPTY",
--`!f:'a->'b. (!s. SURJ f {} s = (s = {})) /\ (!s. SURJ f s {} = (s = {}))`--,
     REWRITE_TAC [SURJ_DEF,NOT_IN_EMPTY,EXTENSION]);

val IMAGE_SURJ =
    store_thm
    ("IMAGE_SURJ",
     (--`!f:'a->'b. !s t. SURJ f s t = ((IMAGE f s) = t)`--),
     PURE_REWRITE_TAC [SURJ_DEF,EXTENSION,IN_IMAGE] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
      [RES_TAC THEN ASM_REWRITE_TAC [],
       MAP_EVERY PURE_ONCE_REWRITE_TAC [[CONJ_SYM],[EQ_SYM_EQ]] THEN
       FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC],
      DISCH_THEN (ASSUME_TAC o CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)) THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
      [EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC [],
       EXISTS_TAC (--`x':'a`--) THEN ASM_REWRITE_TAC []]]);

val SURJ_IMAGE = store_thm(
  "SURJ_IMAGE",
  ``SURJ f s (IMAGE f s)``,
  REWRITE_TAC[IMAGE_SURJ]);
val _ = export_rewrites ["SURJ_IMAGE"]

val SURJ_INJ_INV = store_thm(
  "SURJ_INJ_INV",
  ``SURJ f s t ==> ?g. INJ g t s /\ !y. y IN t ==> (f (g y) = y)``,
  SIMP_TAC (srw_ss())[SURJ_DEF, INJ_DEF] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
                (ASSUME_TAC o
                 SIMP_RULE (srw_ss() ++ DNF_ss)
                           [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM])) THEN
  METIS_TAC[]);

(* ===================================================================== *)
(* Bijective functions on a set.					 *)
(* ===================================================================== *)

val BIJ_DEF =
    new_definition
    ("BIJ_DEF",
     (--`BIJ (f:'a->'b) s t = INJ f s t /\ SURJ f s t`--));

val BIJ_ID =
    store_thm
    ("BIJ_ID",
     (--`!s. BIJ (\x:'a.x) s s`--),
     REWRITE_TAC [BIJ_DEF,INJ_ID,SURJ_ID]);

val BIJ_EMPTY = store_thm("BIJ_EMPTY",
(--`!f:'a->'b. (!s. BIJ f {} s = (s = {})) /\ (!s. BIJ f s {} = (s = {}))`--),
     REWRITE_TAC [BIJ_DEF,INJ_EMPTY,SURJ_EMPTY]);

val BIJ_COMPOSE =
    store_thm
    ("BIJ_COMPOSE",
     (--`!f:'a->'b. !g:'b->'c.
      !s t u. (BIJ f s t  /\ BIJ g t u) ==> BIJ (g o f) s u`--),
     PURE_REWRITE_TAC [BIJ_DEF] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC INJ_COMPOSE,IMP_RES_TAC SURJ_COMPOSE]);

val BIJ_DELETE = Q.store_thm
("BIJ_DELETE",
 `!s t f. BIJ f s t ==> !e. e IN s ==> BIJ f (s DELETE e) (t DELETE (f e))`,
RW_TAC bool_ss [BIJ_DEF, SURJ_DEF, INJ_DELETE, DELETE_DEF, INJ_DEF] THENL
[FULL_SIMP_TAC bool_ss [DIFF_DEF,DIFF_INSERT, DIFF_EMPTY, IN_DELETE] THEN
  METIS_TAC [],
  `?y. y IN s /\ (f y = x)` by METIS_TAC [IN_DIFF] THEN
  Q.EXISTS_TAC `y` THEN RW_TAC bool_ss [] THEN
  `~(y = e)` by (FULL_SIMP_TAC bool_ss [DIFF_DEF, DIFF_INSERT, DIFF_EMPTY,
                                       IN_DELETE] THEN
                 METIS_TAC [IN_DIFF]) THEN
  FULL_SIMP_TAC bool_ss [DIFF_DEF, DIFF_INSERT, DIFF_EMPTY, IN_DELETE]]);

(* ===================================================================== *)
(* Left and right inverses.						 *)
(* ===================================================================== *)

val lemma1 = TAC_PROOF(([],
(--`!(f:'a->'b) s.
      (!x y. x IN s /\ y IN s ==> (f x = f y) ==> (x = y)) =
      (!y. y IN s ==> !x.((x IN s /\ (f x = f y))=(y IN s /\ (x = y))))`--)),
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     RES_TAC THEN ASM_REWRITE_TAC []);

val lemma2 = TAC_PROOF (([],
(--`!f:'a->'b. !s. ?g. !t. INJ f s t ==> !x:'a. x IN s ==> (g(f x) = x)`--)),
     REPEAT GEN_TAC THEN PURE_REWRITE_TAC [INJ_DEF,lemma1] THEN
     EXISTS_TAC (--`\y:'b. @x:'a. x IN s /\ (f x = y)`--) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN (RES_THEN (fn th => REWRITE_TAC [th])) THEN
     ASM_REWRITE_TAC [] THEN CONV_TAC SELECT_CONV THEN
     EXISTS_TAC (--`x:'a`--) THEN REFL_TAC);

(* --------------------------------------------------------------------- *)
(* LINV_DEF:								 *)
(*   |- !f s t. INJ f s t ==> (!x. x IN s ==> (LINV f s(f x) = x))	 *)
(* --------------------------------------------------------------------- *)

val LINV_DEF =
   let val th1 = CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) lemma2
       val th2 = CONV_RULE SKOLEM_CONV th1
   in
      new_specification("LINV_DEF",["LINV"],th2)
   end;

val BIJ_LINV_INV = Q.store_thm (
"BIJ_LINV_INV",
`!f s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)`,
RW_TAC bool_ss [BIJ_DEF] THEN
IMP_RES_TAC LINV_DEF THEN FULL_SIMP_TAC bool_ss [INJ_DEF, SURJ_DEF] THEN
METIS_TAC []);

val BIJ_LINV_BIJ = Q.store_thm (
"BIJ_LINV_BIJ",
`!f s t. BIJ f s t ==> BIJ (LINV f s) t s`,
RW_TAC bool_ss [BIJ_DEF] THEN
IMP_RES_TAC LINV_DEF THEN FULL_SIMP_TAC bool_ss [INJ_DEF, SURJ_DEF] THEN
METIS_TAC []);

val BIJ_IFF_INV = Q.store_thm(
"BIJ_IFF_INV",
`!f s t. BIJ f s t =
  (!x. x IN s ==> f x IN t) /\
  ?g. (!x. x IN t ==> g x IN s) /\
      (!x. x IN s ==> (g (f x) = x)) /\
      (!x. x IN t ==> (f (g x) = x))`,
REPEAT GEN_TAC THEN
EQ_TAC THEN STRIP_TAC THEN1 (
  CONJ_TAC THEN1 METIS_TAC [BIJ_DEF,INJ_DEF] THEN
  Q.EXISTS_TAC `LINV f s` THEN
  IMP_RES_TAC BIJ_LINV_BIJ THEN
  CONJ_TAC THEN1 METIS_TAC [BIJ_DEF,INJ_DEF] THEN
  CONJ_TAC THEN1 METIS_TAC [BIJ_DEF,LINV_DEF] THEN
  METIS_TAC [BIJ_LINV_INV] ) THEN
SRW_TAC [][BIJ_DEF,INJ_DEF,SURJ_DEF] THEN
METIS_TAC []);

val BIJ_INSERT = store_thm(
  "BIJ_INSERT",
  ``BIJ f (e INSERT s) t <=>
      e NOTIN s /\ f e IN t /\ BIJ f s (t DELETE f e) \/
      e IN s /\ BIJ f s t``,
  Cases_on `e IN s` THEN1
    (SRW_TAC [][ABSORPTION |> SPEC_ALL |> EQ_IMP_RULE |> #1]) THEN
  SRW_TAC [][] THEN SRW_TAC [][BIJ_IFF_INV] THEN EQ_TAC THENL [
    SRW_TAC [][DISJ_IMP_THM, FORALL_AND_THM] THEN METIS_TAC [],
    SRW_TAC [][DISJ_IMP_THM, FORALL_AND_THM] THEN
    Q.EXISTS_TAC `\x. if x = f e then e else g x` THEN
    SRW_TAC [][]
  ]);

val lemma3 = TAC_PROOF(([],
(--`!f:'a->'b. !s. ?g. !t. SURJ f s t ==> !x:'b. x IN t ==> (f(g x) = x)`--)),
     REPEAT GEN_TAC THEN PURE_REWRITE_TAC [SURJ_DEF] THEN
     EXISTS_TAC (--`\y:'b. @x:'a. x IN s /\ (f x = y)`--) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     (fn (A,g) =>
       let val tm = mk_conj(Term`^(rand(lhs g)) IN s`, g)
       in SUBGOAL_THEN tm (fn th => ACCEPT_TAC(CONJUNCT2 th))(A,g)
       end)
     THEN CONV_TAC SELECT_CONV THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC);

(* --------------------------------------------------------------------- *)
(* RINV_DEF:								 *)
(*   |- !f s t. SURJ f s t ==> (!x. x IN t ==> (f(RINV f s x) = x))      *)
(* --------------------------------------------------------------------- *)

val RINV_DEF =
    let val th1 = CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) lemma3
        val th2 = CONV_RULE SKOLEM_CONV th1
    in
         new_specification("RINV_DEF",["RINV"],th2)
    end;

(* ===================================================================== *)
(* Finiteness								 *)
(* ===================================================================== *)

val FINITE_DEF =
 new_definition
 ("FINITE_DEF",
  (--`!s:'a set.
    FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s`--));
val _ = ot0 "FINITE" "finite"

val FINITE_EMPTY =
    store_thm
    ("FINITE_EMPTY",
     (--`FINITE (EMPTY:'a set)`--),
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     REPEAT STRIP_TAC);

val FINITE_INSERT =
    TAC_PROOF
    (([], (--`!s. FINITE s ==> !x:'a. FINITE (x INSERT s)`--)),
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     REPEAT STRIP_TAC THEN SPEC_TAC ((--`x:'a`--),(--`x:'a`--)) THEN
     REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
     CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val SIMPLE_FINITE_INDUCT =
    TAC_PROOF
    (([], (--`!P. P EMPTY /\ (!s. P s ==> (!e:'a. P(e INSERT s)))
                ==>
               !s. FINITE s ==> P s`--)),
     GEN_TAC THEN STRIP_TAC THEN
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []);

val lemma =
  let val tac = ASM_CASES_TAC (--`P:bool`--) THEN ASM_REWRITE_TAC[]
      val lem = TAC_PROOF(([],(--`(P ==> P /\ Q) = (P ==> Q)`--)), tac)
      val th1 = SPEC (--`\s:'a set. FINITE s /\ P s`--)
                     SIMPLE_FINITE_INDUCT
  in REWRITE_RULE [lem,FINITE_EMPTY] (BETA_RULE th1)
  end;

val FINITE_INDUCT = store_thm("FINITE_INDUCT",
  ``!P. P {} /\ (!s. FINITE s /\ P s ==> (!e. ~(e IN s) ==> P(e INSERT s))) ==>
    !s:'a set. FINITE s ==> P s``,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THENL
  [IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT,
   ASM_CASES_TAC (--`(e:'a) IN s`--) THENL
   [IMP_RES_THEN SUBST1_TAC ABSORPTION, RES_TAC] THEN
   ASM_REWRITE_TAC []]);

val _ = IndDefLib.export_rule_induction "FINITE_INDUCT";

(* --------------------------------------------------------------------- *)
(* Load the set induction tactic in...                                   *)
(* --------------------------------------------------------------------- *)

val SET_INDUCT_TAC = PSet_ind.SET_INDUCT_TAC FINITE_INDUCT;

val set_tyinfo = TypeBasePure.mk_nondatatype_info
                      (``:'a set``,
                       {nchotomy = SOME SET_CASES,
                        induction= SOME FINITE_INDUCT,
                        size=NONE,
                        encode=NONE});

val _ = TypeBase.write [set_tyinfo];

val FINITE_DELETE =
    TAC_PROOF
    (([], --`!s. FINITE s ==> !x:'a. FINITE (s DELETE x)`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DELETE,FINITE_EMPTY],
      PURE_ONCE_REWRITE_TAC [DELETE_INSERT] THEN
      REPEAT STRIP_TAC THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC,
       FIRST_ASSUM (fn th => fn g => ASSUME_TAC (SPEC (--`x:'a`--) th) g) THEN
       IMP_RES_TAC FINITE_INSERT THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);

val INSERT_FINITE =
    TAC_PROOF
    (([], (--`!x:'a. !s. FINITE(x INSERT s) ==> FINITE s`--)),
     REPEAT GEN_TAC THEN ASM_CASES_TAC (--`(x:'a) IN s`--) THENL
     [IMP_RES_TAC ABSORPTION THEN ASM_REWRITE_TAC [],
      DISCH_THEN (MP_TAC o SPEC (--`x:'a`--) o  MATCH_MP FINITE_DELETE) THEN
      REWRITE_TAC [DELETE_INSERT] THEN
      IMP_RES_TAC DELETE_NON_ELEMENT THEN ASM_REWRITE_TAC[]]);

val FINITE_INSERT =
    store_thm
    ("FINITE_INSERT",
     (--`!x:'a. !s. FINITE(x INSERT s) = FINITE s`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MATCH_ACCEPT_TAC INSERT_FINITE,
      DISCH_THEN (MATCH_ACCEPT_TAC o MATCH_MP FINITE_INSERT)]);

val _ = export_rewrites ["FINITE_EMPTY", "FINITE_INSERT"]

val DELETE_FINITE =
    TAC_PROOF
    (([], (--`!x:'a. !s. FINITE (s DELETE x) ==> FINITE s`--)),
     REPEAT GEN_TAC THEN ASM_CASES_TAC (--`(x:'a) IN s`--) THEN
     DISCH_TAC THENL
     [IMP_RES_THEN (SUBST1_TAC o SYM) INSERT_DELETE THEN
      ASM_REWRITE_TAC [FINITE_INSERT],
      IMP_RES_THEN (SUBST1_TAC o SYM) DELETE_NON_ELEMENT THEN
      FIRST_ASSUM ACCEPT_TAC]);


val FINITE_DELETE =
    store_thm
    ("FINITE_DELETE",
     (--`!x:'a. !s. FINITE(s DELETE x) = FINITE s`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MATCH_ACCEPT_TAC DELETE_FINITE,
      DISCH_THEN (MATCH_ACCEPT_TAC o MATCH_MP FINITE_DELETE)]);

val FINITE_REST =
    store_thm
    ("FINITE_REST",
     (--`!s:'a set. FINITE s ==> FINITE (REST s)`--),
     REWRITE_TAC [REST_DEF, FINITE_DELETE]);

val UNION_FINITE = prove(
  --`!s:'a set. FINITE s ==> !t. FINITE t ==> FINITE (s UNION t)`--,
  SET_INDUCT_TAC THENL [
    REWRITE_TAC [UNION_EMPTY],
    SET_INDUCT_TAC THENL [
      IMP_RES_TAC FINITE_INSERT THEN ASM_REWRITE_TAC [UNION_EMPTY],
      `(e INSERT s) UNION (e' INSERT s') =
          s UNION (e INSERT e' INSERT s')` by
         SIMP_TAC bool_ss [IN_UNION, EXTENSION, IN_INSERT, NOT_IN_EMPTY,
                           EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM] THEN
      ASM_SIMP_TAC bool_ss [FINITE_INSERT, FINITE_EMPTY]
    ]
  ]);

val FINITE_UNION_LEMMA = TAC_PROOF(([],
--`!s:'a set. FINITE s ==> !t. FINITE (s UNION t) ==> FINITE t`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY],
      GEN_TAC THEN ASM_REWRITE_TAC [INSERT_UNION] THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC,
       DISCH_THEN (MP_TAC o MATCH_MP INSERT_FINITE) THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);

val FINITE_UNION = prove(
  --`!s:'a set. !t. FINITE(s UNION t) ==> (FINITE s /\ FINITE t)`--,
  REPEAT STRIP_TAC THEN IMP_RES_THEN MATCH_MP_TAC FINITE_UNION_LEMMA THEN
  PROVE_TAC [UNION_COMM, UNION_ASSOC, UNION_IDEMPOT]);

val FINITE_UNION =
    store_thm
    ("FINITE_UNION",
     (--`!s:'a set. !t. FINITE(s UNION t) = FINITE s /\ FINITE t`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN IMP_RES_TAC FINITE_UNION,
      REPEAT STRIP_TAC THEN IMP_RES_TAC UNION_FINITE]);

val _ = export_rewrites ["FINITE_DELETE", "FINITE_UNION"]

val INTER_FINITE =
    store_thm
    ("INTER_FINITE",
     (--`!s:'a set. FINITE s ==> !t. FINITE (s INTER t)`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [INTER_EMPTY,FINITE_EMPTY],
      REWRITE_TAC [INSERT_INTER] THEN GEN_TAC THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM (fn th => fn g => ASSUME_TAC (SPEC (--`t:'a set`--) th) g
                                     handle _ => NO_TAC g) THEN
       IMP_RES_TAC FINITE_INSERT THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC,
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);

val SUBSET_FINITE =
    store_thm
    ("SUBSET_FINITE",
     (--`!s:'a set. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`--),
     SET_INDUCT_TAC THENL
     [PURE_ONCE_REWRITE_TAC [SUBSET_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [FINITE_EMPTY],
      GEN_TAC THEN ASM_CASES_TAC (--`(e:'a) IN t`--) THENL
      [REWRITE_TAC [SUBSET_INSERT_DELETE] THEN
       STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC DELETE_FINITE,
       IMP_RES_TAC SUBSET_INSERT THEN ASM_REWRITE_TAC []]]);

val SUBSET_FINITE_I = store_thm(
  "SUBSET_FINITE_I",
  ``!s t. FINITE s /\ t SUBSET s ==> FINITE t``,
  METIS_TAC [SUBSET_FINITE]);


val PSUBSET_FINITE =
    store_thm
    ("PSUBSET_FINITE",
     (--`!s:'a set. FINITE s ==> (!t. t PSUBSET s ==> FINITE t)`--),
     PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC SUBSET_FINITE);

val FINITE_DIFF =
    store_thm
    ("FINITE_DIFF",
     (--`!s:'a set. FINITE s ==> !t. FINITE(s DIFF t)`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DIFF,FINITE_EMPTY],
      ASM_REWRITE_TAC [INSERT_DIFF] THEN
      GEN_TAC THEN COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC,
       FIRST_ASSUM (fn th => fn g => ASSUME_TAC (SPEC (--`t:'a set`--)th) g)
       THEN IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT]]);
val _ = export_rewrites ["FINITE_DIFF"]

val FINITE_DIFF_down = Q.store_thm
("FINITE_DIFF_down",
  `!P Q. FINITE (P DIFF Q) /\ FINITE Q ==> FINITE P`,
  Q_TAC SUFF_TAC `!Q. FINITE Q ==> !P. FINITE (P DIFF Q) ==> FINITE P` THEN1
    PROVE_TAC [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][DIFF_EMPTY] THEN
  PROVE_TAC [DIFF_INSERT, FINITE_DELETE]);

val FINITE_SING =
    store_thm
    ("FINITE_SING",
     (--`!x:'a. FINITE {x}`--),
     GEN_TAC THEN MP_TAC FINITE_EMPTY THEN
     SUBST1_TAC (SYM (SPEC (--`x:'a`--) SING_DELETE)) THEN
     DISCH_TAC THEN IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT);

val SING_FINITE =
    store_thm
    ("SING_FINITE",
     (--`!s:'a set. SING s ==> FINITE s`--),
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN DISCH_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
     MATCH_ACCEPT_TAC FINITE_SING);
val _ = export_rewrites ["SING_FINITE"]

val IMAGE_FINITE =
    store_thm
    ("IMAGE_FINITE",
     (--`!s. FINITE s ==> !f:'a->'b. FINITE(IMAGE f s)`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [IMAGE_EMPTY,FINITE_EMPTY],
      ASM_REWRITE_TAC [IMAGE_INSERT,FINITE_INSERT]]);

val FINITELY_INJECTIVE_IMAGE_FINITE = Q.store_thm
("FINITELY_INJECTIVE_IMAGE_FINITE",
  `!f. (!x. FINITE { y | x = f y }) ==> !s. FINITE (IMAGE f s) = FINITE s`,
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM, IMAGE_FINITE] THEN
  Q_TAC SUFF_TAC `!Q. FINITE Q ==> !P. (IMAGE f P = Q) ==> FINITE P` THEN1
     SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][IMAGE_EQ_EMPTY] THEN
  `Q = IMAGE f (P DIFF { y | e = f y})`
     by (POP_ASSUM MP_TAC THEN
         SRW_TAC [][EXTENSION, IN_IMAGE, GSPECIFICATION] THEN
         PROVE_TAC []) THEN
  `FINITE (P DIFF { y | e = f y})` by PROVE_TAC [] THEN
  METIS_TAC [FINITE_DIFF_down]);

val INJECTIVE_IMAGE_FINITE = Q.store_thm
("INJECTIVE_IMAGE_FINITE",
  `!f. (!x y. (f x = f y) = (x = y)) ==>
       !s. FINITE (IMAGE f s) = FINITE s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITELY_INJECTIVE_IMAGE_FINITE THEN
  GEN_TAC THEN Cases_on `?e. x = f e` THENL [
    POP_ASSUM STRIP_ASSUME_TAC THEN
    Q_TAC SUFF_TAC `{y | x = f y} = {e}` THEN1 SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss()) [GSPECIFICATION, EXTENSION] THEN PROVE_TAC [],
    Q_TAC SUFF_TAC `{y | x = f y} = {}` THEN1 SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [EXTENSION, GSPECIFICATION]
  ]);
val _ = export_rewrites ["INJECTIVE_IMAGE_FINITE"]

val lem = Q.prove
(`!t. FINITE t ==> !s f. INJ f s t ==> FINITE s`,
 SET_INDUCT_TAC
  THEN RW_TAC bool_ss [INJ_EMPTY,FINITE_EMPTY]
  THEN Cases_on `?a. a IN s' /\ (f a = e)`
  THEN POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE bool_ss []) THENL
     [RW_TAC bool_ss []
       THEN IMP_RES_TAC INJ_DELETE
       THEN FULL_SIMP_TAC bool_ss [DELETE_INSERT]
       THEN METIS_TAC [DELETE_NON_ELEMENT,FINITE_DELETE],
      Q.PAT_ASSUM `INJ x y z` MP_TAC
       THEN RW_TAC bool_ss [INJ_DEF]
       THEN `!x. x IN s' ==> f x IN s` by METIS_TAC [IN_INSERT]
       THEN `INJ f s' s` by METIS_TAC [INJ_DEF]
       THEN METIS_TAC[]]);

val FINITE_INJ = Q.store_thm
("FINITE_INJ",
 `!(f:'a->'b) s t. INJ f s t /\ FINITE t ==> FINITE s`,
 METIS_TAC [lem]);

val REL_RESTRICT_DEF = new_definition(
  "REL_RESTRICT_DEF",
  ``REL_RESTRICT R s x y = x IN s /\ y IN s /\ R x y``);

val REL_RESTRICT_EMPTY = store_thm(
  "REL_RESTRICT_EMPTY",
  ``REL_RESTRICT R {} = REMPTY``,
  SRW_TAC [][REL_RESTRICT_DEF, FUN_EQ_THM]);
val _ = export_rewrites ["REL_RESTRICT_EMPTY"]

val REL_RESTRICT_SUBSET = store_thm(
  "REL_RESTRICT_SUBSET",
  ``s1 SUBSET s2 ==> REL_RESTRICT R s1 RSUBSET REL_RESTRICT R s2``,
  SRW_TAC [][relationTheory.RSUBSET, REL_RESTRICT_DEF, SUBSET_DEF]);

(* =====================================================================*)
(* Cardinality 								*)
(* =====================================================================*)

(* --------------------------------------------------------------------- *)
(* card_rel_def: defining equations for a relation `R s n`, which means  *)
(* that the finite s has cardinality n.				 	 *)
(* --------------------------------------------------------------------- *)

val card_rel_def =
    (--`(!s. R s 0 = (s = EMPTY)) /\
      (!s n. R s (SUC n) = ?x:'a. x IN s /\ R (s DELETE x) n)`--);

(* ---------------------------------------------------------------------*)
(* Prove that such a relation exists.					*)
(* ---------------------------------------------------------------------*)

val CARD_REL_EXISTS =  prove_rec_fn_exists num_Axiom card_rel_def;

(* ---------------------------------------------------------------------*)
(* Now, prove that it doesn't matter which element we delete		*)
(* Proof modified for Version 12 IMP_RES_THEN		 [TFM 91.01.23]	*)
(* ---------------------------------------------------------------------*)

val CARD_REL_DEL_LEMMA =
    TAC_PROOF
    ((strip_conj card_rel_def,
      (--`!(n:num) s (x:'a).
       x IN s ==>
       R (s DELETE x) n  ==>
      !y:'a. y IN s ==> R (s DELETE y) n`--)),
     INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      IMP_RES_TAC DELETE_EQ_SING THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_SING] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SING_DELETE],
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      let val th = (SPEC (--`y:'a = x'`--) EXCLUDED_MIDDLE)
      in DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th
      end
      THENL
      [MP_TAC (SPECL [(--`s:'a set`--),(--`x:'a`--),(--`x':'a`--)]
                     IN_DELETE_EQ) THEN
       ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
       PURE_ONCE_REWRITE_TAC [DELETE_COMM] THEN
       EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
       let val th = (SPEC (--`x:'a = y`--) EXCLUDED_MIDDLE)
       in DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th
       end
       THENL
       [EXISTS_TAC (--`x':'a`--) THEN ASM_REWRITE_TAC [],
        EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC [IN_DELETE] THEN
        RES_THEN (TRY o IMP_RES_THEN ASSUME_TAC) THEN
        PURE_ONCE_REWRITE_TAC [DELETE_COMM] THEN
	FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_DELETE] THEN
	CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN FIRST_ASSUM ACCEPT_TAC]]]);


(* --------------------------------------------------------------------- *)
(* So `R s` specifies a unique number.				         *)
(* --------------------------------------------------------------------- *)

val CARD_REL_UNIQUE =
    TAC_PROOF
    ((strip_conj card_rel_def,
      (--`!n:num. !s:'a set. R s n ==> (!m. R s m ==> (n = m))`--)),
     INDUCT_TAC THEN ASM_REWRITE_TAC [] THENL
     [GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THENL
      [STRIP_TAC THEN REFL_TAC, ASM_REWRITE_TAC[NOT_SUC,NOT_IN_EMPTY]],
      GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
      [ASM_REWRITE_TAC [NOT_SUC,SYM(SPEC_ALL MEMBER_NOT_EMPTY)] THEN
       EXISTS_TAC (--`x:'a`--) THEN FIRST_ASSUM ACCEPT_TAC,
       ASM_REWRITE_TAC [INV_SUC_EQ] THEN STRIP_TAC THEN
       IMP_RES_TAC CARD_REL_DEL_LEMMA THEN RES_TAC]]);

(* --------------------------------------------------------------------- *)
(* Now, ?n. R s n if s is finite.					*)
(* --------------------------------------------------------------------- *)

val CARD_REL_EXISTS_LEMMA = TAC_PROOF
((strip_conj card_rel_def,
 (--`!s:'a set. FINITE s ==> ?n:num. R s n`--)),
     SET_INDUCT_TAC THENL
     [EXISTS_TAC (--`0`--) THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM (fn th => fn g => CHOOSE_THEN ASSUME_TAC th g) THEN
      EXISTS_TAC (--`SUC n`--) THEN ASM_REWRITE_TAC [] THEN
      EXISTS_TAC (--`e:'a`--) THEN IMP_RES_TAC DELETE_NON_ELEMENT THEN
      ASM_REWRITE_TAC [DELETE_INSERT,IN_INSERT]]);

(* ---------------------------------------------------------------------*)
(* So (@n. R s n) = m iff R s m        (\s.@n.R s n defines a function)	*)
(* Proof modified for Version 12 IMP_RES_THEN		 [TFM 91.01.23]	*)
(* ---------------------------------------------------------------------*)

val CARD_REL_THM =
    TAC_PROOF
    ((strip_conj card_rel_def,
     (--`!m s. FINITE s ==> (((@n:num. R (s:'a set) n) = m) = R s m)`--)),
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC CARD_REL_EXISTS_LEMMA THEN
     EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
      EXISTS_TAC (--`n:num`--) THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      STRIP_TAC THEN
      IMP_RES_THEN ASSUME_TAC CARD_REL_UNIQUE THEN
      CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      CONV_TAC SELECT_CONV THEN
      EXISTS_TAC (--`n:num`--) THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

(* ---------------------------------------------------------------------*)
(* Now, prove the existence of the required cardinality function.	*)
(* ---------------------------------------------------------------------*)

val CARD_EXISTS = TAC_PROOF(([],
(--` ?CARD.
       (CARD EMPTY = 0) /\
       (!s. FINITE s ==>
       !x:'a. CARD(x INSERT s) = (if x IN s then CARD s else SUC(CARD s)))`--)),
     STRIP_ASSUME_TAC CARD_REL_EXISTS THEN
     EXISTS_TAC (--`\s:'a set. @n:num. R s n`--) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [ASSUME_TAC FINITE_EMPTY THEN IMP_RES_TAC CARD_REL_THM THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_THEN SUBST1_TAC ABSORPTION THEN REFL_TAC,
       IMP_RES_THEN (ASSUME_TAC o SPEC (--`x:'a`--)) FINITE_INSERT THEN
       IMP_RES_THEN (TRY o MATCH_MP_TAC) CARD_REL_THM THEN
       ASM_REWRITE_TAC [] THEN EXISTS_TAC (--`x:'a`--) THEN
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       ASM_REWRITE_TAC [IN_INSERT,DELETE_INSERT] THEN
       CONV_TAC SELECT_CONV THEN
       IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) CARD_REL_EXISTS_LEMMA]]);

(* ---------------------------------------------------------------------*)
(* Finally, introduce the CARD function via a constant specification.	*)
(* ---------------------------------------------------------------------*)

val CARD_DEF = new_specification ("CARD_DEF", ["CARD"], CARD_EXISTS);

(* ---------------------------------------------------------------------*)
(* Various cardinality results.						*)
(* ---------------------------------------------------------------------*)

val CARD_EMPTY = save_thm("CARD_EMPTY",CONJUNCT1 CARD_DEF);
val _ = export_rewrites ["CARD_EMPTY"]

val CARD_INSERT = save_thm("CARD_INSERT",CONJUNCT2 CARD_DEF);
val _ = export_rewrites ["CARD_INSERT"]

val CARD_EQ_0 =
    store_thm
    ("CARD_EQ_0",
     (--`!s:'a set. FINITE s ==> ((CARD s = 0) = (s = EMPTY))`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_EMPTY],
      IMP_RES_TAC CARD_INSERT THEN
      ASM_REWRITE_TAC [NOT_INSERT_EMPTY,NOT_SUC]]);

val CARD_DELETE =
    store_thm
    ("CARD_DELETE",
     (--`!s. FINITE s ==>
          !x:'a. CARD(s DELETE x) = if x IN s then CARD s - 1 else CARD s`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DELETE,NOT_IN_EMPTY],
      PURE_REWRITE_TAC [DELETE_INSERT,IN_INSERT] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x:'a = e`--) THENL
      [IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [SUC_SUB1],
       SUBST1_TAC (SPECL [(--`e:'a`--),(--`x:'a`--)] EQ_SYM_EQ) THEN
       IMP_RES_THEN (ASSUME_TAC o SPEC (--`x:'a`--)) FINITE_DELETE THEN
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [IN_DELETE,SUC_SUB1] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       STRIP_ASSUME_TAC (SPEC (--`CARD(s:'a set)`--) num_CASES) THENL
       [let fun tac th g = SUBST_ALL_TAC th g handle _ => ASSUME_TAC th g
        in REPEAT_GTCL IMP_RES_THEN tac CARD_EQ_0
        end THEN IMP_RES_TAC NOT_IN_EMPTY,
	ASM_REWRITE_TAC [SUC_SUB1]]]]);


val lemma1 =
    TAC_PROOF
    (([], (--`!n m. (SUC n <= SUC m) = (n <= m)`--)),
     REWRITE_TAC [LESS_OR_EQ,INV_SUC_EQ,LESS_MONO_EQ]);

val lemma2 =
    TAC_PROOF
    (([], (--`!n m. (n <= SUC m) = (n <= m \/ (n = SUC m))`--)),
     REWRITE_TAC [LESS_OR_EQ,LESS_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[]);

val CARD_INTER_LESS_EQ =
    store_thm
    ("CARD_INTER_LESS_EQ",
     (--`!s:'a set. FINITE s ==> !t. CARD (s INTER t) <= CARD s`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_DEF,INTER_EMPTY,LESS_EQ_REFL],
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      GEN_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_THEN (ASSUME_TAC o SPEC (--`t:'a set`--)) INTER_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [IN_INTER,lemma1],
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [lemma2]]]);

val CARD_UNION =
    store_thm
    ("CARD_UNION",
     (--`!s:'a set.
       FINITE s ==>
       !t. FINITE t ==>
           (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY,INTER_EMPTY,CARD_DEF,ADD_CLAUSES],
      REPEAT STRIP_TAC THEN REWRITE_TAC [INSERT_UNION,INSERT_INTER] THEN
      ASM_CASES_TAC (--`(e:'a) IN t`--) THENL
      [IMP_RES_THEN (ASSUME_TAC o SPEC (--`t:'a set`--)) INTER_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN RES_TAC THEN
       ASM_REWRITE_TAC [IN_INTER,ADD_CLAUSES],
       IMP_RES_TAC UNION_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN RES_TAC THEN
       ASM_REWRITE_TAC [ADD_CLAUSES, INV_SUC_EQ, IN_UNION]]]);

val CARD_UNION_EQN = store_thm(
  "CARD_UNION_EQN",
  ``!s:'a set t.
      FINITE s /\ FINITE t ==>
      (CARD (s UNION t) = CARD s + CARD t - CARD (s INTER t))``,
  REPEAT STRIP_TAC THEN
  `CARD (s INTER t) <= CARD s`
    by SRW_TAC [][CARD_INTER_LESS_EQ] THEN
  `CARD (s INTER t) <= CARD s + CARD t` by SRW_TAC [ARITH_ss][] THEN
  SRW_TAC [][GSYM ADD_EQ_SUB, CARD_UNION]);

val lemma =
    TAC_PROOF
    (([], (--`!n m. (n <= SUC m) = (n <= m \/ (n = SUC m))`--)),
     REWRITE_TAC [LESS_OR_EQ,LESS_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[]);

val CARD_SUBSET =
    store_thm
    ("CARD_SUBSET",
     (--`!s:'a set.
         FINITE s ==> !t. t SUBSET s ==> CARD t <= CARD s`--),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [SUBSET_EMPTY,CARD_EMPTY] THEN
        GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [CARD_DEF,LESS_EQ_REFL],
      IMP_RES_THEN (ASSUME_TAC o SPEC (--`e:'a`--)) FINITE_INSERT THEN
        IMP_RES_TAC CARD_INSERT THEN
        ASM_REWRITE_TAC [SUBSET_INSERT_DELETE] THEN
        REPEAT STRIP_TAC THEN RES_THEN MP_TAC THEN
        IMP_RES_TAC SUBSET_FINITE THEN
        IMP_RES_TAC DELETE_FINITE THEN
        IMP_RES_TAC CARD_DELETE THEN
        ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL
        [let val th = SPEC (--`CARD (t:'a set)`--) num_CASES
         in REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC th
         end THENL
          [REWRITE_TAC [LESS_OR_EQ,LESS_0],
           REWRITE_TAC [SUC_SUB1,LESS_OR_EQ,LESS_MONO_EQ,INV_SUC_EQ]],
        STRIP_TAC THEN ASM_REWRITE_TAC [lemma]]]);

val CARD_PSUBSET =
    store_thm
    ("CARD_PSUBSET",
     (--`!s:'a set.
         FINITE s ==> !t. t PSUBSET s ==> CARD t < CARD s`--),
     REPEAT STRIP_TAC THEN IMP_RES_TAC PSUBSET_DEF THEN
     IMP_RES_THEN (IMP_RES_THEN MP_TAC) CARD_SUBSET THEN
     PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
     DISCH_THEN (STRIP_THM_THEN
       (fn th => fn g => ACCEPT_TAC th g handle _ => MP_TAC th g)) THEN
     IMP_RES_THEN STRIP_ASSUME_TAC PSUBSET_INSERT_SUBSET THEN
     IMP_RES_THEN (IMP_RES_THEN MP_TAC) CARD_SUBSET THEN
     IMP_RES_TAC INSERT_SUBSET THEN
     IMP_RES_TAC SUBSET_FINITE THEN
     IMP_RES_TAC CARD_INSERT THEN
     ASM_REWRITE_TAC [LESS_EQ] THEN
     REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val SUBSET_EQ_CARD = Q.store_thm
("SUBSET_EQ_CARD",
 `!s. FINITE s ==> !t. FINITE t /\ (CARD s = CARD t) /\ s SUBSET t ==> (s=t)`,
SET_INDUCT_TAC THEN RW_TAC bool_ss [EXTENSION] THENL
[PROVE_TAC [CARD_DEF, CARD_EQ_0], ALL_TAC] THEN
 EQ_TAC THEN RW_TAC bool_ss [] THENL
 [FULL_SIMP_TAC bool_ss [SUBSET_DEF], ALL_TAC] THEN
 Q.PAT_ASSUM `!t. FINITE t /\ (CARD s = CARD t) /\ s SUBSET t ==> (s = t)`
            (MP_TAC o Q.SPEC `t DELETE e`) THEN
 RW_TAC arith_ss [FINITE_DELETE, CARD_DELETE, SUBSET_DELETE] THENL
 [ALL_TAC, FULL_SIMP_TAC bool_ss [INSERT_SUBSET]] THEN
 `CARD t = SUC (CARD s)` by PROVE_TAC [CARD_INSERT] THEN
 `s SUBSET t` by FULL_SIMP_TAC bool_ss [INSERT_SUBSET] THEN
 FULL_SIMP_TAC arith_ss [] THEN
 RW_TAC bool_ss [INSERT_DEF, DELETE_DEF, GSPECIFICATION,IN_DIFF,NOT_IN_EMPTY]);

val CARD_SING =
    store_thm
    ("CARD_SING",
     (--`!x:'a. CARD {x} = 1`--),
     CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
     GEN_TAC THEN ASSUME_TAC FINITE_EMPTY THEN
     IMP_RES_THEN (ASSUME_TAC o SPEC (--`x:'a`--)) FINITE_INSERT THEN
     IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [NOT_IN_EMPTY,CARD_DEF]);

val SING_IFF_CARD1 =
    store_thm
    ("SING_IFF_CARD1",
     (--`!s:'a set. SING s = (CARD s = 1) /\ FINITE s`--),
     REWRITE_TAC [SING_DEF,ONE] THEN
     GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      CONJ_TAC THENL
      [ASSUME_TAC FINITE_EMPTY THEN
       IMP_RES_TAC CARD_INSERT THEN
       ASM_REWRITE_TAC [CARD_EMPTY,NOT_IN_EMPTY],
       REWRITE_TAC [FINITE_INSERT,FINITE_EMPTY]],
      STRIP_ASSUME_TAC (SPEC (--`s:'a set`--) SET_CASES) THENL
      [ASM_REWRITE_TAC [CARD_EMPTY,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
       ASM_REWRITE_TAC [FINITE_INSERT] THEN
       DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
       IMP_RES_TAC CARD_INSERT THEN
       IMP_RES_TAC CARD_EQ_0 THEN
       ASM_REWRITE_TAC [INV_SUC_EQ] THEN
       DISCH_TAC THEN EXISTS_TAC (--`x:'a`--) THEN
       ASM_REWRITE_TAC []]]);

(* ---------------------------------------------------------------------*)
(* A theorem from homeier@aero.uniblab (Peter Homeier)      		*)
(* ---------------------------------------------------------------------*)
val CARD_DIFF =
    store_thm
    ("CARD_DIFF",
     (--`!t:'a set.
          FINITE t ==>
          !s:'a set. FINITE s ==>
                       (CARD (s DIFF t) = (CARD s - CARD (s INTER t)))`--),
     SET_INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC [DIFF_EMPTY,INTER_EMPTY,CARD_EMPTY,SUB_0],
      PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      COND_CASES_TAC THENL
      [let val th = SPEC (--`s':'a set`--)
                         (UNDISCH (SPEC (--`s:'a set`--) INTER_FINITE))
       in PURE_ONCE_REWRITE_TAC [MATCH_MP CARD_INSERT th]
       end THEN
       IMP_RES_THEN (ASSUME_TAC o SPEC (--`e:'a`--)) FINITE_DELETE THEN
       IMP_RES_TAC CARD_DELETE THEN
       RES_TAC THEN ASM_REWRITE_TAC [IN_INTER,DIFF_INSERT] THEN
       PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL SUB_PLUS)] THEN
       REWRITE_TAC [ONE,ADD_CLAUSES,DELETE_INTER] THEN
       MP_TAC (SPECL [(--`s':'a set`--),(--`s:'a set`--),(--`e:'a`--)]
                     IN_INTER) THEN
       ASM_REWRITE_TAC [DELETE_NON_ELEMENT] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBST1_TAC (SPECL [(--`s:'a set`--),(--`s':'a set`--)] INTER_COMM)
       THEN REFL_TAC,
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
       RES_TAC THEN ASM_REWRITE_TAC [DIFF_INSERT]]]);

(* Improved version of the above - DIFF's second argument can be infinite *)
val CARD_DIFF_EQN = store_thm(
  "CARD_DIFF_EQN",
  ``!s. FINITE s ==> (CARD (s DIFF t) = CARD s - CARD (s INTER t))``,
  Induct_on `FINITE` THEN SRW_TAC [][] THEN
  Cases_on `e IN t` THEN
  SRW_TAC [][INSERT_INTER, INSERT_DIFF, INTER_FINITE] THEN
  `CARD (s INTER t) <= CARD s`
    by METIS_TAC [CARD_INTER_LESS_EQ] THEN
  SRW_TAC [numSimps.ARITH_ss][]);

(* ---------------------------------------------------------------------*)
(* A theorem from homeier@aero.uniblab (Peter Homeier)	        	*)
(* ---------------------------------------------------------------------*)
val LESS_CARD_DIFF =
    store_thm
    ("LESS_CARD_DIFF",
     (--`!t:'a set. FINITE t ==>
      !s. FINITE s ==> (CARD t < CARD s) ==> (0 < CARD(s DIFF t))`--),
     REPEAT STRIP_TAC THEN
     REPEAT_GTCL IMP_RES_THEN SUBST1_TAC CARD_DIFF THEN
     PURE_REWRITE_TAC [GSYM SUB_LESS_0] THEN
     let val th1 = UNDISCH (SPEC (--`s:'a set`--) CARD_INTER_LESS_EQ)
         val th2 = SPEC (--`t:'a set`--)
                        (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] th1)
     in DISJ_CASES_THEN2 ACCEPT_TAC (SUBST_ALL_TAC o SYM) th2
     end THEN
     let val th3 = SPEC (--`s:'a set`--)
                        (UNDISCH(SPEC(--`t:'a set`--) CARD_INTER_LESS_EQ))
         val th4 = PURE_ONCE_REWRITE_RULE [INTER_COMM] th3
     in
     IMP_RES_TAC (PURE_ONCE_REWRITE_RULE [GSYM NOT_LESS] th4)
     end);

val BIJ_FINITE = store_thm(
  "BIJ_FINITE",
  ``!f s t. BIJ f s t /\ FINITE s ==> FINITE t``,
  Q_TAC SUFF_TAC
    `!s. FINITE s ==> !f t. BIJ f s t ==> FINITE t` THEN1 METIS_TAC [] THEN
  Induct_on `FINITE s` THEN SRW_TAC[][BIJ_EMPTY, BIJ_INSERT] THEN
  METIS_TAC [FINITE_DELETE]);

val FINITE_BIJ_CARD_EQ = Q.store_thm
("FINITE_BIJ_CARD_EQ",
 `!S. FINITE S ==> !t f. BIJ f S t /\ FINITE t ==> (CARD S = CARD t)`,
SET_INDUCT_TAC THEN RW_TAC bool_ss [BIJ_EMPTY, CARD_EMPTY] THEN
`BIJ f s (t DELETE (f e))` by
     METIS_TAC [DELETE_NON_ELEMENT, IN_INSERT, DELETE_INSERT, BIJ_DELETE] THEN
RW_TAC bool_ss [CARD_INSERT] THEN
Q.PAT_ASSUM `$! m` (MP_TAC o Q.SPECL [`t DELETE f e`, `f`]) THEN
RW_TAC bool_ss [FINITE_DELETE] THEN
`f e IN t` by (Q.PAT_ASSUM `BIJ f (e INSERT s) t` MP_TAC THEN
               RW_TAC (bool_ss++SET_SPEC_ss) [BIJ_DEF,INJ_DEF,INSERT_DEF]) THEN
RW_TAC arith_ss [CARD_DELETE] THEN
`~(CARD t = 0)` by METIS_TAC [EMPTY_DEF, IN_DEF, CARD_EQ_0] THEN
RW_TAC arith_ss []);

val CARD_INJ_IMAGE = store_thm(
  "CARD_INJ_IMAGE",
  ``!f s. (!x y. (f x = f y) <=> (x = y)) /\ FINITE s ==>
          (CARD (IMAGE f s) = CARD s)``,
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN NTAC 3 STRIP_TAC THEN
  Q.ID_SPEC_TAC `s` THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][]);

val FINITE_COMPLETE_INDUCTION = Q.store_thm(
  "FINITE_COMPLETE_INDUCTION",
  `!P. (!x. (!y. y PSUBSET x ==> P y) ==> FINITE x ==> P x)
      ==>
       !x. FINITE x ==> P x`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ((BETA_RULE o
                 Q.ISPEC `\x. FINITE x ==> P x` o
                 REWRITE_RULE [prim_recTheory.WF_measure] o
                 Q.ISPEC `measure CARD`)
                relationTheory.WF_INDUCTION_THM) THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [AND_IMP_INTRO]) THEN
  Q.PAT_ASSUM `!x. (!y. y PSUBSET x ==> P y) /\ FINITE x ==>
                   P x` MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [prim_recTheory.measure_def,
                   relationTheory.inv_image_def] THEN
  BETA_TAC THEN mesonLib.ASM_MESON_TAC [PSUBSET_FINITE, CARD_PSUBSET]);

val lem = Q.prove
(`!s. FINITE s ==>
  !t. FINITE t ==>
  !f. INJ f s t ==> CARD s <= CARD t`,
 SET_INDUCT_TAC
  THEN RW_TAC arith_ss [CARD_DEF]
  THEN `INJ f ((e INSERT s) DELETE e) (t DELETE (f e))`
       by METIS_TAC [INJ_DELETE,IN_INSERT]
  THEN FULL_SIMP_TAC bool_ss [DELETE_INSERT]
  THEN `s DELETE e = s` by METIS_TAC [DELETE_NON_ELEMENT]
  THEN POP_ASSUM SUBST_ALL_TAC
  THEN `FINITE (t DELETE (f e))` by RW_TAC bool_ss [FINITE_DELETE]
  THEN `CARD s <= CARD (t DELETE (f e))` by METIS_TAC []
  THEN `f e IN t` by METIS_TAC [INJ_DEF, IN_INSERT]
  THEN `CARD(t DELETE (f e)) = CARD t - 1` by RW_TAC arith_ss [CARD_DELETE]
  THEN POP_ASSUM SUBST_ALL_TAC
  THEN MATCH_MP_TAC (AP ``!m n. 0 < n /\ m<=n-1 ==> SUC m <= n``)
  THEN ASM_REWRITE_TAC []
  THEN Cases_on `t`
  THEN FULL_SIMP_TAC arith_ss [NOT_IN_EMPTY,CARD_DEF,FINITE_INSERT]);

val INJ_CARD = Q.store_thm
("INJ_CARD",
 `!(f:'a->'b) s t. INJ f s t /\ FINITE t ==> CARD s <= CARD t`,
 METIS_TAC [lem, FINITE_INJ]);

val PHP = Q.store_thm
("PHP",
 `!(f:'a->'b) s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t`,
 METIS_TAC [INJ_CARD, AP ``x < y = ~(y <= x)``]);

(* =====================================================================*)
(* Infiniteness								*)
(* =====================================================================*)

val _ = overload_on ("INFINITE", ``\s. ~FINITE s``)
val INFINITE_DEF = save_thm("INFINITE_DEF", TRUTH)

val NOT_IN_FINITE =
    store_thm
    ("NOT_IN_FINITE",
     (--`INFINITE (UNIV:'a set)
           =
         !s:'a set. FINITE s ==> ?x. ~(x IN s)`--),
     EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
      REWRITE_TAC [NOT_IMP] THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      REWRITE_TAC [EQ_UNIV] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC THEN RES_THEN STRIP_ASSUME_TAC THEN
      ASSUME_TAC (SPEC (--`x:'a`--) IN_UNIV) THEN RES_TAC]);

val INFINITE_INHAB = Q.store_thm
("INFINITE_INHAB",
 `!P. INFINITE P ==> ?x. x IN P`,
  REWRITE_TAC [MEMBER_NOT_EMPTY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [FINITE_EMPTY]);

val INVERSE_LEMMA =
    TAC_PROOF
    (([], (--`!f:'a->'b. (!x y. (f x = f y) ==> (x = y)) ==>
                     ((\x:'b. @y:'a. x = f y) o f = \x:'a.x)`--)),
     REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
     PURE_ONCE_REWRITE_TAC [o_THM] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
     EXISTS_TAC (--`x:'a`--) THEN REFL_TAC);

val IMAGE_11_INFINITE = store_thm (
  "IMAGE_11_INFINITE",
  ``!f:'a->'b. (!x y. (f x = f y) ==> (x = y)) ==>
      !s:'a set. INFINITE s ==> INFINITE (IMAGE f s)``,
  METIS_TAC [INJECTIVE_IMAGE_FINITE]);

val INFINITE_SUBSET =
    store_thm
    ("INFINITE_SUBSET",
     (--`!s:'a set. INFINITE s ==> (!t. s SUBSET t ==> INFINITE t)`--),
     REPEAT STRIP_TAC THEN IMP_RES_TAC SUBSET_FINITE THEN RES_TAC);

val IN_INFINITE_NOT_FINITE = store_thm (
  "IN_INFINITE_NOT_FINITE",
  ``!s t. INFINITE s /\ FINITE t ==> ?x:'a. x IN s /\ ~(x IN t)``,
   CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
   CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
   PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN
   REWRITE_TAC [SYM(SPEC_ALL IMP_DISJ_THM)] THEN
   PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL SUBSET_DEF)] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC INFINITE_SUBSET);

(* ---------------------------------------------------------------------- *)
(* The next series of lemmas are used for proving that if UNIV: set       *)
(* is INFINITE then :'a satisfies an axiom of infinity.			  *)
(*									  *)
(* The function g:num->'a set defines a series of sets:		          *)
(*									  *)
(*    {}, {x1}, {x1,x2}, {x1,x2,x3},...					  *)
(*									  *)
(* and one then defines an f:'a->'a such that f(xi)=xi+1.		  *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------*)
(* Defining equations for g 				                *)
(* ---------------------------------------------------------------------*)

val gdef = map Term
    [    `g  0      = ({}:'a set)`,
     `!n. g (SUC n) = (@x:'a.~(x IN (g n))) INSERT (g n)`];

(* ---------------------------------------------------------------------*)
(* Lemma: g n is finite for all n.					*)
(* ---------------------------------------------------------------------*)

val g_finite =
    TAC_PROOF
    ((gdef, ``!n:num. FINITE (g n:'a set)``),
     INDUCT_TAC THEN ASM_REWRITE_TAC[FINITE_EMPTY,FINITE_INSERT]);

(* ---------------------------------------------------------------------*)
(* Lemma: g n is contained in g (n+i) for all i.			*)
(* ---------------------------------------------------------------------*)

val g_subset =
    TAC_PROOF
    ((gdef, ``!n. !x:'a. x IN (g n) ==> !i. x IN (g (n+i))``),
     REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [ADD_CLAUSES,IN_INSERT]);

(* ---------------------------------------------------------------------*)
(* Lemma: if x is in g(n) then {x} = g(n+1)-g(n) for some n.		*)
(* ---------------------------------------------------------------------*)

val lemma =
    TAC_PROOF(([], (--`((A \/ B) /\ ~B) = (A /\ ~B)`--)),
              BOOL_CASES_TAC (--`B:bool`--) THEN REWRITE_TAC[]);

val g_cases =
    TAC_PROOF
    ((gdef, (--`(!s. FINITE s ==> ?x:'a. ~(x IN s)) ==>
    	      !x:'a. (?n. x IN (g n)) ==>
	            (?m. (x IN (g (SUC m))) /\ ~(x IN (g m)))`--)),
     DISCH_TAC THEN GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN MP_TAC o
                 CONV_RULE numLib.EXISTS_LEAST_CONV) THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC (--`n:num`--) num_CASES) THEN
     ASM_REWRITE_TAC [NOT_IN_EMPTY,IN_INSERT] THEN STRIP_TAC THENL
     [REWRITE_TAC [lemma] THEN EXISTS_TAC (--`n':num`--) THEN
      CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_ASSUM (fn th => fn g => SUBST1_TAC th g) THEN
      CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_ACCEPT_TAC g_finite,
      REWRITE_TAC [lemma] THEN
      FIRST_ASSUM (fn th => fn g => MP_TAC (SPEC (--`n':num`--) th) g) THEN
      REWRITE_TAC [LESS_SUC_REFL] THEN
      DISCH_THEN IMP_RES_TAC]);

(* ---------------------------------------------------------------------*)
(* Lemma: @x.~(x IN {}) is an element of every g(n+1).			*)
(* ---------------------------------------------------------------------*)

val z_in_g1 =
    TAC_PROOF
    ((gdef, (--`(@x:'a.~(x IN {})) IN (g (SUC 0))`--)),
     ASM_REWRITE_TAC [NOT_IN_EMPTY,IN_INSERT]);

val z_in_gn =
    TAC_PROOF
    ((gdef, (--`!n:num. (@x:'a. ~(x IN {})) IN (g (SUC n))`--)),
     PURE_ONCE_REWRITE_TAC [ADD1] THEN
     PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC g_subset THEN
     REWRITE_TAC [ONE,z_in_g1]);

(* ---------------------------------------------------------------------*)
(* Lemma: @x. ~(x IN g n) is an element of g(n+1).			*)
(* ---------------------------------------------------------------------*)

val in_lemma =
    TAC_PROOF
    ((gdef, (--`!n:num. (@x:'a. ~(x IN (g n))) IN (g(SUC n))`--)),
     ASM_REWRITE_TAC [IN_INSERT]);

(* ---------------------------------------------------------------------*)
(* Lemma: the x added to g(n+1) is not in g(n)				*)
(* ---------------------------------------------------------------------*)

val not_in_lemma =
    TAC_PROOF
    ((gdef, (--`(!s. FINITE s ==>
                     ?x:'a. ~(x IN s)) ==>
	             !i n. ~((@x:'a. ~(x IN (g (n+i)))) IN g n)`--)),
     DISCH_TAC THEN INDUCT_TAC THENL
     [ASM_REWRITE_TAC [ADD_CLAUSES] THEN
      GEN_TAC THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_ACCEPT_TAC g_finite,
      PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      GEN_TAC THEN FIRST_ASSUM (fn th => fn g =>
                                  MP_TAC(SPEC (--`SUC n`--) th) g) THEN
      REWRITE_TAC (map ASSUME gdef) THEN
      REWRITE_TAC [IN_INSERT,DE_MORGAN_THM] THEN
      REPEAT STRIP_TAC THEN RES_TAC]);

(* ---------------------------------------------------------------------*)
(* Lemma: each value is added to a unique g(n).				*)
(* ---------------------------------------------------------------------*)

val less_lemma = numLib.ARITH_PROVE ``!m n. ~(m = n) = ((m < n) \/ (n < m))``

val gn_unique = TAC_PROOF
((gdef,
 (--`(!s. FINITE s ==>
        ?x:'a. ~(x IN s)) ==>
        !(n:num) m. ((@x:'a.~(x IN (g n))) = @x:'a.~(x IN (g m))) = (n=m)`--)),
     DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC [less_lemma] THEN
      DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN
      DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [num_CONV (--`1`--),ADD_CLAUSES] THEN
      REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      IMP_RES_TAC not_in_lemma THEN
      DISCH_TAC THENL
      [MP_TAC (SPEC (--`n:num`--) in_lemma) THEN
       EVERY_ASSUM (fn th => fn g => SUBST1_TAC th g handle _ => ALL_TAC g)
       THEN DISCH_TAC THEN RES_TAC,
       MP_TAC (SPEC (--`m:num`--) in_lemma) THEN
       EVERY_ASSUM (fn th=>fn g => SUBST1_TAC (SYM th) g handle _ => ALL_TAC g)
       THEN DISCH_TAC THEN RES_TAC],
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]);

(* ---------------------------------------------------------------------*)
(* Lemma: the value added to g(n) to get g(n+1) is unique.		*)
(* ---------------------------------------------------------------------*)

val x_unique =
    TAC_PROOF
    ((gdef, (--`!n. !x. !y:'a.
	       (~(x IN g n) /\ ~(y IN g n))
                ==> (x IN g(SUC n))
                ==> (y IN g(SUC n))
                ==> (x = y)`--)),
     REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT] THEN
     REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC);

(* ---------------------------------------------------------------------*)
(* Now, show the existence of a non-onto one-one fuction.  The required	*)
(* function is denoted by fdef.  The theorem cases is:			*)
(*									*)
(*   |- (?n. x IN (g n)) \/ (!n. ~x IN (g n))				*)
(*									*)
(* and is used to do case splits on the condition of the conditional 	*)
(* present in fdef.							*)
(* ---------------------------------------------------------------------*)

val fdef = Term
   `\x:'a. if (?n. x IN (g n))
           then (@y. ~(y IN (g (SUC @n. x IN g(SUC n) /\ ~(x IN (g n))))))
           else  x`;

val cases =
   let val thm = GEN (--`x:'a`--)
                     (SPEC (--`?n:num.(x:'a) IN (g n)`--) EXCLUDED_MIDDLE)
   in CONV_RULE (ONCE_DEPTH_CONV NOT_EXISTS_CONV) thm
   end;


val INF_IMP_INFINITY = TAC_PROOF(([],
--`(!s. FINITE s ==> ?x:'a. ~(x IN s)) ==>
   ?f:'a->'a.
       (!x y. (f x = f y) ==> (x=y)) /\
       ?y. !x. ~(f x = y)`--),
 let val xcases = SPEC (--`x:'a`--) cases
     and ycases = SPEC (--`y:'a`--) cases
     fun nv x = (--`SUC(@n. ^x IN (g(SUC n)) /\ ~(^x IN (g n)))`--)
 in
 STRIP_ASSUME_TAC (prove_rec_fn_exists num_Axiom (list_mk_conj gdef)) THEN
 STRIP_TAC THEN EXISTS_TAC fdef THEN
 CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
 [REPEAT GEN_TAC THEN
  DISJ_CASES_THEN (fn th => REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) xcases
  THEN
  DISJ_CASES_THEN (fn th => REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) ycases
  THENL
  [REWRITE_TAC [UNDISCH gn_unique,INV_SUC_EQ] THEN
   IMP_RES_THEN (IMP_RES_THEN(STRIP_ASSUME_TAC o SELECT_RULE)) g_cases THEN
   DISCH_THEN SUBST_ALL_TAC THEN IMP_RES_TAC x_unique,
   ASSUME_TAC (SPEC (nv (--`x:'a`--)) in_lemma) THEN
   DISCH_THEN (SUBST_ALL_TAC o SYM) THEN RES_TAC,
   ASSUME_TAC (SPEC (nv (--`y:'a`--)) in_lemma) THEN
   DISCH_THEN SUBST_ALL_TAC THEN RES_TAC],
   EXISTS_TAC (--`@x:'a.~(x IN g 0)`--) THEN GEN_TAC THEN
   DISJ_CASES_THEN (fn th => REWRITE_TAC[th] THEN ASSUME_TAC th) xcases
   THENL
   [REWRITE_TAC [UNDISCH gn_unique,NOT_SUC],
    ASSUME_TAC (SPEC (--`n:num`--) z_in_gn) THEN
    FIRST_ASSUM (fn th => fn g => SUBST1_TAC th g) THEN
    DISCH_THEN SUBST_ALL_TAC THEN RES_TAC]]
  end);

(* --------------------------------------------------------------------- *)
(* We now also prove the converse, namely that if :'a satisfies an axiom *)
(* of infinity then UNIV:'a set is INFINITE.			         *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* First, a version of the primitive recursion theorem			 *)
(* --------------------------------------------------------------------- *)

val prth =
    prove_rec_fn_exists num_Axiom
    (Term`(fn f x 0       = x) /\
          (fn f x (SUC n) = (f:'a->'a) (fn f x n))`);

val prmth =
    TAC_PROOF
    (([], (--`!x:'a. !f. ?fn. (fn 0 = x) /\ !n. fn (SUC n) = f(fn n)`--)),
     REPEAT GEN_TAC THEN STRIP_ASSUME_TAC prth THEN
     EXISTS_TAC (--`fn (f:'a->'a) (x:'a) : num->'a`--) THEN
     ASM_REWRITE_TAC []);

(* --------------------------------------------------------------------- *)
(* Lemma: if f is one-to-one and not onto, there is a one-one f:num->'a. *)
(* --------------------------------------------------------------------- *)

val num_fn_thm = TAC_PROOF(([],
(--`(?f:'a->'a. (!x y. (f x = f y) ==> (x=y)) /\ ?y. !x. ~(f x = y))
    ==>
    (?fn:num->'a. (!n m. (fn n = fn m) ==> (n=m)))`--)),
     STRIP_TAC THEN
     STRIP_ASSUME_TAC (SPECL [(--`y:'a`--),(--`f:'a->'a`--)] prmth) THEN
     EXISTS_TAC (--`fn:num->'a`--) THEN INDUCT_TAC THENL
     [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC[],
      INDUCT_TAC THEN ASM_REWRITE_TAC [INV_SUC_EQ] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC]);

(* --------------------------------------------------------------------- *)
(* Lemma: every finite set of numbers has an upper bound.		*)
(* --------------------------------------------------------------------- *)

val finite_N_bounded =
    TAC_PROOF
    (([], (--`!s. FINITE s ==> ?m. !n. (n IN s) ==> n < m`--)),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY],
      FIRST_ASSUM (fn th => fn g => CHOOSE_THEN ASSUME_TAC th g) THEN
      EXISTS_TAC (--`(SUC m) + e`--) THEN REWRITE_TAC [IN_INSERT] THEN
      REPEAT STRIP_TAC THENL
      [PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [LESS_ADD_SUC],
       RES_TAC THEN IMP_RES_TAC LESS_IMP_LESS_ADD THEN
       let val [_,_,c1,c2] = CONJUNCTS ADD_CLAUSES
       in ASM_REWRITE_TAC [c1,SYM c2]
       end]]);

(* --------------------------------------------------------------------- *)
(* Lemma: the set UNIV:(num->bool) is infinite.				*)
(* --------------------------------------------------------------------- *)

val N_lemma =
    TAC_PROOF
    (([], (--`INFINITE(UNIV:(num->bool))`--)),
     REWRITE_TAC [INFINITE_DEF] THEN STRIP_TAC THEN
     IMP_RES_THEN MP_TAC finite_N_bounded THEN
     REWRITE_TAC [IN_UNIV] THEN
     CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
     CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC (--`SUC m`--) THEN
     REWRITE_TAC [NOT_LESS,LESS_OR_EQ,LESS_SUC_REFL]);

(* --------------------------------------------------------------------- *)
(* Lemma: if s is finite, f:num->'a is one-one, then ?n. f(n) not in s	*)
(* --------------------------------------------------------------------- *)

val main_lemma =
    TAC_PROOF
    (([], (--`!s:'a set. FINITE s ==>
           !f:num->'a. (!n m. (f n = f m) ==> (n=m)) ==> ?n. ~(f n IN s)`--)),
     REPEAT STRIP_TAC THEN
     ASSUME_TAC N_lemma THEN
     IMP_RES_TAC IMAGE_11_INFINITE THEN
     IMP_RES_THEN (TRY o IMP_RES_THEN MP_TAC) IN_INFINITE_NOT_FINITE THEN
     REWRITE_TAC [IN_IMAGE,IN_UNIV] THEN
     REPEAT STRIP_TAC THEN EXISTS_TAC (--`x':num`--) THEN
     EVERY_ASSUM (fn th => fn g => SUBST1_TAC (SYM th) g handle _ => ALL_TAC g)
     THEN FIRST_ASSUM ACCEPT_TAC);

(* ---------------------------------------------------------------------*)
(* Now show that we can always choose an element not in a finite set.	*)
(* ---------------------------------------------------------------------*)

val INFINITY_IMP_INF =
    TAC_PROOF
    (([],(--`(?f:'a->'a. (!x y. (f x = f y) ==> (x=y)) /\ ?y. !x. ~(f x = y))
          ==> (!s. FINITE s ==> ?x:'a. ~(x IN s))`--)),
     DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP num_fn_thm) THEN
     GEN_TAC THEN STRIP_TAC THEN
     IMP_RES_TAC main_lemma THEN
     EXISTS_TAC (--`(fn:num->'a) n`--) THEN
     FIRST_ASSUM ACCEPT_TAC);


(* ---------------------------------------------------------------------*)
(* Finally, we can prove the desired theorem.				*)
(* ---------------------------------------------------------------------*)

val INFINITE_UNIV =
    store_thm
    ("INFINITE_UNIV",
     (--`INFINITE (UNIV:'a set)
        =
      (?f:'a->'a. (!x y. (f x = f y) ==> (x = y)) /\ (?y. !x. ~(f x = y)))`--),
     PURE_ONCE_REWRITE_TAC [NOT_IN_FINITE] THEN
     ACCEPT_TAC (IMP_ANTISYM_RULE INF_IMP_INFINITY INFINITY_IMP_INF));

(* a natural consequence *)
val INFINITE_NUM_UNIV = store_thm(
  "INFINITE_NUM_UNIV",
  ``INFINITE univ(:num)``,
  REWRITE_TAC [GSYM INFINITE_DEF] THEN
  SRW_TAC [][INFINITE_UNIV] THEN Q.EXISTS_TAC `SUC` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `0` THEN SRW_TAC [][]);
val _ = export_rewrites ["INFINITE_NUM_UNIV"]

val FINITE_PSUBSET_INFINITE = store_thm("FINITE_PSUBSET_INFINITE",
(--`!s. INFINITE (s:'a set) =
        !t. FINITE (t:'a set) ==> ((t SUBSET s) ==> (t PSUBSET s))`--),
   PURE_REWRITE_TAC [INFINITE_DEF,PSUBSET_DEF] THEN
   GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC,
     FIRST_ASSUM (fn th => fn g => SUBST_ALL_TAC th g handle _ => NO_TAC g)
     THEN RES_TAC],
    REPEAT STRIP_TAC THEN RES_TAC THEN
    ASSUME_TAC (SPEC (--`s:'a set`--) SUBSET_REFL) THEN
    ASSUME_TAC (REFL (--`s:'a set`--)) THEN RES_TAC]);

val FINITE_PSUBSET_UNIV = store_thm("FINITE_PSUBSET_UNIV",
(--`INFINITE (UNIV:'a set) = !s:'a set. FINITE s ==> s PSUBSET UNIV`--),
     PURE_ONCE_REWRITE_TAC [FINITE_PSUBSET_INFINITE] THEN
     REWRITE_TAC [PSUBSET_DEF,SUBSET_UNIV]);

val INFINITE_DIFF_FINITE = store_thm("INFINITE_DIFF_FINITE",
     (--`!s t. (INFINITE s /\ FINITE t) ==> ~(s DIFF t = ({}:'a set))`--),
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     IMP_RES_TAC IN_INFINITE_NOT_FINITE THEN
     REWRITE_TAC [EXTENSION,IN_DIFF,NOT_IN_EMPTY] THEN
     CONV_TAC NOT_FORALL_CONV THEN
     EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[]);

val FINITE_ISO_NUM =
    store_thm
    ("FINITE_ISO_NUM",
     (--`!s:'a set.
       FINITE s ==>
       ?f. (!n m. (n < CARD s /\ m < CARD s) ==> (f n = f m) ==> (n = m)) /\
           (s = {f n | n < CARD s})`--),
  SET_INDUCT_TAC THENL
  [PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
   CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
   REWRITE_TAC [CARD_EMPTY,NOT_LESS_0,NOT_IN_EMPTY],
   FIRST_ASSUM (fn th => fn g => CHOOSE_THEN STRIP_ASSUME_TAC th g) THEN
   PURE_ONCE_REWRITE_TAC [UNDISCH (SPEC (--`s:'a set`--) CARD_INSERT)] THEN
   FILTER_ASM_REWRITE_TAC is_neg [] THEN
   PURE_ONCE_REWRITE_TAC [LESS_THM] THEN
   EXISTS_TAC (--`\n. if n < (CARD (s:'a set)) then f n else (e:'a)`--) THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    let fun ttac th g = SUBST_ALL_TAC th g handle _ => ASSUME_TAC th g
    in DISCH_THEN (REPEAT_TCL STRIP_THM_THEN ttac) end
    THENL
    [REPEAT STRIP_TAC THEN REFL_TAC,
     let fun is_less t = (fst(strip_comb t) = (--`$<`--)) handle _ => false
     in FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] end THEN
     FIRST_ASSUM (fn th => fn g => MP_TAC (assert (is_eq o concl) th) g) THEN
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC,
     let fun is_less t = (fst(strip_comb t) = (--`$<`--)) handle _ => false
     in FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] end THEN
     FIRST_ASSUM (fn th => fn g => MP_TAC (assert (is_eq o concl) th) g) THEN
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC,
     let fun is_less t = (fst(strip_comb t) = (--`$<`--)) handle _ => false
     in FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] end THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC],
    FIRST_ASSUM (fn th => fn g => (MP_TAC (assert(is_eq o concl) th)) g) THEN
    PURE_REWRITE_TAC [EXTENSION,IN_INSERT] THEN
    CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
    DISCH_THEN (fn th => PURE_ONCE_REWRITE_TAC [th]) THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [EXISTS_TAC (--`CARD (s:'a set)`--) THEN
     REWRITE_TAC [LESS_REFL] THEN FIRST_ASSUM ACCEPT_TAC,
     EXISTS_TAC (--`n:num`--) THEN
     FILTER_ASM_REWRITE_TAC (fn t => (not(lhs t = (--`s:'a set`--)))
                                     handle _ => true) [],
     SUBST1_TAC
       (ASSUME (--`x:'a = (if n < CARD (s:'a set) then f n else e)`--)) THEN
     SUBST1_TAC (ASSUME (--`n = CARD (s:'a set)`--)) THEN
     REWRITE_TAC [LESS_REFL],
     SUBST1_TAC
       (ASSUME (--`x:'a = (if n < CARD (s:'a set) then f n else e)`--)) THEN
     DISJ2_TAC THEN EXISTS_TAC (--`n:num`--) THEN
     REWRITE_TAC [ASSUME (--`n < CARD (s:'a set)`--)]]]]);


val FINITE_WEAK_ENUMERATE = Q.store_thm
("FINITE_WEAK_ENUMERATE",
 `!s. FINITE s = ?f b. !e. e IN s = ?n. n < b /\ (e = f n)`,
  ONCE_REWRITE_TAC [EQ_IMP_THM] THEN
  SIMP_TAC bool_ss [FORALL_AND_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SIMP_TAC bool_ss [IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `0` THEN SIMP_TAC arith_ss [],
      Q.EXISTS_TAC `\n. if n = b then e else f n` THEN
      Q.EXISTS_TAC `b + 1` THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
        Q.EXISTS_TAC `b` THEN ASM_SIMP_TAC arith_ss [],
        RES_TAC THEN Q.EXISTS_TAC `n` THEN ASM_SIMP_TAC arith_ss [],
        POP_ASSUM MP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
        ASM_MESON_TAC [AP (Term`~(x = y) /\ x < y + 1 ==> x < y`)]
      ]
    ],

    SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
    MAP_EVERY Q.ID_SPEC_TAC [`f`, `s`, `b`] THEN numLib.INDUCT_TAC THENL [
      SIMP_TAC (bool_ss ++ ARITH_ss) [] THEN
      GEN_TAC THEN
      STRIP_ASSUME_TAC (Q.SPEC `s` SET_CASES) THEN
      ASM_SIMP_TAC bool_ss [IN_INSERT, FINITE_EMPTY] THEN
      DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN REWRITE_TAC [],
      REPEAT STRIP_TAC THEN
      Q.ASM_CASES_TAC `?x. x IN s /\ !m. m < b ==> ~(f m = x)` THENL [
        POP_ASSUM STRIP_ASSUME_TAC THEN
        Q.SUBGOAL_THEN `f b = x` ASSUME_TAC THENL [
          `?n. n < SUC b /\ (x = f n)` by ASM_MESON_TAC [] THEN
          `~(n < b)` by ASM_MESON_TAC [] THEN
          `n = b` by ASM_SIMP_TAC arith_ss [] THEN
          ASM_SIMP_TAC bool_ss [],
          ALL_TAC
        ] THEN
        `s = x INSERT (s DELETE x)` by ASM_MESON_TAC [INSERT_DELETE] THEN
        POP_ASSUM SUBST1_TAC THEN
        SIMP_TAC bool_ss [FINITE_INSERT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        Q.EXISTS_TAC `f` THEN SIMP_TAC bool_ss [IN_DELETE] THEN
        GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
          `?n. n < SUC b /\ (e = f n)` by ASM_MESON_TAC [] THEN
          `~(n = b)` by ASM_MESON_TAC [] THEN
          `n < b` by ASM_SIMP_TAC arith_ss [] THEN
          ASM_MESON_TAC [],
          `n < SUC b` by ASM_SIMP_TAC arith_ss [] THEN
          ASM_MESON_TAC []
        ],
        FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `f` THEN
        POP_ASSUM (ASSUME_TAC o SIMP_RULE bool_ss []) THEN
        ASM_MESON_TAC [AP (Term`!x y. x < y ==> x < SUC y`)]
      ]
    ]
  ]);

val lem = prove(
  ``!s R.
      FINITE s /\ (!e. e IN s <=> (?y. R e y) \/ (?x. R x e)) /\
      (!n. R (f (SUC n)) (f n)) ==>
      ?x. R^+ x x``,
  REPEAT STRIP_TAC THEN `!n. f n IN s` by METIS_TAC [] THEN
  Cases_on `?n m. (f n = f m) /\ n <> m` THENL [
    POP_ASSUM STRIP_ASSUME_TAC THEN
    Cases_on `n < m` THENL [
      ALL_TAC,
      `m < n` by DECIDE_TAC
    ] THEN
    Q.ISPECL_THEN [`inv R^+`, `f`] MP_TAC transitive_monotone THEN
    SRW_TAC [][relationTheory.inv_DEF, relationTheory.transitive_inv] THEN
    METIS_TAC [relationTheory.TC_SUBSET],

    `!n m. (f n = f m) = (n = m)` by METIS_TAC [] THEN
    `IMAGE f univ(:num) SUBSET s`
      by (SRW_TAC [][SUBSET_DEF, IN_IMAGE] THEN METIS_TAC []) THEN
    `FINITE (IMAGE f univ(:num))` by METIS_TAC [SUBSET_FINITE] THEN
    POP_ASSUM MP_TAC THEN SRW_TAC [][INJECTIVE_IMAGE_FINITE]
  ])

val FINITE_WF_noloops = store_thm(
  "FINITE_WF_noloops",
  ``!s. FINITE s ==>
        (WF (REL_RESTRICT R s) <=> irreflexive (REL_RESTRICT R s)^+)``,
  Q_TAC SUFF_TAC
    `!s. FINITE s ==>
         irreflexive (TC (REL_RESTRICT R s)) ==> WF (REL_RESTRICT R s)`
    THEN1 METIS_TAC [relationTheory.irreflexive_def,
                     relationTheory.WF_noloops] THEN
  REWRITE_TAC [prim_recTheory.WF_IFF_WELLFOUNDED,
               prim_recTheory.wellfounded_def] THEN
  REPEAT STRIP_TAC THEN
  Q.SPECL_THEN [`f`,
                `{x | x IN s /\ ((?y. R x y /\ y IN s) \/
                                 (?x'. R x' x /\ x' IN s))}`,
                `REL_RESTRICT R s`] MP_TAC (GEN_ALL lem) THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [REL_RESTRICT_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [relationTheory.irreflexive_def] THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC SUBSET_FINITE_I THEN Q.EXISTS_TAC `s` THEN
    SRW_TAC [][SUBSET_DEF],
    METIS_TAC []
  ]);

val FINITE_StrongOrder_WF = store_thm(
  "FINITE_StrongOrder_WF",
  ``!R s. FINITE s /\ StrongOrder (REL_RESTRICT R s) ==>
          WF (REL_RESTRICT R s)``,
  SRW_TAC [][FINITE_WF_noloops, relationTheory.StrongOrder,
             relationTheory.transitive_TC_identity]);

(* ===================================================================== *)
(* Big union (union of set of sets)                                      *)
(* ===================================================================== *)

val BIGUNION = Q.new_definition
 ("BIGUNION",
  `BIGUNION P = { x | ?s. s IN P /\ x IN s}`);

val IN_BIGUNION = store_thm
("IN_BIGUNION",
 ``!x sos. x IN (BIGUNION sos) = ?s. x IN s /\ s IN sos``,
  SIMP_TAC bool_ss [GSPECIFICATION, BIGUNION, pairTheory.PAIR_EQ] THEN
  MESON_TAC []);
val _ = export_rewrites ["IN_BIGUNION"]

val BIGUNION_EMPTY = Q.store_thm
("BIGUNION_EMPTY",
 `BIGUNION EMPTY = EMPTY`,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGUNION, NOT_IN_EMPTY]);
val _ = export_rewrites ["BIGUNION_EMPTY"]

val BIGUNION_EQ_EMPTY = Q.store_thm
("BIGUNION_EQ_EMPTY",
  `!P. ((BIGUNION P = {}) = (P = {}) \/ (P = {{}})) /\
        (({} = BIGUNION P) = (P = {}) \/ (P = {{}}))`,
  SRW_TAC [][EXTENSION, IN_BIGUNION, EQ_IMP_THM, FORALL_AND_THM] THEN
  METIS_TAC [EXTENSION]);
val _ = export_rewrites ["BIGUNION_EQ_EMPTY"]

val BIGUNION_SING = Q.store_thm
("BIGUNION_SING",
 `!x. BIGUNION {x} = x`,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGUNION, IN_INSERT, NOT_IN_EMPTY] THEN
  SIMP_TAC bool_ss [GSYM EXTENSION]);

val BIGUNION_UNION = Q.store_thm
("BIGUNION_UNION",
 `!s1 s2. BIGUNION (s1 UNION s2) = (BIGUNION s1) UNION (BIGUNION s2)`,
  SIMP_TAC bool_ss [EXTENSION, IN_UNION, IN_BIGUNION, LEFT_AND_OVER_OR,
                    EXISTS_OR_THM]);

val DISJOINT_BIGUNION_lemma = Q.prove
(`!s t. DISJOINT (BIGUNION s) t = !s'. s' IN s ==> DISJOINT s' t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC bool_ss [DISJOINT_DEF, EXTENSION, IN_BIGUNION, IN_INTER,
                    NOT_IN_EMPTY] THEN MESON_TAC []);

(* above with DISJOINT x y both ways round *)
val DISJOINT_BIGUNION = save_thm(
  "DISJOINT_BIGUNION",
  CONJ DISJOINT_BIGUNION_lemma
       (ONCE_REWRITE_RULE [DISJOINT_SYM] DISJOINT_BIGUNION_lemma));

val BIGUNION_INSERT = Q.store_thm
("BIGUNION_INSERT",
 `!s P. BIGUNION (s INSERT P) = s UNION (BIGUNION P)`,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGUNION, IN_UNION, IN_INSERT] THEN
  MESON_TAC []);
val _ = export_rewrites ["BIGUNION_INSERT"]

val BIGUNION_SUBSET = Q.store_thm
("BIGUNION_SUBSET",
 `!X P. BIGUNION P SUBSET X = (!Y. Y IN P ==> Y SUBSET X)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  FULL_SIMP_TAC bool_ss [IN_BIGUNION, SUBSET_DEF] THEN
  PROVE_TAC []);

val FINITE_BIGUNION = Q.store_thm
("FINITE_BIGUNION",
 `!P. FINITE P /\ (!s. s IN P ==> FINITE s) ==> FINITE (BIGUNION P)`,
  SIMP_TAC bool_ss [GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss [NOT_IN_EMPTY, FINITE_EMPTY, BIGUNION_EMPTY,
                    IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
                    BIGUNION_INSERT, FINITE_UNION]);

val FINITE_BIGUNION_EQ = Q.store_thm
("FINITE_BIGUNION_EQ",
 `!P. FINITE (BIGUNION P) = FINITE P /\ (!s. s IN P ==> FINITE s)`,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM, FINITE_BIGUNION] THEN
  Q_TAC SUFF_TAC
        `!P. FINITE P ==>
             !Q. (BIGUNION Q = P) ==> FINITE Q /\ !s. s IN Q ==> FINITE s`
         THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC (srw_ss()) [DISJ_IMP_THM] THEN
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
  `BIGUNION (IMAGE (\s. s DELETE e) Q) = P`
     by (REWRITE_TAC [EXTENSION] THEN
         ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
                      [IN_BIGUNION, IN_IMAGE, IN_DELETE] THEN
         Q.X_GEN_TAC `x` THEN EQ_TAC THEN STRIP_TAC THENL [
           `x IN BIGUNION Q` by (SRW_TAC [][] THEN METIS_TAC []) THEN
           POP_ASSUM MP_TAC THEN ASM_SIMP_TAC bool_ss [IN_INSERT],
           `x IN (e INSERT P)` by SRW_TAC [][] THEN
           `~(x = e)` by PROVE_TAC [] THEN
           `x IN BIGUNION Q` by ASM_SIMP_TAC bool_ss [IN_INSERT] THEN
           POP_ASSUM MP_TAC THEN SRW_TAC [][]
         ]) THEN
  `FINITE (IMAGE (\s. s DELETE e) Q) /\
   !s. s IN IMAGE (\s. s DELETE e) Q ==> FINITE s` by PROVE_TAC [] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `!x. FINITE { y | x = (\s. s DELETE e) y }` THEN1
       METIS_TAC [FINITELY_INJECTIVE_IMAGE_FINITE] THEN
    GEN_TAC THEN SIMP_TAC (srw_ss()) [] THEN
    Cases_on `e IN x` THENL [
      Q_TAC SUFF_TAC `{y | x = y DELETE e} = {}` THEN1 SRW_TAC [][] THEN
      SRW_TAC [][EXTENSION, IN_DELETE, GSPECIFICATION] THEN
      PROVE_TAC [],
      Q_TAC SUFF_TAC `{y | x = y DELETE e} = {x; e INSERT x}` THEN1
         SRW_TAC [][] THEN
      SRW_TAC [][EXTENSION, IN_DELETE, GSPECIFICATION] THEN METIS_TAC []
    ],
    REPEAT STRIP_TAC THEN
    `(s DELETE e) IN IMAGE (\s. s DELETE e) Q`
        by (SRW_TAC [][IN_IMAGE] THEN PROVE_TAC []) THEN
    `FINITE (s DELETE e)` by PROVE_TAC [] THEN
    PROVE_TAC [FINITE_DELETE]
  ]);
val _ = export_rewrites ["FINITE_BIGUNION_EQ"]

val SUBSET_BIGUNION_I = store_thm(
  "SUBSET_BIGUNION_I",
  ``x IN P ==> x SUBSET BIGUNION P``,
  SRW_TAC [][BIGUNION, SUBSET_DEF] THEN METIS_TAC []);

val CARD_BIGUNION_SAME_SIZED_SETS = store_thm(
  "CARD_BIGUNION_SAME_SIZED_SETS",
  ``!n s.
      FINITE s /\ (!e. e IN s ==> FINITE e /\ (CARD e = n)) /\
      (!e1 e2. e1 IN s /\ e2 IN s /\ e1 <> e2 ==> DISJOINT e1 e2) ==>
      (CARD (BIGUNION s) = CARD s * n)``,
  GEN_TAC THEN
  SIMP_TAC bool_ss [RIGHT_FORALL_IMP_THM, GSYM AND_IMP_INTRO] THEN
  Induct_on `FINITE` THEN SRW_TAC [][] THEN
  SRW_TAC [][CARD_UNION_EQN] THEN
  `e INTER BIGUNION s = {}`
    suffices_by SRW_TAC [ARITH_ss][MULT_CLAUSES] THEN
  ASM_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  Q.X_GEN_TAC `x` THEN Cases_on `x IN e` THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q.X_GEN_TAC `e1` THEN Cases_on `e1 IN s` THEN SRW_TAC [][] THEN
  STRIP_TAC THEN
  `~DISJOINT e e1`
    by (SRW_TAC [][DISJOINT_DEF, EXTENSION] THEN METIS_TAC[]) THEN
  METIS_TAC[]);

(* ----------------------------------------------------------------------
    BIGINTER (intersection of a set of sets)
   ---------------------------------------------------------------------- *)

val BIGINTER = Q.new_definition
("BIGINTER",
 `BIGINTER P = { x | !s. s IN P ==> x IN s}`);

val IN_BIGINTER = store_thm
("IN_BIGINTER",
 ``x IN BIGINTER B = !P. P IN B ==> x IN P``,
  SIMP_TAC bool_ss [BIGINTER, GSPECIFICATION, pairTheory.PAIR_EQ]);

val BIGINTER_INSERT = Q.store_thm
("BIGINTER_INSERT",
 `!P B. BIGINTER (P INSERT B) = P INTER BIGINTER B`,
  REPEAT GEN_TAC THEN CONV_TAC (REWR_CONV EXTENSION) THEN
  SIMP_TAC bool_ss [IN_BIGINTER, IN_INSERT, IN_INTER, DISJ_IMP_THM,
                    FORALL_AND_THM]);

val BIGINTER_EMPTY = Q.store_thm
("BIGINTER_EMPTY",
 `BIGINTER {} = UNIV`,
  REWRITE_TAC [EXTENSION, IN_BIGINTER, NOT_IN_EMPTY, IN_UNIV]);

val BIGINTER_INTER = Q.store_thm
("BIGINTER_INTER",
 `!P Q. BIGINTER {P; Q} = P INTER Q`,
  REWRITE_TAC [BIGINTER_EMPTY, BIGINTER_INSERT, INTER_UNIV]);

val BIGINTER_SING = Q.store_thm
("BIGINTER_SING",
 `!P. BIGINTER {P} = P`,
  SIMP_TAC bool_ss [EXTENSION, IN_BIGINTER, IN_SING] THEN
  SIMP_TAC bool_ss [GSYM EXTENSION]);

val SUBSET_BIGINTER = Q.store_thm
("SUBSET_BIGINTER",
 `!X P. X SUBSET BIGINTER P = !Y. Y IN P ==> X SUBSET Y`,
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss [IN_BIGINTER, SUBSET_DEF] THEN
  PROVE_TAC []);

val DISJOINT_BIGINTER = Q.store_thm
("DISJOINT_BIGINTER",
 `!X Y P. Y IN P /\ DISJOINT Y X ==>
            DISJOINT X (BIGINTER P) /\ DISJOINT (BIGINTER P) X`,
  SIMP_TAC bool_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
                    IN_BIGINTER] THEN PROVE_TAC []);

val BIGINTER_UNION = Q.store_thm
("BIGINTER_UNION",
 `!s1 s2. BIGINTER (s1 UNION s2) = BIGINTER s1 INTER BIGINTER s2`,
 SIMP_TAC bool_ss [IN_BIGINTER, IN_UNION, IN_INTER, EXTENSION] THEN PROVE_TAC []);

(* ====================================================================== *)
(* Cross product of sets                                                  *)
(* ====================================================================== *)


val CROSS_DEF = Q.new_definition(
  "CROSS_DEF",
  `CROSS P Q = { p | FST p IN P /\ SND p IN Q }`);
val _ = set_fixity "CROSS" (Infixl 600);
val _ = Unicode.unicode_version {tmnm = "CROSS", u = UTF8.chr 0xD7}
val _ = TeX_notation {hol = "CROSS", TeX = ("\\ensuremath{\\times}", 1)}
val _ = TeX_notation {hol = UTF8.chr 0xD7, TeX = ("\\ensuremath{\\times}", 1)}

val IN_CROSS = store_thm(
  "IN_CROSS",
  ``!P Q x. x IN (P CROSS Q) = FST x IN P /\ SND x IN Q``,
  SIMP_TAC bool_ss [GSPECIFICATION, CROSS_DEF, PAIR_EQ]);
val _ = export_rewrites ["IN_CROSS"]

val CROSS_EMPTY = store_thm(
  "CROSS_EMPTY",
  ``!P. (P CROSS {} = {}) /\ ({} CROSS P = {})``,
  SIMP_TAC bool_ss [EXTENSION, IN_CROSS, NOT_IN_EMPTY]);
val _ = export_rewrites ["CROSS_EMPTY"]

val CROSS_INSERT_LEFT = store_thm(
  "CROSS_INSERT_LEFT",
  ``!P Q x. (x INSERT P) CROSS Q = ({x} CROSS Q) UNION (P CROSS Q)``,
  SIMP_TAC bool_ss [EXTENSION, IN_CROSS, IN_UNION, IN_INSERT,
                    NOT_IN_EMPTY] THEN
  MESON_TAC []);

val CROSS_INSERT_RIGHT = store_thm(
  "CROSS_INSERT_RIGHT",
  ``!P Q x. P CROSS (x INSERT Q) = (P CROSS {x}) UNION (P CROSS Q)``,
  SIMP_TAC bool_ss [EXTENSION, IN_CROSS, IN_UNION, IN_INSERT,
                    NOT_IN_EMPTY] THEN
  MESON_TAC []);

val FINITE_CROSS = store_thm(
  "FINITE_CROSS",
  ``!P Q. FINITE P /\ FINITE Q ==> FINITE (P CROSS Q)``,
  SIMP_TAC bool_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss [CROSS_EMPTY, FINITE_EMPTY] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CROSS_INSERT_LEFT] THEN
  ASM_SIMP_TAC bool_ss [FINITE_UNION] THEN
  REWRITE_TAC [FINITE_WEAK_ENUMERATE] THEN
  `?f b. !x. x IN Q = ?n. n < b /\ (x = f n)`
     by ASM_MESON_TAC [FINITE_WEAK_ENUMERATE] THEN
  Q.EXISTS_TAC `\m. (e, f m)` THEN Q.EXISTS_TAC `b` THEN
  ASM_SIMP_TAC bool_ss [IN_CROSS, IN_INSERT, NOT_IN_EMPTY] THEN
  GEN_TAC THEN Cases_on `e'` THEN
  SIMP_TAC bool_ss [PAIR_EQ, FST, SND] THEN MESON_TAC []);

val CROSS_SINGS = store_thm(
  "CROSS_SINGS",
  ``!x y. {x} CROSS {y} = {(x,y)}``,
  SIMP_TAC bool_ss [EXTENSION, IN_INSERT, IN_CROSS, NOT_IN_EMPTY] THEN
  MESON_TAC [PAIR, FST, SND]);
val _ = export_rewrites ["CROSS_SINGS"]

val CARD_SING_CROSS = store_thm(
  "CARD_SING_CROSS",
  ``!x P. FINITE P ==> (CARD ({x} CROSS P) = CARD P)``,
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss [CROSS_EMPTY, CARD_EMPTY] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [CROSS_INSERT_RIGHT] THEN
  ASM_SIMP_TAC bool_ss [CROSS_SINGS, GSYM INSERT_SING_UNION] THEN
  `FINITE ({x} CROSS P)` by ASM_MESON_TAC [FINITE_SING, FINITE_CROSS] THEN
  `~((x,e) IN ({x} CROSS P))`
     by ASM_MESON_TAC [IN_CROSS, FST, SND, IN_SING] THEN
  ASM_SIMP_TAC bool_ss [CARD_INSERT]);

val CARD_CROSS = store_thm(
  "CARD_CROSS",
  ``!P Q. FINITE P /\ FINITE Q ==> (CARD (P CROSS Q) = CARD P * CARD Q)``,
  SIMP_TAC bool_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss [CROSS_EMPTY, CARD_EMPTY, CARD_INSERT,
                    MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC [CROSS_INSERT_LEFT] THEN
  REPEAT STRIP_TAC THEN
  `FINITE (P CROSS Q)` by ASM_MESON_TAC [FINITE_CROSS] THEN
  `FINITE ({e} CROSS Q)` by ASM_MESON_TAC [FINITE_CROSS, FINITE_SING] THEN
  Q.SUBGOAL_THEN `({e} CROSS Q) INTER (P CROSS Q) = {}` ASSUME_TAC THENL [
    SIMP_TAC bool_ss [IN_INTER, EXTENSION, IN_CROSS, IN_SING,
                      NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [],
    ALL_TAC
  ] THEN
  CONV_TAC (LHS_CONV (REWR_CONV (GSYM ADD_0))) THEN
  POP_ASSUM (SUBST1_TAC o GSYM o REWRITE_RULE [CARD_EMPTY] o
             Q.AP_TERM `CARD`) THEN
  ASM_SIMP_TAC bool_ss [CARD_UNION, CARD_SING_CROSS, ADD_COMM]);

val CROSS_SUBSET = store_thm(
  "CROSS_SUBSET",
  Term`!P Q P0 Q0. (P0 CROSS Q0) SUBSET (P CROSS Q) =
                   (P0 = {}) \/ (Q0 = {}) \/
                   P0 SUBSET P /\ Q0 SUBSET Q`,
  SIMP_TAC bool_ss [IN_CROSS, SUBSET_DEF, FORALL_PROD, FST, SND,
                    NOT_IN_EMPTY, EXTENSION] THEN
  MESON_TAC []);


val FINITE_CROSS_EQ_lemma0 = prove(
  Term`!x. FINITE x ==>
           !P Q. (x = P CROSS Q) ==>
                 (P = {}) \/ (Q = {}) \/ FINITE P /\ FINITE Q`,
  HO_MATCH_MP_TAC FINITE_COMPLETE_INDUCTION THEN
  REPEAT STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  `(P = {}) \/ ?p P0. (P = p INSERT P0) /\ ~(p IN P0)` by
     MESON_TAC [SET_CASES] THEN
  `(Q = {}) \/ ?q Q0. (Q = q INSERT Q0) /\ ~(q IN Q0)` by
     MESON_TAC [SET_CASES] THEN
  ASM_SIMP_TAC bool_ss [NOT_INSERT_EMPTY, FINITE_INSERT] THEN
  REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  Q.PAT_ASSUM `FINITE X` MP_TAC THEN
  ONCE_REWRITE_TAC [CROSS_INSERT_LEFT] THEN
  ONCE_REWRITE_TAC [CROSS_INSERT_RIGHT] THEN
  SIMP_TAC bool_ss [FINITE_UNION, FINITE_SING, CROSS_SINGS] THEN
  REPEAT STRIP_TAC THENL [
    Q.SUBGOAL_THEN
       `(P0 CROSS {q}) PSUBSET ((p INSERT P0) CROSS (q INSERT Q0)) \/
        (P0 = {})`
    STRIP_ASSUME_TAC THENL [
      ASM_SIMP_TAC bool_ss [PSUBSET_DEF, CROSS_SUBSET, SUBSET_INSERT,
                            SUBSET_REFL, EXTENSION, IN_CROSS, IN_INSERT,
                            FORALL_PROD, FST, SND, NOT_IN_EMPTY,
                            SUBSET_DEF, IN_SING] THEN
      ASM_MESON_TAC [],
      POP_ASSUM (ANTE_RES_THEN (MP_TAC o Q.SPECL [`P0`, `{q}`])) THEN
      MESON_TAC [FINITE_EMPTY, NOT_INSERT_EMPTY],
      ASM_SIMP_TAC bool_ss [FINITE_EMPTY]
    ],
    Q.SUBGOAL_THEN
       `({p} CROSS Q0) PSUBSET ((p INSERT P0) CROSS (q INSERT Q0)) \/
        (Q0 = {})`
    STRIP_ASSUME_TAC THENL [
      ASM_SIMP_TAC bool_ss [PSUBSET_DEF, CROSS_SUBSET, SUBSET_INSERT,
                            SUBSET_REFL, EXTENSION, IN_CROSS, IN_INSERT,
                            FORALL_PROD, FST, SND, NOT_IN_EMPTY,
                            SUBSET_DEF, IN_SING] THEN
      ASM_MESON_TAC [],
      POP_ASSUM (ANTE_RES_THEN (MP_TAC o Q.SPECL [`{p}`, `Q0`])) THEN
      MESON_TAC [FINITE_EMPTY, NOT_INSERT_EMPTY],
      ASM_SIMP_TAC bool_ss [FINITE_EMPTY]
    ]
  ]);

val FINITE_CROSS_EQ_lemma =
  SIMP_RULE bool_ss [GSYM RIGHT_FORALL_IMP_THM] FINITE_CROSS_EQ_lemma0

val FINITE_CROSS_EQ = store_thm(
  "FINITE_CROSS_EQ",
  ``!P Q. FINITE (P CROSS Q)
             =
          (P = {}) \/ (Q = {}) \/ FINITE P /\ FINITE Q``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  MESON_TAC [FINITE_CROSS_EQ_lemma, FINITE_CROSS, FINITE_EMPTY,
             CROSS_EMPTY]);
val _ = export_rewrites ["FINITE_CROSS_EQ"]

val CROSS_UNIV = store_thm(
  "CROSS_UNIV",
  ``univ(:'a # 'b) = univ(:'a) CROSS univ(:'b)``,
  SRW_TAC [][EXTENSION]);

val INFINITE_PAIR_UNIV = store_thm(
  "INFINITE_PAIR_UNIV",
  ``(FINITE univ(:'a # 'b) = FINITE univ(:'a) /\ FINITE univ(:'b))``,
  FULL_SIMP_TAC (srw_ss()) [CROSS_UNIV]);
val _ = export_rewrites ["INFINITE_PAIR_UNIV"]

(* sums *)

val SUM_UNIV = store_thm(
  "SUM_UNIV",
  ``univ(:'a + 'b) = IMAGE INL univ(:'a) UNION IMAGE INR univ(:'b)``,
  SRW_TAC[][EQ_IMP_THM, EXTENSION] THEN METIS_TAC [sumTheory.sum_CASES]);

val INJ_INL = store_thm(
  "INJ_INL",
  ``(!x. x IN s ==> INL x IN t) ==> INJ INL s t``,
  SIMP_TAC (srw_ss()) [INJ_DEF])
val INJ_INR = store_thm(
  "INJ_INR",
  ``(!x. x IN s ==> INR x IN t) ==> INJ INR s t``,
  SIMP_TAC (srw_ss()) [INJ_DEF])

(* ====================================================================== *)
(* Set complements.                                                       *)
(* ====================================================================== *)

val COMPL_DEF = new_definition ("COMPL_DEF", ``COMPL P = UNIV DIFF P``);

val IN_COMPL = store_thm
  ("IN_COMPL",
   ``!(x:'a) s. x IN COMPL s = ~(x IN s)``,
   SIMP_TAC bool_ss [COMPL_DEF, IN_DIFF, IN_UNIV]);

val COMPL_COMPL = store_thm
  ("COMPL_COMPL",
   ``!(s:'a->bool). COMPL (COMPL s) = s``,
   SIMP_TAC bool_ss [EXTENSION, IN_COMPL]);

val COMPL_CLAUSES = store_thm
  ("COMPL_CLAUSES",
   ``!(s:'a->bool). (COMPL s INTER s = {})
                    /\ (COMPL s UNION s = UNIV)``,
   SIMP_TAC bool_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION, NOT_IN_EMPTY,
                     IN_UNIV]);

val COMPL_SPLITS = store_thm
  ("COMPL_SPLITS",
   ``!(p:'a->bool) q. p INTER q UNION COMPL p INTER q = q``,
   SIMP_TAC bool_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION, NOT_IN_EMPTY,
                     IN_UNIV]
   THEN MESON_TAC []);

val INTER_UNION_COMPL = store_thm
  ("INTER_UNION_COMPL",
   ``!(s:'a->bool) t. s INTER t
                      = COMPL (COMPL s UNION COMPL t)``,
   SIMP_TAC bool_ss [EXTENSION, IN_COMPL, IN_INTER, IN_UNION, NOT_IN_EMPTY,
                     IN_UNIV]);

val COMPL_EMPTY = store_thm
  ("COMPL_EMPTY",
   ``COMPL {} = UNIV``,
   SIMP_TAC bool_ss [EXTENSION, IN_COMPL, NOT_IN_EMPTY, IN_UNIV]);

val COMPL_INTER = store_thm(
  "COMPL_INTER",
  ``(x INTER COMPL x = {}) /\ (COMPL x INTER x = {})``,
  SRW_TAC [][EXTENSION, IN_COMPL]);
val _ = export_rewrites ["COMPL_INTER"]

val COMPL_UNION = Q.store_thm(
"COMPL_UNION",
`COMPL (s UNION t) = COMPL s INTER COMPL t`,
SRW_TAC [][EXTENSION,COMPL_DEF]);

(* ====================================================================== *)
(* Sets of size n.                                                        *)
(* ====================================================================== *)

val count_def = new_definition ("count_def", ``count (n:num) = {m | m < n}``);

val IN_COUNT = store_thm
  ("IN_COUNT",
   ``!m n. m IN count n = m < n``,
   RW_TAC bool_ss [GSPECIFICATION, count_def]);
val _ = export_rewrites ["IN_COUNT"]

val COUNT_ZERO = store_thm
  ("COUNT_ZERO",
   ``count 0 = {}``,
   RW_TAC bool_ss [EXTENSION, IN_COUNT, NOT_IN_EMPTY]
   THEN CONV_TAC Arith.ARITH_CONV);
val _ = export_rewrites ["COUNT_ZERO"]

val COUNT_SUC = store_thm
  ("COUNT_SUC",
   ``!n. count (SUC n) = n INSERT count n``,
   RW_TAC bool_ss [EXTENSION, IN_INSERT, IN_COUNT]
   THEN CONV_TAC Arith.ARITH_CONV);

val FINITE_COUNT = store_thm
  ("FINITE_COUNT",
   ``!n. FINITE (count n)``,
   Induct THENL
   [RW_TAC bool_ss [COUNT_ZERO, FINITE_EMPTY],
    RW_TAC bool_ss [COUNT_SUC, FINITE_INSERT]]);
val _ = export_rewrites ["FINITE_COUNT"]

val CARD_COUNT = store_thm
  ("CARD_COUNT",
   ``!n. CARD (count n) = n``,
   Induct THENL
   [RW_TAC bool_ss [COUNT_ZERO, CARD_EMPTY],
    RW_TAC bool_ss [COUNT_SUC, CARD_INSERT, FINITE_COUNT, IN_COUNT]
    THEN POP_ASSUM MP_TAC
    THEN CONV_TAC Arith.ARITH_CONV]);
val _ = export_rewrites ["CARD_COUNT"]

val COUNT_11 = store_thm(
  "COUNT_11",
  ``(count n1 = count n2) <=> (n1 = n2)``,
  SRW_TAC [][EQ_IMP_THM, EXTENSION] THEN
  METIS_TAC [numLib.ARITH_PROVE ``x:num < y <=> ~(y <= x)``,
             arithmeticTheory.LESS_EQ_REFL,
             arithmeticTheory.LESS_EQUAL_ANTISYM]);
val _ = export_rewrites ["COUNT_11"]

(*---------------------------------------------------------------------------
    A "fold"-like operation for sets.
 ---------------------------------------------------------------------------*)

val ITSET_def =
 let open TotalDefn
 in
   tDefine "ITSET"
    `ITSET (s:'a->bool) (b:'b) =
       if FINITE s then
          if s={} then b
          else ITSET (REST s) (f (CHOICE s) b)
       else ARB`
  (WF_REL_TAC `measure (CARD o FST)` THEN
   METIS_TAC [CARD_PSUBSET, REST_PSUBSET])
 end;

val ITSET_IND = fetch "-" "ITSET_ind";

(*---------------------------------------------------------------------------
      Desired recursion equation.

     |- FINITE s ==> ITSET f s b = if s = {} then b
                                  else ITSET f (REST s) (f (CHOICE s) b)
 ---------------------------------------------------------------------------*)

val ITSET_THM =
W (GENL o rev o free_vars o concl)
  (DISCH_ALL(ASM_REWRITE_RULE [ASSUME ``FINITE s``] (SPEC_ALL ITSET_def)));

val _ = save_thm("ITSET_IND",ITSET_IND);
val _ = save_thm("ITSET_THM",ITSET_THM);
val _ = save_thm("ITSET_EMPTY",
                  REWRITE_RULE []
                      (MATCH_MP (SPEC ``{}`` ITSET_THM) FINITE_EMPTY));

(* Could also prove by

    PROVE_TAC [FINITE_INSERT,ITSET_THM,NOT_INSERT_EMPTY]);
*)
val ITSET_INSERT = Q.store_thm
("ITSET_INSERT",
 `!s. FINITE s ==>
        !f x b. ITSET f (x INSERT s) b =
                ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (fn th =>
    `FINITE (x INSERT s)` by PROVE_TAC [th, FINITE_INSERT]) THEN
  IMP_RES_TAC ITSET_THM THEN
  POP_ASSUM (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  SIMP_TAC bool_ss [NOT_INSERT_EMPTY]);

val absorption = #1 (EQ_IMP_RULE (SPEC_ALL ABSORPTION))
val delete_non_element = #1 (EQ_IMP_RULE (SPEC_ALL DELETE_NON_ELEMENT))

val COMMUTING_ITSET_INSERT = Q.store_thm
("COMMUTING_ITSET_INSERT",
 `!f s. (!x y z. f x (f y z) = f y (f x z)) /\
          FINITE s ==>
          !x b. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  completeInduct_on `CARD s` THEN
  POP_ASSUM (ASSUME_TAC o SIMP_RULE bool_ss
        [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) THEN
  GEN_TAC THEN SIMP_TAC bool_ss [ITSET_INSERT] THEN
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `t = REST (x INSERT s)` THEN
  Q.ABBREV_TAC `y = CHOICE (x INSERT s)` THEN
  `~(y IN t)` by PROVE_TAC [CHOICE_NOT_IN_REST] THEN
  Cases_on `x IN s` THENL [
    FULL_SIMP_TAC bool_ss [absorption] THEN
    Cases_on `x = y` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN
      Q_TAC SUFF_TAC `t = s DELETE y` THEN1 SRW_TAC [][] THEN
      `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] THEN
      SRW_TAC [][DELETE_INSERT, delete_non_element],
      `s = y INSERT t` by PROVE_TAC [NOT_IN_EMPTY, CHOICE_INSERT_REST] THEN
      `x IN t` by PROVE_TAC [IN_INSERT] THEN
      Q.ABBREV_TAC `u = t DELETE x` THEN
      `t = x INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] THEN
      `~(x IN u)` by PROVE_TAC [IN_DELETE] THEN
      `s = x INSERT (y INSERT u)` by SRW_TAC [][INSERT_COMM] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FULL_SIMP_TAC bool_ss [FINITE_INSERT, CARD_INSERT, DELETE_INSERT,
                             IN_INSERT] THEN
      ASM_SIMP_TAC arith_ss [delete_non_element]
    ],
    ALL_TAC
  ] THEN (* ~(x IN s) *)
  ASM_SIMP_TAC bool_ss [delete_non_element] THEN
  `x INSERT s = y INSERT t`
     by PROVE_TAC [NOT_EMPTY_INSERT, CHOICE_INSERT_REST] THEN
  Cases_on `x = y` THENL [
    POP_ASSUM SUBST_ALL_TAC THEN
    Q_TAC SUFF_TAC `t = s` THEN1 SRW_TAC [][] THEN
    FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] THEN PROVE_TAC [],
    ALL_TAC
  ] THEN (* ~(x = y) *)
  `x IN t /\ y IN s` by PROVE_TAC [IN_INSERT] THEN
  Q.ABBREV_TAC `u = s DELETE y` THEN
  `~(y IN u)` by PROVE_TAC [IN_DELETE] THEN
  `s = y INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  FULL_SIMP_TAC bool_ss [IN_INSERT, FINITE_INSERT, CARD_INSERT,
                         DELETE_INSERT, delete_non_element] THEN
  `t = x INSERT u` by
     (FULL_SIMP_TAC bool_ss [EXTENSION, IN_INSERT] THEN PROVE_TAC []) THEN
  ASM_SIMP_TAC arith_ss [delete_non_element]);

val COMMUTING_ITSET_RECURSES = store_thm(
  "COMMUTING_ITSET_RECURSES",
  ``!f e s b. (!x y z. f x (f y z) = f y (f x z)) /\ FINITE s ==>
              (ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b))``,
  Q_TAC SUFF_TAC
    `!f. (!x y z. f x (f y z) = f y (f x z)) ==>
         !s. FINITE s ==>
             !e b. ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b)` THEN1
    PROVE_TAC [] THEN
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [COMMUTING_ITSET_INSERT] THEN
  Q_TAC SUFF_TAC
    `!s. FINITE s ==> !e b. ITSET f s (f e b) = f e (ITSET f s b)` THEN1
    PROVE_TAC [FINITE_DELETE] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL [
    SIMP_TAC bool_ss [ITSET_THM, FINITE_EMPTY],
    ASM_SIMP_TAC bool_ss [COMMUTING_ITSET_INSERT, delete_non_element]
  ]);

(* ----------------------------------------------------------------------
    SUM_IMAGE

    This constant is the same as standard mathematics \Sigma operator:

     \Sigma_{x\in P}{f(x)} = SUM_IMAGE f P

    Where f's range is the natural numbers and P is finite.
   ---------------------------------------------------------------------- *)

val SUM_IMAGE_DEF = new_definition(
  "SUM_IMAGE_DEF",
  ``SUM_IMAGE f s = ITSET (\e acc. f e + acc) s 0``);

val _ = overload_on ("SIGMA", ``SUM_IMAGE``)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2211, tmnm = "SIGMA"}

val SUM_IMAGE_THM = store_thm(
  "SUM_IMAGE_THM",
  ``!f. (SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (SUM_IMAGE f (e INSERT s) =
                f e + SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THENL [
    SIMP_TAC (srw_ss()) [ITSET_THM, SUM_IMAGE_DEF],
    SIMP_TAC (srw_ss()) [SUM_IMAGE_DEF] THEN
    Q.ABBREV_TAC `g = \e acc. f e + acc` THEN
    Q_TAC SUFF_TAC `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)` THEN1
       SRW_TAC [][Abbr`g`] THEN
    MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
    SRW_TAC [ARITH_ss][Abbr`g`]
  ]);

val SUM_IMAGE_SING = store_thm(
  "SUM_IMAGE_SING",
  ``!f e. SUM_IMAGE f {e} = f e``,
  SRW_TAC [][SUM_IMAGE_THM]);

val SUM_IMAGE_SUBSET_LE = store_thm(
  "SUM_IMAGE_SUBSET_LE",
  ``!f s t. FINITE s /\ t SUBSET s ==> SUM_IMAGE f t <= SUM_IMAGE f s``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!s. FINITE s ==>
                      !t. t SUBSET s ==> SUM_IMAGE f t <= SUM_IMAGE f s` THEN1
    PROVE_TAC [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC (srw_ss()) [SUM_IMAGE_THM, delete_non_element] THEN
  REPEAT STRIP_TAC THEN Cases_on `e IN t` THENL [
    Q.ABBREV_TAC `u = t DELETE e` THEN
    `t = e INSERT u` by SRW_TAC [][INSERT_DELETE, Abbr`u`] THEN
    `FINITE u` by PROVE_TAC [FINITE_DELETE, SUBSET_FINITE, FINITE_INSERT] THEN
    `~(e IN u)` by PROVE_TAC [IN_DELETE] THEN
    ASM_SIMP_TAC arith_ss [SUM_IMAGE_THM, delete_non_element] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC bool_ss [SUBSET_INSERT_DELETE],
    FULL_SIMP_TAC bool_ss [SUBSET_INSERT] THEN
    RES_TAC THEN ASM_SIMP_TAC arith_ss []
  ]);

val SUM_IMAGE_IN_LE = store_thm(
  "SUM_IMAGE_IN_LE",
  ``!f s e. FINITE s /\ e IN s ==> f e <= SUM_IMAGE f s``,
  REPEAT STRIP_TAC THEN
  `{e} SUBSET s` by SRW_TAC [][SUBSET_DEF] THEN
  PROVE_TAC [SUM_IMAGE_SING, SUM_IMAGE_SUBSET_LE]);

val SUM_IMAGE_DELETE = store_thm(
  "SUM_IMAGE_DELETE",
  ``!f s. FINITE s ==>
          !e. SUM_IMAGE f (s DELETE e) = if e IN s then SUM_IMAGE f s - f e
                                         else SUM_IMAGE f s``,
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][SUM_IMAGE_THM, DELETE_INSERT] THEN
  COND_CASES_TAC THENL [
    POP_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC arith_ss [],
    ASM_SIMP_TAC bool_ss [SUM_IMAGE_THM, FINITE_DELETE, IN_DELETE,
                          delete_non_element] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN
    `f e' <= SUM_IMAGE f s` by PROVE_TAC [SUM_IMAGE_IN_LE] THEN
    FULL_SIMP_TAC arith_ss []
  ]);

val SUM_IMAGE_UNION = store_thm(
  "SUM_IMAGE_UNION",
  ``!f s t. FINITE s /\ FINITE t ==>
            (SUM_IMAGE f (s UNION t) =
             SUM_IMAGE f s + SUM_IMAGE f t - SUM_IMAGE f (s INTER t))``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC
    `!s. FINITE s ==>
         !t. FINITE t ==>
             (SUM_IMAGE f (s UNION t) =
              SUM_IMAGE f s + SUM_IMAGE f t - SUM_IMAGE f (s INTER t))` THEN1
    PROVE_TAC [] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THEN1
    SRW_TAC [ARITH_ss][SUM_IMAGE_THM] THEN
  SIMP_TAC (srw_ss()) [INSERT_UNION_EQ, SUM_IMAGE_THM, INSERT_INTER] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `e IN t` THEN
  ASM_SIMP_TAC arith_ss [INSERT_INTER, INTER_FINITE, FINITE_INSERT,
                         SUM_IMAGE_THM, IN_UNION, delete_non_element]
  THENL [
    `s UNION t DELETE e = s UNION (t DELETE e)` by
       (SRW_TAC [][EXTENSION, IN_UNION, IN_DELETE] THEN PROVE_TAC []) THEN
    ASM_SIMP_TAC bool_ss [FINITE_DELETE, SUM_IMAGE_DELETE, INTER_FINITE,
                          IN_INTER] THEN
    `s INTER (t DELETE e) = s INTER t DELETE e` by
       (SRW_TAC [][EXTENSION, IN_DELETE] THEN PROVE_TAC []) THEN
    ASM_SIMP_TAC bool_ss [SUM_IMAGE_DELETE, INTER_FINITE, IN_INTER] THEN
    `f e <= SUM_IMAGE f t` by PROVE_TAC [SUM_IMAGE_IN_LE] THEN
    `s INTER t SUBSET t` by PROVE_TAC [INTER_SUBSET] THEN
    `SUM_IMAGE f (s INTER t) <= SUM_IMAGE f t` by
       PROVE_TAC [SUM_IMAGE_SUBSET_LE] THEN
    Q_TAC SUFF_TAC `f e + SUM_IMAGE f (s INTER t) <= SUM_IMAGE f t` THEN1
       ASM_SIMP_TAC arith_ss [] THEN
    Q_TAC SUFF_TAC
          `f e + SUM_IMAGE f (s INTER t) =
             SUM_IMAGE f (e INSERT s INTER t)` THEN1
          ASM_SIMP_TAC bool_ss [SUM_IMAGE_SUBSET_LE,
                                SUBSET_DEF, IN_INTER, IN_INSERT,
                                DISJ_IMP_THM, FORALL_AND_THM] THEN
    ASM_SIMP_TAC bool_ss [INTER_FINITE, SUM_IMAGE_THM, IN_INTER,
                          delete_non_element],
    `s INTER t SUBSET t` by PROVE_TAC [INTER_SUBSET] THEN
    `SUM_IMAGE f (s INTER t) <= SUM_IMAGE f t`
       by PROVE_TAC [SUM_IMAGE_SUBSET_LE] THEN
    ASM_SIMP_TAC arith_ss []
  ]);

val SUM_IMAGE_lower_bound = store_thm(
  "SUM_IMAGE_lower_bound",
  ``!s. FINITE s ==>
        !n. (!x. x IN s ==> n <= f x) ==>
            CARD s * n <= SUM_IMAGE f s``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][DISJ_IMP_THM, FORALL_AND_THM, SUM_IMAGE_THM,
             MULT_CLAUSES, CARD_EMPTY, CARD_INSERT] THEN
  `s DELETE e = s` by (SRW_TAC [][EXTENSION, IN_DELETE] THEN PROVE_TAC []) THEN
  SRW_TAC [][] THEN
  PROVE_TAC [LESS_EQ_LESS_EQ_MONO, ADD_COMM]);

val SUM_IMAGE_upper_bound = store_thm(
  "SUM_IMAGE_upper_bound",
  ``!s. FINITE s ==>
        !n. (!x. x IN s ==> f x <= n) ==>
            SUM_IMAGE f s <= CARD s * n``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SRW_TAC [][DISJ_IMP_THM, FORALL_AND_THM, SUM_IMAGE_THM,
             MULT_CLAUSES, CARD_EMPTY, CARD_INSERT] THEN
  `s DELETE e = s` by (SRW_TAC [][EXTENSION, IN_DELETE] THEN PROVE_TAC []) THEN
  SRW_TAC [][] THEN
  PROVE_TAC [LESS_EQ_LESS_EQ_MONO, ADD_COMM]);

val DISJ_BIGUNION_CARD = Q.prove (
`!P. FINITE P
     ==> (!s. s IN P ==> FINITE s) /\
         (!s t. s IN P /\ t IN P /\ ~(s = t) ==> DISJOINT s t)
     ==> (CARD (BIGUNION P) = SUM_IMAGE CARD P)`,
  SET_INDUCT_TAC THEN
  RW_TAC bool_ss [CARD_EMPTY,BIGUNION_EMPTY,SUM_IMAGE_THM,
                  BIGUNION_INSERT] THEN
  `FINITE (BIGUNION s) /\ FINITE e`
     by METIS_TAC [FINITE_BIGUNION, IN_INSERT] THEN
  `!s'. s' IN s ==> DISJOINT e s'`  by METIS_TAC [IN_INSERT] THEN
  `CARD (e INTER (BIGUNION s)) = 0`
     by METIS_TAC [DISJOINT_DEF,DISJOINT_BIGUNION,CARD_EMPTY] THEN
  `CARD (e UNION BIGUNION s) = CARD (e UNION BIGUNION s) +
                               CARD (e INTER (BIGUNION s))`
    by RW_TAC arith_ss [] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  FULL_SIMP_TAC arith_ss [CARD_UNION, DELETE_NON_ELEMENT] THEN
  METIS_TAC [IN_INSERT]);

val SUM_SAME_IMAGE = Q.store_thm
("SUM_SAME_IMAGE",
 `!P. FINITE P
     ==> !f p. p IN P /\ (!q. q IN P ==> (f p = f q))
               ==> (SUM_IMAGE f P = CARD P * f p)`,
  SET_INDUCT_TAC THEN
  RW_TAC arith_ss [CARD_EMPTY, SUM_IMAGE_THM, CARD_INSERT, ADD1] THEN
  SRW_TAC [][delete_non_element] THEN
  `(s = {}) \/ (?x t. s = x INSERT t)`
      by METIS_TAC [TypeBase.nchotomy_of ``:'a set``]
  THENL [
    SRW_TAC [][SUM_IMAGE_THM],
    `(f e = f x) /\ (f p = f x)`
        by (FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
    Q_TAC SUFF_TAC `SIGMA f s = CARD s * f x`
          THEN1 SRW_TAC [ARITH_ss][] THEN
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) []
  ]);

val SUM_IMAGE_CONG = Q.store_thm(
"SUM_IMAGE_CONG",
`(s1 = s2) /\ (!x. x IN s2 ==> (f1 x = f2 x))
 ==> (SIGMA f1 s1 = SIGMA f2 s2)`,
SRW_TAC [][] THEN
REVERSE (Cases_on `FINITE s1`) THEN1 (
  SRW_TAC [][SUM_IMAGE_DEF,Once ITSET_def] THEN
  SRW_TAC [][Once ITSET_def] ) THEN
Q.PAT_ASSUM `!x.P` MP_TAC THEN
POP_ASSUM MP_TAC THEN
Q.ID_SPEC_TAC `s1` THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][SUM_IMAGE_THM,SUM_IMAGE_DELETE])
val _ = DefnBase.export_cong "SUM_IMAGE_CONG"

val SUM_IMAGE_ZERO = Q.store_thm(
"SUM_IMAGE_ZERO",
`!s. FINITE s ==> ((SIGMA f s = 0) <=> (!x. x IN s ==> (f x = 0)))`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
CONJ_TAC THEN1 SIMP_TAC bool_ss [SUM_IMAGE_THM,NOT_IN_EMPTY] THEN
SIMP_TAC bool_ss [SUM_IMAGE_THM,DELETE_NON_ELEMENT,ADD_EQ_0,IN_INSERT] THEN
METIS_TAC [])

val ABS_DIFF_SUM_IMAGE = Q.store_thm(
"ABS_DIFF_SUM_IMAGE",
`!s. FINITE s ==> (ABS_DIFF (SIGMA f s) (SIGMA g s) <= SIGMA (\x. ABS_DIFF (f x) (g x)) s)`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][] THEN1 (
  SRW_TAC [][SUM_IMAGE_THM,ABS_DIFF_EQS] ) THEN
SRW_TAC [][SUM_IMAGE_THM] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
MATCH_MP_TAC LESS_EQ_TRANS THEN
Q.EXISTS_TAC `ABS_DIFF (f e) (g e) + ABS_DIFF (SIGMA f s) (SIGMA g s)` THEN
SRW_TAC [][ABS_DIFF_SUMS])

val SUM_IMAGE_MONO_LESS_EQ = Q.store_thm(
"SUM_IMAGE_MONO_LESS_EQ",
`!s. FINITE s ==> (!x. x IN s ==> f x <= g x)
  ==> SUM_IMAGE f s <= SUM_IMAGE g s`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][SUM_IMAGE_THM] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO THEN
SRW_TAC [][]);

val SUM_IMAGE_MONO_LESS = Q.store_thm(
"SUM_IMAGE_MONO_LESS",
`!s. FINITE s ==> (?x. x IN s /\ f x < g x) /\ (!x. x IN s ==> f x <= g x)
  ==> SUM_IMAGE f s < SUM_IMAGE g s`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [][SUM_IMAGE_THM] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN1 (
  MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  Q.EXISTS_TAC `g e + SIGMA f s` THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (MP_CANON SUM_IMAGE_MONO_LESS_EQ) THEN
  SRW_TAC [][] ) THEN
`SIGMA f s < SIGMA g s` by METIS_TAC [] THEN
MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
Q.EXISTS_TAC `f e + SIGMA g s` THEN
SRW_TAC [][]);

(*---------------------------------------------------------------------------*)
(* Support for Cases, Cases_on, Induct, and termination proofs               *)
(*---------------------------------------------------------------------------*)

val set_tyinfo = TypeBasePure.mk_nondatatype_info
                      (``:'a set``,
                       {nchotomy = SOME SET_CASES,
                        induction = SOME FINITE_INDUCT,
                        size=SOME(``\(x:'a->num) (y:'b). SUM_IMAGE x``,SUM_IMAGE_THM),
                        encode=NONE});

val _ = TypeBase.write [set_tyinfo];

(*---------------------------------------------------------------------------*)
(* SUM_SET sums the elements of a set of natural numbers                     *)
(*---------------------------------------------------------------------------*)

val SUM_SET_DEF = new_definition("SUM_SET_DEF", ``SUM_SET = SUM_IMAGE I``);

val SUM_SET_THM = store_thm(
  "SUM_SET_THM",
  ``(SUM_SET {} = 0) /\
    (!x s. FINITE s ==> (SUM_SET (x INSERT s) = x + SUM_SET (s DELETE x)))``,
  SRW_TAC [][SUM_SET_DEF, SUM_IMAGE_THM]);

val SUM_SET_EMPTY = save_thm("SUM_SET_EMPTY", CONJUNCT1 SUM_SET_THM)
val _ = export_rewrites ["SUM_SET_EMPTY"]

val SUM_SET_SING = store_thm(
  "SUM_SET_SING",
  ``!n. SUM_SET {n} = n``,
  SRW_TAC [][SUM_SET_DEF, SUM_IMAGE_SING]);
val _ = export_rewrites ["SUM_SET_SING"]

val SUM_SET_SUBSET_LE = store_thm(
  "SUM_SET_SUBSET_LE",
  ``!s t. FINITE t /\ s SUBSET t ==> SUM_SET s <= SUM_SET t``,
  SRW_TAC [][SUM_SET_DEF, SUM_IMAGE_SUBSET_LE]);

val SUM_SET_IN_LE = store_thm(
  "SUM_SET_IN_LE",
  ``!x s. FINITE s /\ x IN s ==> x <= SUM_SET s``,
  SRW_TAC [][SUM_SET_DEF] THEN
  PROVE_TAC [combinTheory.I_THM, SUM_IMAGE_IN_LE]);

val SUM_SET_DELETE = store_thm(
  "SUM_SET_DELETE",
  ``!s. FINITE s ==> !e. SUM_SET (s DELETE e) = if e IN s then SUM_SET s - e
                                                else SUM_SET s``,
  SIMP_TAC (srw_ss()) [SUM_SET_DEF, SUM_IMAGE_DELETE]);

val SUM_SET_UNION = store_thm(
  "SUM_SET_UNION",
  ``!s t. FINITE s /\ FINITE t ==>
          (SUM_SET (s UNION t) =
             SUM_SET s + SUM_SET t - SUM_SET (s INTER t))``,
  SRW_TAC [][SUM_SET_DEF, SUM_IMAGE_UNION]);

(* ----------------------------------------------------------------------
    PROD_IMAGE

    This construct is the same as standard mathematics \Pi operator:

     \Pi_{x\in P}{f(x)} = PROD_IMAGE f P

    Where f's range is the natural numbers and P is finite.
   ---------------------------------------------------------------------- *)

(* Define PROD_IMAGE similar to SUM_IMAGE *)
val PROD_IMAGE_DEF = new_definition(
  "PROD_IMAGE_DEF",
  ``PROD_IMAGE f s = ITSET (\e acc. f e * acc) s 1``);

(* Theorem: property of PROD_IMAGE *)
val PROD_IMAGE_THM = store_thm(
  "PROD_IMAGE_THM",
  ``!f. (PROD_IMAGE f {} = 1) /\
        (!e s. FINITE s ==>
          (PROD_IMAGE f (e INSERT s) = f e * PROD_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THEN1
    SIMP_TAC (srw_ss()) [ITSET_THM, PROD_IMAGE_DEF] THEN
  SIMP_TAC (srw_ss()) [PROD_IMAGE_DEF] THEN
  Q.ABBREV_TAC `g = \e acc. f e * acc` THEN
  Q_TAC SUFF_TAC `ITSET g (e INSERT s) 1 =
                  g e (ITSET g (s DELETE e) 1)` THEN1 SRW_TAC [][Abbr`g`] THEN
  MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
  SRW_TAC [ARITH_ss][Abbr`g`]);

val _ = overload_on ("PI", ``PROD_IMAGE``)
val _ = Unicode.unicode_version {tmnm = "PROD_IMAGE", u = UnicodeChars.Pi}

(*---------------------------------------------------------------------------*)
(* PROD_SET multiplies the elements of a set of natural numbers              *)
(*---------------------------------------------------------------------------*)

(* Define PROD_SET similar to SUM_SET *)
(* val PROD_SET_DEF = new_definition("PROD_SET_DEF", ``PROD_SET = PROD_IMAGE I``); *)
val PROD_SET_DEF = new_definition("PROD_SET_DEF", ``PROD_SET = PROD_IMAGE I``);

(* Theorem: Product Set property *)
val PROD_SET_THM = store_thm(
  "PROD_SET_THM",
  ``(PROD_SET {} = 1) /\
    (!x s. FINITE s ==> (PROD_SET (x INSERT s) = x * PROD_SET (s DELETE x)))``,
  SRW_TAC [][PROD_SET_DEF, PROD_IMAGE_THM]);

val PROD_SET_EMPTY = save_thm("PROD_SET_EMPTY", CONJUNCT1 PROD_SET_THM);

(* Theorem: PROD_SET (IMAGE f (x INSERT s)) = (f x) * PROD_SET (IMAGE f s) *)
(* Proof:
     PROD_SET (IMAGE f (x INSERT s))
   = PROD_SET (f x INSERT IMAGE f s)          by IMAGE_INSERT
   = f x * PROD_SET (IMAGE f s) DELETE (f x)  by PROD_SET_THM, assume FINITE (IMAGE f s)
   = f x * PROD_SET (IMAGE f s)               by (f x) not in (IMAGE f s)
*)
val PROD_SET_IMAGE_REDUCTION = store_thm(
  "PROD_SET_IMAGE_REDUCTION",
  ``!f s x. FINITE (IMAGE f s) /\ f x NOTIN IMAGE f s ==>
     (PROD_SET (IMAGE f (x INSERT s)) = (f x) * PROD_SET (IMAGE f s))``,
  METIS_TAC [DELETE_NON_ELEMENT, IMAGE_INSERT, PROD_SET_THM]);


(* every finite, non-empty set of natural numbers has a maximum element *)

val max_lemma = prove(
  ``!s. FINITE s ==> ~(s = {}) ==> ?x. x IN s /\ !y. y IN s ==> y <= x``,
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss [NOT_INSERT_EMPTY, IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  Q.ISPEC_THEN `s` STRIP_ASSUME_TAC SET_CASES THENL [
    ASM_SIMP_TAC arith_ss [NOT_IN_EMPTY],
    `~(s = {})` by PROVE_TAC [NOT_INSERT_EMPTY] THEN
    `?m. m IN s /\ !y. y IN s ==> y <= m` by PROVE_TAC [] THEN
    Cases_on `e <= m` THENL [
      PROVE_TAC [],
      `m <= e` by RW_TAC arith_ss [] THEN
      PROVE_TAC [LESS_EQ_REFL, LESS_EQ_TRANS]
    ]
  ])

val MAX_SET_DEF = new_specification (
  "MAX_SET_DEF", ["MAX_SET"],
  SIMP_RULE bool_ss [AND_IMP_INTRO, GSYM RIGHT_EXISTS_IMP_THM,
                     SKOLEM_THM] max_lemma);

val MAX_SET_THM = store_thm(
  "MAX_SET_THM",
  ``(!e. MAX_SET {e} = e) /\
    (!s. FINITE s ==> !e1 e2. MAX_SET (e1 INSERT e2 INSERT s) =
                              MAX e1 (MAX_SET (e2 INSERT s)))``,
  CONJ_TAC THENL [
    GEN_TAC THEN
    STRIP_ASSUME_TAC (SIMP_RULE bool_ss [FINITE_SING, NOT_INSERT_EMPTY,
                                         IN_SING]
                                (Q.SPEC `{e}` MAX_SET_DEF)),
    REPEAT STRIP_TAC THEN
    Q.ISPEC_THEN `e1 INSERT e2 INSERT s` MP_TAC MAX_SET_DEF THEN
    ASM_SIMP_TAC bool_ss [FINITE_INSERT, NOT_INSERT_EMPTY,
                          IN_INSERT, FORALL_AND_THM, DISJ_IMP_THM] THEN
    STRIP_TAC THEN
    Q.ISPEC_THEN `e2 INSERT s` MP_TAC MAX_SET_DEF THEN
    ASM_SIMP_TAC bool_ss [FINITE_INSERT, NOT_INSERT_EMPTY,
                          IN_INSERT, FORALL_AND_THM, DISJ_IMP_THM] THEN
    STRIP_TAC THEN
    Q.ABBREV_TAC `m1 = MAX_SET (e1 INSERT e2 INSERT s)` THEN
    Q.ABBREV_TAC `m2 = MAX_SET (e2 INSERT s)` THEN
    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN RES_TAC THEN
    ASM_SIMP_TAC arith_ss [MAX_DEF]
  ]);

val MAX_SET_ELIM = store_thm(
  "MAX_SET_ELIM",
  ``!P Q. FINITE P /\ ~(P = {}) /\ (!x. (!y. y IN P ==> y <= x) /\ x IN P ==> Q x) ==>
          Q (MAX_SET P)``,
  PROVE_TAC [MAX_SET_DEF]);

val MIN_SET_DEF = new_definition("MIN_SET_DEF", ``MIN_SET = $LEAST``);

val MIN_SET_ELIM = store_thm(
  "MIN_SET_ELIM",
  ``!P Q. ~(P = {}) /\ (!x. (!y. y IN P ==> x <= y) /\ x IN P ==> Q x) ==>
          Q (MIN_SET P)``,
  REWRITE_TAC [MIN_SET_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEAST_ELIM THEN CONJ_TAC THENL [
    `?x. P x` by PROVE_TAC [SET_CASES, IN_INSERT, SPECIFICATION] THEN
    PROVE_TAC [],
    FULL_SIMP_TAC arith_ss [SPECIFICATION] THEN
    PROVE_TAC [NOT_LESS]
  ]);

val MIN_SET_THM = store_thm(
  "MIN_SET_THM",
  ``(!e. MIN_SET {e} = e) /\
    (!s e1 e2. MIN_SET (e1 INSERT e2 INSERT s) =
               MIN e1 (MIN_SET (e2 INSERT s)))``,
  CONJ_TAC THENL [
    GEN_TAC THEN
    Q.SPECL_THEN [`{e}`, `\x. x = e`] (MATCH_MP_TAC o BETA_RULE)
                 MIN_SET_ELIM THEN
    SIMP_TAC bool_ss [IN_INSERT, NOT_INSERT_EMPTY, DISJ_IMP_THM,
                      NOT_IN_EMPTY],
    REPEAT GEN_TAC THEN
    Q.SPECL_THEN [`e1 INSERT e2 INSERT s`,
                   `\x. x = MIN e1 (MIN_SET (e2 INSERT s))`]
                 (MATCH_MP_TAC o BETA_RULE)
                 MIN_SET_ELIM THEN
    SIMP_TAC bool_ss [IN_INSERT, NOT_INSERT_EMPTY, DISJ_IMP_THM,
                      FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN
    Q.SPECL_THEN [`e2 INSERT s`, `\y. x = MIN e1 y`]
                 (MATCH_MP_TAC o BETA_RULE)
                 MIN_SET_ELIM THEN
    SIMP_TAC bool_ss [IN_INSERT, NOT_INSERT_EMPTY, DISJ_IMP_THM,
                      FORALL_AND_THM] THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_SIMP_TAC arith_ss [MIN_DEF]
  ]);

val MIN_SET_LEM = Q.store_thm
("MIN_SET_LEM",
 `!s. ~(s={}) ==> (MIN_SET s IN s) /\ !x. x IN s ==> MIN_SET s <= x`,
  METIS_TAC [GSYM MEMBER_NOT_EMPTY,MIN_SET_DEF,
             IN_DEF,whileTheory.FULL_LEAST_INTRO]);

val SUBSET_MIN_SET = Q.store_thm
("SUBSET_MIN_SET",
 `!I J n. ~(I={}) /\ ~(J={}) /\ I SUBSET J ==> MIN_SET J <= MIN_SET I`,
  METIS_TAC [SUBSET_DEF,MIN_SET_LEM]);

val SUBSET_MAX_SET = Q.store_thm
("SUBSET_MAX_SET",
 `!I J n. FINITE I /\ FINITE J /\
          ~(I={}) /\ ~(J={}) /\ I SUBSET J ==> MAX_SET I <= MAX_SET J`,
 METIS_TAC [SUBSET_DEF,MAX_SET_DEF]);

val MIN_SET_LEQ_MAX_SET = Q.store_thm
("MIN_SET_LEQ_MAX_SET",
 `!s. ~(s={}) /\ FINITE s ==> MIN_SET s <= MAX_SET s`,
 RW_TAC arith_ss [MIN_SET_DEF] THEN
METIS_TAC [FULL_LEAST_INTRO,MAX_SET_DEF,IN_DEF]);

val MIN_SET_UNION = Q.store_thm
("MIN_SET_UNION",
 `!A B. FINITE A /\ FINITE B /\ ~(A={}) /\ ~(B={})
         ==>
      (MIN_SET (A UNION B) = MIN (MIN_SET A) (MIN_SET B))`,
 let val lem = Q.prove
 (`!A. FINITE A ==>
   !B. FINITE B /\ ~(A={}) /\ ~(B={})
       ==> (MIN_SET (A UNION B) = MIN (MIN_SET A) (MIN_SET B))`,
  SET_INDUCT_TAC THEN RW_TAC (srw_ss()) []
   THEN `?b t. (B = b INSERT t) /\ ~(b IN t)` by METIS_TAC [SET_CASES]
   THEN RW_TAC (srw_ss()) []
   THEN `(e INSERT s) UNION (b INSERT t) = e INSERT b INSERT (s UNION t)`
        by METIS_TAC [INSERT_UNION,INSERT_UNION_EQ, UNION_COMM, UNION_ASSOC]
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN `FINITE (s UNION t)` by METIS_TAC [FINITE_INSERT,FINITE_UNION]
   THEN RW_TAC (srw_ss()) [MIN_SET_THM]
   THEN Cases_on `s={}` THEN RW_TAC (srw_ss()) [MIN_SET_THM]
   THEN `b INSERT (s UNION t) = s UNION (b INSERT t)`
        by METIS_TAC [INSERT_UNION,INSERT_UNION_EQ, UNION_COMM, UNION_ASSOC]
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN `MIN_SET (s UNION (b INSERT t)) = MIN (MIN_SET s) (MIN_SET (b INSERT t))`
        by METIS_TAC [] THEN POP_ASSUM SUBST_ALL_TAC
   THEN `MIN_SET (e INSERT s) = MIN (MIN_SET s) (MIN_SET {e})`
        by METIS_TAC [FINITE_SING,NOT_EMPTY_INSERT,
                      UNION_COMM,INSERT_UNION_EQ,UNION_EMPTY]
   THEN RW_TAC (srw_ss()) [MIN_SET_THM, AC MIN_COMM MIN_ASSOC])
 in METIS_TAC [lem]
 end);;

val MAX_SET_UNION = Q.store_thm
("MAX_SET_UNION",
 `!A B. FINITE A /\ FINITE B /\ ~(A={}) /\ ~(B={})
         ==>
      (MAX_SET (A UNION B) = MAX (MAX_SET A) (MAX_SET B))`,
 let val lem = Q.prove
 (`!A. FINITE A ==>
   !B. FINITE B /\ ~(A={}) /\ ~(B={})
       ==> (MAX_SET (A UNION B) = MAX (MAX_SET A) (MAX_SET B))`,
  SET_INDUCT_TAC THEN RW_TAC (srw_ss()) []
   THEN `?b t. (B = b INSERT t) /\ ~(b IN t)` by METIS_TAC [SET_CASES]
   THEN RW_TAC (srw_ss()) []
   THEN `(e INSERT s) UNION (b INSERT t) = e INSERT b INSERT (s UNION t)`
        by METIS_TAC [INSERT_UNION,INSERT_UNION_EQ, UNION_COMM, UNION_ASSOC]
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN `FINITE (s UNION t)` by METIS_TAC [FINITE_INSERT,FINITE_UNION]
   THEN RW_TAC (srw_ss()) [MAX_SET_THM]
   THEN Cases_on `s={}` THEN RW_TAC (srw_ss()) [MAX_SET_THM]
   THEN `b INSERT (s UNION t) = s UNION (b INSERT t)`
        by METIS_TAC [INSERT_UNION,INSERT_UNION_EQ, UNION_COMM, UNION_ASSOC]
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN `MAX_SET (s UNION (b INSERT t)) = MAX (MAX_SET s) (MAX_SET (b INSERT t))`
        by METIS_TAC [] THEN POP_ASSUM SUBST_ALL_TAC
   THEN `MAX_SET (e INSERT s) = MAX (MAX_SET s) (MAX_SET {e})`
        by METIS_TAC [FINITE_SING,NOT_EMPTY_INSERT,
                      UNION_COMM,INSERT_UNION_EQ,UNION_EMPTY]
   THEN RW_TAC (srw_ss()) [MAX_SET_THM, AC MAX_COMM MAX_ASSOC])
 in METIS_TAC [lem]
 end);;

val set_ss = arith_ss ++ SET_SPEC_ss ++
             rewrites [CARD_INSERT,CARD_EMPTY,FINITE_EMPTY,FINITE_INSERT,
                       NOT_IN_EMPTY];

(*---------------------------------------------------------------------------*)
(* POW s is the powerset of s                                                *)
(*---------------------------------------------------------------------------*)

val POW_DEF =
 new_definition
  ("POW_DEF",
   ``POW set = {s | s SUBSET set}``);

val IN_POW = Q.store_thm
("IN_POW",
 `!set e. e IN POW set = e SUBSET set`,
 RW_TAC bool_ss [POW_DEF,GSPECIFICATION]);

val UNIV_FUN_TO_BOOL = store_thm(
  "UNIV_FUN_TO_BOOL",
  ``univ(:'a -> bool) = POW univ(:'a)``,
  SIMP_TAC (srw_ss()) [EXTENSION, IN_POW]);

val SUBSET_POW = Q.store_thm
("SUBSET_POW",
 `!s1 s2. s1 SUBSET s2 ==> (POW s1) SUBSET (POW s2)`,
 RW_TAC set_ss [POW_DEF,SUBSET_DEF]);

val SUBSET_INSERT_RIGHT = Q.store_thm
("SUBSET_INSERT_RIGHT",
 `!e s1 s2. s1 SUBSET s2 ==> s1 SUBSET (e INSERT s2)`,
 RW_TAC set_ss [SUBSET_DEF,IN_INSERT]);

val SUBSET_DELETE_BOTH = Q.store_thm
("SUBSET_DELETE_BOTH",
 `!s1 s2 x. s1 SUBSET s2 ==> (s1 DELETE x) SUBSET (s2 DELETE x)`,
 RW_TAC set_ss [SUBSET_DEF,SUBSET_DELETE,IN_DELETE]);

(*---------------------------------------------------------------------------*)
(* Recursion equations for POW                                               *)
(*---------------------------------------------------------------------------*)

val POW_INSERT = Q.store_thm
("POW_INSERT",
 `!e s. POW (e INSERT s) = IMAGE ($INSERT e) (POW s) UNION (POW s)`,
 RW_TAC set_ss [EXTENSION,IN_UNION,IN_POW] THEN
 Cases_on `e IN x` THENL
 [EQ_TAC THEN RW_TAC set_ss [] THENL
  [DISJ1_TAC
    THEN RW_TAC set_ss [IN_IMAGE,IN_POW]
    THEN Q.EXISTS_TAC `x DELETE e`
    THEN RW_TAC set_ss [INSERT_DELETE]
    THEN IMP_RES_TAC SUBSET_DELETE_BOTH
    THEN POP_ASSUM (MP_TAC o Q.SPEC `e`)
    THEN RW_TAC set_ss [DELETE_INSERT]
    THEN METIS_TAC [DELETE_SUBSET,SUBSET_TRANS],
   FULL_SIMP_TAC set_ss
     [IN_IMAGE,IN_POW,SUBSET_INSERT_RIGHT,INSERT_SUBSET,IN_INSERT],
   FULL_SIMP_TAC set_ss [SUBSET_DEF]
    THEN METIS_TAC [IN_INSERT]],
  RW_TAC set_ss [SUBSET_INSERT]
    THEN EQ_TAC THEN RW_TAC set_ss [IN_IMAGE]
    THEN METIS_TAC [IN_INSERT]]);

val POW_EQNS = Q.store_thm
("POW_EQNS",
 `(POW {} = {{}} : 'a set set) /\
  (!e:'a.
   !s. POW (e INSERT s) = let ps = POW s
                            in (IMAGE ($INSERT e) ps) UNION ps)`,
 CONJ_TAC THENL
 [RW_TAC set_ss [POW_DEF,SUBSET_EMPTY,EXTENSION,NOT_IN_EMPTY,IN_INSERT],
  METIS_TAC [POW_INSERT,LET_THM]]);

val FINITE_POW = Q.store_thm
("FINITE_POW",
 `!s. FINITE s ==> FINITE (POW s)`,
 HO_MATCH_MP_TAC FINITE_INDUCT
  THEN CONJ_TAC THENL
  [METIS_TAC [POW_EQNS,FINITE_EMPTY,FINITE_INSERT],
   RW_TAC set_ss [POW_EQNS,LET_THM,FINITE_UNION,IMAGE_FINITE]]);

val lem = Q.prove
(`!n. 2 * 2**n = 2**n + 2**n`,
 RW_TAC arith_ss [EXP]);

(*---------------------------------------------------------------------------*)
(* Cardinality of the power set of a finite set                              *)
(*---------------------------------------------------------------------------*)

val CARD_POW = Q.store_thm
("CARD_POW",
 `!s. FINITE s ==> (CARD (POW s) = 2 EXP (CARD s))`,
 SET_INDUCT_TAC
  THEN RW_TAC set_ss [POW_EQNS,LET_THM,EXP]
  THEN `FINITE (POW s) /\
        FINITE (IMAGE ($INSERT e) (POW s))`
    by METIS_TAC[FINITE_POW,IMAGE_FINITE]
  THEN `CARD (IMAGE ($INSERT e) (POW s) UNION POW s) =
        CARD (IMAGE ($INSERT e) (POW s)) + CARD(POW s)`
    by
   (`CARD ((IMAGE ($INSERT e) (POW s)) INTER (POW s)) = 0`
      by (RW_TAC set_ss [CARD_EQ_0,INTER_FINITE] THEN
          RW_TAC set_ss [EXTENSION,IN_INTER,IN_POW,IN_IMAGE] THEN
          RW_TAC set_ss [SUBSET_DEF,IN_INSERT] THEN METIS_TAC[])
     THEN METIS_TAC [CARD_UNION,ADD_CLAUSES])
  THEN POP_ASSUM SUBST_ALL_TAC
  THEN Q.PAT_ASSUM `X = 2 ** (CARD s)` (ASSUME_TAC o SYM)
  THEN ASM_REWRITE_TAC [lem, EQ_ADD_RCANCEL]
  THEN `BIJ ($INSERT e) (POW s) (IMAGE ($INSERT e) (POW s))`
    by (RW_TAC set_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_IMAGE,IN_POW]
        THENL
         [METIS_TAC [IN_POW],
          `~(e IN x) /\ ~(e IN y)` by METIS_TAC [SUBSET_DEF]
            THEN FULL_SIMP_TAC set_ss [EXTENSION, IN_INSERT]
            THEN METIS_TAC[],
          METIS_TAC [IN_POW],METIS_TAC[]])
  THEN METIS_TAC [FINITE_BIJ_CARD_EQ]);


(* ----------------------------------------------------------------------
    Simple lemmas about GSPECIFICATIONs
   ---------------------------------------------------------------------- *)

val sspec_tac = CONV_TAC (DEPTH_CONV SET_SPEC_CONV)

val GSPEC_ETA = store_thm(
  "GSPEC_ETA",
  ``{x | P x} = P``,
  SRW_TAC [] [EXTENSION, SPECIFICATION]);

val GSPEC_F = store_thm(
  "GSPEC_F",
  ``{ x | F} = {}``,
  SRW_TAC [][EXTENSION] THEN sspec_tac THEN REWRITE_TAC []);

val GSPEC_T = store_thm(
  "GSPEC_T",
  ``{x | T} = UNIV``,
  SRW_TAC [][EXTENSION, IN_UNIV] THEN sspec_tac);

val GSPEC_ID = store_thm(
  "GSPEC_ID",
  ``{x | x IN y} = y``,
  SRW_TAC [][EXTENSION] THEN sspec_tac THEN REWRITE_TAC []);

val GSPEC_EQ = store_thm(
  "GSPEC_EQ",
  ``{ x | x = y} = {y}``,
  SRW_TAC [][EXTENSION] THEN sspec_tac THEN REWRITE_TAC []);

val GSPEC_EQ2 = store_thm(
  "GSPEC_EQ2",
  ``{ x | y = x} = {y}``,
  SRW_TAC [][EXTENSION] THEN sspec_tac THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC []);

val _ = export_rewrites ["GSPEC_F", "GSPEC_T", "GSPEC_ID", "GSPEC_EQ",
                         "GSPEC_EQ2"]

(* Following rewrites are useful, but probably not suitable for
   automatic application.  Sadly even those above fail in the presence
   of more complicated GSPEC expressions, such as { (x,y) | F }.

   We could cope with that particular example using the conditional
   rewrite below, but again, this is probably not suitable for
   automatic inclusion in rewrite sets *)

val GSPEC_F_COND = store_thm(
  "GSPEC_F_COND",
  ``!f. (!x. ~SND (f x)) ==> (GSPEC f = {})``,
  SRW_TAC [][EXTENSION, GSPECIFICATION] THEN
  POP_ASSUM (Q.SPEC_THEN `x'` MP_TAC) THEN
  Cases_on `f x'` THEN SRW_TAC [][]);

val GSPEC_AND = store_thm(
  "GSPEC_AND",
  ``!P Q. {x | P x /\ Q x} = {x | P x} INTER {x | Q x}``,
  SRW_TAC [][EXTENSION] THEN sspec_tac THEN REWRITE_TAC []);

val GSPEC_OR = store_thm(
  "GSPEC_OR",
  ``!P Q. {x | P x \/ Q x} = {x | P x} UNION {x | Q x}``,
  SRW_TAC [][EXTENSION, IN_UNION] THEN sspec_tac THEN REWRITE_TAC []);

(* ----------------------------------------------------------------------
    partition a set according to an equivalence relation (or at least
    a relation that is reflexive, symmetric and transitive over that set)
   ---------------------------------------------------------------------- *)

val equiv_on_def = new_definition(
  "equiv_on_def",
  ``(equiv_on) R s =
       (!x. x IN s ==> R x x) /\
       (!x y. x IN s /\ y IN s ==> (R x y = R y x)) /\
       (!x y z. x IN s /\ y IN s /\ z IN s /\ R x y /\ R y z ==> R x z)``);
val _ = set_fixity "equiv_on" (Infix(NONASSOC, 425))

val partition_def = new_definition(
  "partition_def",
  ``partition R s =
      { t | ?x. x IN s /\ (t = { y | y IN s /\ R x y})}``);

val BIGUNION_partition = store_thm(
  "BIGUNION_partition",
  ``R equiv_on s ==> (BIGUNION (partition R s) = s)``,
  STRIP_TAC THEN
  SRW_TAC [][EXTENSION, IN_BIGUNION, partition_def] THEN
  EQ_TAC THEN STRIP_TAC THENL[
    METIS_TAC [equiv_on_def],
    Q.EXISTS_TAC `{ y | R x y /\ y IN s}` THEN
    `R x x` by METIS_TAC [equiv_on_def] THEN SRW_TAC [][] THEN
    METIS_TAC []
  ]);

val EMPTY_NOT_IN_partition = store_thm(
  "EMPTY_NOT_IN_partition",
  ``R equiv_on s ==> ~({} IN partition R s)``,
  SRW_TAC [][partition_def, EXTENSION] THEN
  METIS_TAC [equiv_on_def]);

(* Invocation(s) of PROVE_TAC are slow, but METIS seems to be
   possibly slower
*)
val partition_elements_disjoint = store_thm(
  "partition_elements_disjoint",
  ``R equiv_on s ==>
    !t1 t2. t1 IN partition R s /\ t2 IN partition R s /\ ~(t1 = t2) ==>
            DISJOINT t1 t2``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [partition_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2
              (Q.X_CHOOSE_THEN `a` MP_TAC)
              (CONJUNCTS_THEN2
               (Q.X_CHOOSE_THEN `b` MP_TAC) MP_TAC)) THEN
  MAP_EVERY Q.ID_SPEC_TAC [`t1`, `t2`] THEN SIMP_TAC (srw_ss()) [] THEN
  SRW_TAC [][DISJOINT_DEF] THEN
  SIMP_TAC (srw_ss()) [EXTENSION] THEN
  Q.X_GEN_TAC `c` THEN Cases_on `c IN s` THEN SRW_TAC [][] THEN
  Cases_on `R a c` THEN SRW_TAC [][] THEN
  STRIP_TAC THEN
  `R a b` by PROVE_TAC [equiv_on_def] THEN
  Q.PAT_ASSUM `~(a = b)` MP_TAC THEN SRW_TAC [][] THEN
  SRW_TAC [][EXTENSION] THEN PROVE_TAC [equiv_on_def]);

val partition_elements_interrelate = store_thm(
  "partition_elements_interrelate",
  ``R equiv_on s ==> !t. t IN partition R s ==>
                         !x y. x IN t /\ y IN t ==> R x y``,
  SIMP_TAC (srw_ss()) [partition_def, GSYM LEFT_FORALL_IMP_THM] THEN
  PROVE_TAC [equiv_on_def]);

val partition_SUBSET = Q.store_thm
("partition_SUBSET",
 `!R s t. t IN partition R s ==> t SUBSET s`,
  SRW_TAC [][partition_def, EXTENSION, EQ_IMP_THM] THEN
  METIS_TAC [SUBSET_DEF]);

val FINITE_partition = Q.store_thm (
  "FINITE_partition",
  `!R s. FINITE s ==>
         FINITE (partition R s) /\
         !t. t IN partition R s ==> FINITE t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  `!t. t IN partition R s ==> t SUBSET s` by METIS_TAC [partition_SUBSET] THEN
  `!t. t IN partition R s ==> t IN POW s` by SRW_TAC [][POW_DEF] THEN
  METIS_TAC [FINITE_POW, SUBSET_FINITE, SUBSET_DEF]);

val partition_CARD = Q.store_thm
("partition_CARD",
 `!R s. R equiv_on s /\ FINITE s
          ==>
        (CARD s = SUM_IMAGE CARD (partition R s))`,
METIS_TAC [FINITE_partition, BIGUNION_partition, DISJ_BIGUNION_CARD,
           partition_elements_disjoint, FINITE_BIGUNION, partition_def]);

(* ----------------------------------------------------------------------
    Assert a predicate on all pairs of elements in a set.
    Take the RC of the P argument to consider only pairs of distinct elements.
   ---------------------------------------------------------------------- *)

val pairwise_def = new_definition(
  "pairwise_def",
  ``pairwise P s = !e1 e2. e1 IN s /\ e2 IN s ==> P e1 e2``);

val pairwise_UNION = Q.store_thm(
"pairwise_UNION",
`pairwise R (s1 UNION s2) <=>
 pairwise R s1 /\ pairwise R s2 /\ (!x y. x IN s1 /\ y IN s2 ==> R x y /\ R y x)`,
SRW_TAC [boolSimps.DNF_ss][pairwise_def] THEN METIS_TAC []);

val pairwise_SUBSET = Q.store_thm(
"pairwise_SUBSET",
`!R s t. pairwise R t /\ s SUBSET t ==> pairwise R s`,
SRW_TAC [][SUBSET_DEF,pairwise_def]);


(* ----------------------------------------------------------------------
    A proof of Koenig's Lemma
   ---------------------------------------------------------------------- *)

(* a counting exercise for R-trees.  If x0 has finitely many successors, and
   each of these successors has finite trees underneath, then x0's tree is
   also finite *)
val KL_lemma1 = prove(
  ``FINITE { x | R x0 x} /\
    (!y. R x0 y ==> FINITE { x | RTC R y x }) ==>
    FINITE { x | RTC R x0 x}``,
  REPEAT STRIP_TAC THEN
  `{ x | RTC R x0 x} =
   x0 INSERT BIGUNION (IMAGE (\x. {y | RTC R x y}) {x | R x0 x})`
      by (REWRITE_TAC [EXTENSION] THEN
          SRW_TAC [][GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION, IN_IMAGE,
                     GSPECIFICATION] THEN
          PROVE_TAC [relationTheory.RTC_CASES1]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][IN_IMAGE] THENL [
    SRW_TAC [][IMAGE_FINITE, IN_IMAGE, GSPECIFICATION],
    RES_TAC
  ]);


(*---------------------------------------------------------------------------*)
(* Effectively taking the contrapositive of the above, saying that if R is   *)
(* finitely branching, and we're on top of an infinite R tree, then one of   *)
(* the immediate children is on top of an infinite R tree                    *)
(*---------------------------------------------------------------------------*)

val KL_lemma2 = prove(
  ``(!x. FINITE {y | R x y}) ==>
    !y. ~ FINITE {x | RTC R y x} ==> ?z. R y z /\ ~FINITE { x | RTC R z x}``,
  METIS_TAC [KL_lemma1]);

(*---------------------------------------------------------------------------*)
(* Now throw in the unavoidable use of the axiom of choice, and say that     *)
(* there's a function to do this for us.                                     *)
(*---------------------------------------------------------------------------*)

val KL_lemma3 =
    CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC
               ONCE_DEPTH_CONV SKOLEM_CONV) KL_lemma2

val KoenigsLemma = store_thm(
  "KoenigsLemma",
  ``!R. (!x. FINITE {y | R x y}) ==>
        !x. ~FINITE {y | RTC R x y} ==>
            ?f. (f 0 = x) /\ !n. R (f n) (f (SUC n))``,
  REPEAT STRIP_TAC THEN
  `?g. !y. ~FINITE { x | RTC R y x} ==>
           R y (g y) /\ ~FINITE {x | RTC R (g y) x}`
     by METIS_TAC [KL_lemma3] THEN
  Q.SPECL_THEN [`x`, `\n r. g r`]
               (Q.X_CHOOSE_THEN `f` STRIP_ASSUME_TAC o BETA_RULE)
               (TypeBase.axiom_of ``:num``) THEN
  Q.EXISTS_TAC `f` THEN ASM_REWRITE_TAC [] THEN
  Q_TAC SUFF_TAC
        `!n. R (f n) (g (f n)) /\ ~FINITE { x | RTC R (f n) x}` THEN1
        METIS_TAC [] THEN
  Induct THEN METIS_TAC []);

val KoenigsLemma_WF = store_thm(
  "KoenigsLemma_WF",
  ``!R. (!x. FINITE {y | R x y}) /\ WF (inv R) ==> !x. FINITE {y | RTC R x y}``,
  SRW_TAC [][prim_recTheory.WF_IFF_WELLFOUNDED,
             prim_recTheory.wellfounded_def,
             relationTheory.inv_DEF] THEN
  METIS_TAC [KoenigsLemma]);


val SET_EQ_SUBSET = Q.store_thm
("SET_EQ_SUBSET",
 `!s1 s2. (s1 = s2) = s1 SUBSET s2 /\ s2 SUBSET s1`,
 REPEAT (GEN_TAC ORELSE EQ_TAC)
  THEN RW_TAC set_ss [SUBSET_DEF,SUBSET_ANTISYM]);

val PSUBSET_EQN = Q.store_thm
("PSUBSET_EQN",
 `!s1 s2. s1 PSUBSET s2 = s1 SUBSET s2 /\ ~(s2 SUBSET s1)`,
 PROVE_TAC [PSUBSET_DEF,SET_EQ_SUBSET]);

val PSUBSET_SUBSET_TRANS = Q.store_thm
("PSUBSET_SUBSET_TRANS",
 `!s t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
 PROVE_TAC [SUBSET_DEF,PSUBSET_EQN]);

val SUBSET_PSUBSET_TRANS = Q.store_thm
("SUBSET_PSUBSET_TRANS",
 `!s t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
 PROVE_TAC [SUBSET_DEF,PSUBSET_EQN]);

val CROSS_EQNS = Q.store_thm
("CROSS_EQNS",
 `!(s1:'a set) (s2:'b set).
  (({}:'a set)   CROSS s2 = ({}:('a#'b) set)) /\
  ((a INSERT s1) CROSS s2 = (IMAGE (\y.(a,y)) s2) UNION (s1 CROSS s2))`,
RW_TAC set_ss [CROSS_EMPTY,Once CROSS_INSERT_LEFT]
  THEN MATCH_MP_TAC (PROVE [] (Term`(a=b) ==> (f a c = f b c)`))
  THEN RW_TAC set_ss [CROSS_DEF,IMAGE_DEF,EXTENSION]
  THEN METIS_TAC [ABS_PAIR_THM,IN_SING,FST,SND]);

val count_EQN = Q.store_thm
("count_EQN",
 `!n. count n = if n = 0 then {} else
            let p = PRE n in p INSERT (count p)`,
 REWRITE_TAC [count_def]
  THEN Induct
  THEN RW_TAC arith_ss [GSPEC_F]
  THEN RW_TAC set_ss [EXTENSION,IN_SING,IN_INSERT]);

(* Theorems about countability added by Scott Owens on 2009-03-20, plus a few
* misc. theorems *)

fun FSTAC thms = FULL_SIMP_TAC (srw_ss()) thms;
fun RWTAC thms = SRW_TAC [] thms;

val UNIQUE_MEMBER_SING = Q.store_thm ("UNIQUE_MEMBER_SING",
`!x s. x IN s /\ (!y. y IN s ==> (x = y)) = (s = {x})`,
SRW_TAC [] [EXTENSION] THEN
METIS_TAC []);

val inj_surj = Q.store_thm ("inj_surj",
`!f s t. INJ f s t ==> (s = {}) \/ ?f'. SURJ f' t s`,
RWTAC [INJ_DEF, SURJ_DEF, METIS_PROVE [] ``!a b. a \/ b = ~a ==> b``] THEN
`!x. ?y. y IN s /\ (x IN IMAGE f s ==> (f y = x))`
          by (RWTAC [] THEN
              Cases_on `x IN IMAGE f s` THEN
              FSTAC [IMAGE_DEF] THEN1
              METIS_TAC [] THEN
              Q.EXISTS_TAC `CHOICE s` THEN
              RWTAC [CHOICE_DEF] THEN
              METIS_TAC []) THEN
     FSTAC [SKOLEM_THM, IN_IMAGE] THEN
     METIS_TAC []);

val infinite_rest = Q.store_thm ("infinite_rest",
`!s. INFINITE s ==> INFINITE (REST s)`,
RWTAC [] THEN
CCONTR_TAC THEN
FSTAC [INFINITE_DEF, REST_DEF]);

val chooser_def = TotalDefn.Define `
  (chooser s 0 = CHOICE s) /\
  (chooser s (SUC n) = chooser (REST s) n)`;

val chooser_lem1 = Q.prove (
`!n s t. INFINITE s /\ s SUBSET t ==> chooser s n IN t`,
Induct THEN
RWTAC [chooser_def, SUBSET_DEF] THENL [
  `s <> {}` by (RWTAC [EXTENSION] THEN METIS_TAC [INFINITE_INHAB]) THEN
  METIS_TAC [CHOICE_DEF],
  `REST s SUBSET s` by RWTAC [REST_SUBSET] THEN
  METIS_TAC [infinite_rest]
]);

val chooser_lem2 = Q.prove (
`!n s. INFINITE s ==> chooser (REST s) n <> CHOICE s`,
RWTAC [] THEN
IMP_RES_TAC infinite_rest THEN
`chooser (REST s) n IN (REST s)`
        by METIS_TAC [chooser_lem1, SUBSET_REFL] THEN
FSTAC [REST_DEF, IN_DELETE]);

val chooser_lem3 = Q.prove (
`!x y s. INFINITE s /\ (chooser s x = chooser s y) ==> (x = y)`,
Induct_on `x` THEN
RWTAC [chooser_def] THEN
Cases_on `y` THEN
FSTAC [chooser_def] THEN
RWTAC [] THEN
METIS_TAC [chooser_lem2, infinite_rest]);

val infinite_num_inj_lem = Q.prove (
`!s. FINITE s ==> ~?f. INJ f (UNIV:num set) s`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
RWTAC [] THEN
FSTAC [INJ_DEF] THEN
CCONTR_TAC THEN
FSTAC [IN_UNIV] THEN
Q.PAT_ASSUM `!f. (?x. f x NOTIN s) \/ P f` MP_TAC THEN
RWTAC [] THEN
Cases_on `?y. f y = e` THEN
FSTAC [] THEN
RWTAC [] THENL [
  Q.EXISTS_TAC `\x. if x < y then f x else f (SUC x)` THEN
  RWTAC [] THEN
  FSTAC [METIS_PROVE [] ``! a b. a \/ b = ~a==>b``] THEN
  RWTAC [] THENL [
    `x <> y` by DECIDE_TAC THEN METIS_TAC [],
    `SUC x <> y` by DECIDE_TAC THEN METIS_TAC [],
    `x = SUC y'` by METIS_TAC [] THEN DECIDE_TAC,
    `SUC x = y'` by METIS_TAC [] THEN DECIDE_TAC,
    `SUC x = SUC y'` by METIS_TAC [] THEN DECIDE_TAC
  ],
  METIS_TAC []
]);

val infinite_num_inj = Q.store_thm ("infinite_num_inj",
`!s. INFINITE s = ?f. INJ f (UNIV:num set) s`,
RWTAC [] THEN
EQ_TAC THEN
RWTAC [] THENL
[Q.EXISTS_TAC `chooser s` THEN
     RWTAC [INJ_DEF] THEN
     METIS_TAC [chooser_lem1, chooser_lem3, SUBSET_REFL],
 METIS_TAC [infinite_num_inj_lem, INFINITE_DEF]]);

val countable_def = TotalDefn.Define `
  countable s = ?f. INJ f s (UNIV:num set)`;

val countable_image_nats = store_thm( "countable_image_nats",
  ``countable (IMAGE f univ(:num))``, SIMP_TAC
  (srw_ss())[countable_def] THEN METIS_TAC[SURJ_IMAGE, SURJ_INJ_INV]);
  val _ = export_rewrites ["countable_image_nats"]

val countable_surj = Q.store_thm ("countable_surj",
`!s. countable s = (s = {}) \/ ?f. SURJ f (UNIV:num set) s`,
RWTAC [countable_def] THEN
EQ_TAC THEN
RWTAC [] THENL
[METIS_TAC [inj_surj],
 RWTAC [INJ_DEF],
 Cases_on `s = {}` THEN
     FSTAC [INJ_DEF, SURJ_DEF] THEN
     METIS_TAC []]);

val num_countable = Q.store_thm ("num_countable",
`countable (UNIV:num set)`,
RWTAC [countable_def, INJ_DEF] THEN
Q.EXISTS_TAC `\x.x` THEN
RWTAC []);

val INJ_SUBSET = Q.prove (
`!f s t s'. INJ f s t /\ s' SUBSET s ==> INJ f s' t`,
RWTAC [INJ_DEF, SUBSET_DEF]);

val subset_countable = Q.store_thm ("subset_countable",
`!s t. countable s /\ t SUBSET s ==> countable t`,
RWTAC [countable_def] THEN
METIS_TAC [INJ_SUBSET]);

val image_countable = Q.store_thm ("image_countable",
`!f s. countable s ==> countable (IMAGE f s)`,
RWTAC [countable_surj, SURJ_DEF] THEN
Cases_on `s = {}` THEN
FSTAC [IN_IMAGE, IN_UNIV] THEN
Q.EXISTS_TAC `f o f'` THEN
RWTAC [] THEN
METIS_TAC []);

val finite_countable = Q.store_thm ("finite_countable",
`!s. FINITE s ==> countable s`,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
RWTAC [countable_def] THEN
FSTAC [INJ_DEF, IN_UNIV] THEN
Q.EXISTS_TAC `\x. if x IN s then f x else SUC (MAX_SET (IMAGE f s))` THEN
RWTAC [] THEN
`IMAGE f s <> {}` by (CCONTR_TAC THEN FSTAC [IMAGE_DEF])
THENL [
  `MAX_SET (IMAGE f s) IN IMAGE f s /\
   (f x <= MAX_SET (IMAGE f s))`
       by METIS_TAC [MAX_SET_DEF, IMAGE_FINITE, IN_IMAGE] THEN
  METIS_TAC [DECIDE ``~(SUC x <= x)``],
  `MAX_SET (IMAGE f s) IN IMAGE f s /\
   (f y <= MAX_SET (IMAGE f s))`
          by METIS_TAC [MAX_SET_DEF, IMAGE_FINITE, IN_IMAGE] THEN
     METIS_TAC [DECIDE ``!x. ~(SUC x <= x)``]
]);

open numpairTheory

val num_to_pair_def = TotalDefn.Define `num_to_pair n = (nfst n, nsnd n)`
val pair_to_num_def = TotalDefn.Define `pair_to_num (m,n) = m *, n`

val pair_to_num_formula = Q.store_thm ("pair_to_num_formula",
  `!x y. pair_to_num (x, y) = (x + y + 1) * (x + y) DIV 2 + y`,
  SRW_TAC [][pair_to_num_def, tri_formula, npair_def, MULT_COMM]);

val pair_to_num_inv = Q.store_thm ("pair_to_num_inv",
  `(!x. pair_to_num (num_to_pair x) = x) /\
   (!x y. num_to_pair (pair_to_num (x, y)) = (x, y))`,
  SRW_TAC [][pair_to_num_def, num_to_pair_def]);

val num_cross_countable = Q.prove (
  `countable (UNIV:num set CROSS UNIV:num set)`,
  RWTAC [countable_surj, SURJ_DEF, CROSS_DEF] THEN
  METIS_TAC [PAIR, pair_to_num_inv]);

val cross_countable = Q.store_thm ("cross_countable",
`!s t. countable s /\ countable t ==> countable (s CROSS t)`,
RWTAC [] THEN
POP_ASSUM (MP_TAC o SIMP_RULE bool_ss [countable_surj]) THEN
POP_ASSUM (MP_TAC o SIMP_RULE bool_ss [countable_surj]) THEN
RWTAC [SURJ_DEF] THEN
RWTAC [CROSS_EMPTY, FINITE_EMPTY, finite_countable] THEN
`s CROSS t = IMAGE (\(x, y). (f x, f' y)) (UNIV:num set CROSS UNIV:num set)`
        by  (RWTAC [CROSS_DEF, IMAGE_DEF, EXTENSION] THEN
             EQ_TAC THEN
             RWTAC [] THENL
             [Cases_on `x` THEN
                  FSTAC [] THEN
                  RES_TAC THEN
                  Q.EXISTS_TAC `(y', y)` THEN
                  RWTAC [],
              Cases_on `x'` THEN
                  FSTAC [],
              Cases_on `x'` THEN
                  FSTAC []]) THEN
METIS_TAC [num_cross_countable, image_countable]);

val inter_countable = Q.store_thm ("inter_countable",
`!s t. countable s \/ countable t ==> countable (s INTER t)`,
METIS_TAC [INTER_SUBSET, subset_countable]);

val inj_countable = Q.store_thm ("inj_countable",
`!f s t. countable t /\ INJ f s t ==> countable s`,
RWTAC [countable_def, INJ_DEF] THEN
Q.EXISTS_TAC `f' o f` THEN
RWTAC []);

val bigunion_countable = Q.store_thm ("bigunion_countable",
`!s. countable s /\ (!x. x IN s ==> countable x) ==> countable (BIGUNION s)`,
RWTAC [] THEN
`!x. ?f. x IN s ==> INJ f x (UNIV:num set)`
           by (RWTAC [RIGHT_EXISTS_IMP_THM] THEN
               FSTAC [countable_def]) THEN
`!a. ?x. a IN BIGUNION s ==> a IN x /\ x IN s`
           by (RWTAC [IN_BIGUNION] THEN
               METIS_TAC []) THEN
FSTAC [SKOLEM_THM] THEN
`?g. INJ g s (UNIV:num set)`
           by (FSTAC [countable_def] THEN
               METIS_TAC []) THEN
`INJ (\a. (g (f' a),  f (f' a) a)) (BIGUNION s)
     (UNIV:num set CROSS UNIV:num set)`
         by (FSTAC [INJ_DEF] THEN
             RWTAC [] THEN
             `f' a = f' a'` by METIS_TAC [] THEN
             FSTAC [] THEN
             METIS_TAC []) THEN
METIS_TAC [inj_countable, num_cross_countable]);

val union_countable = Q.store_thm ("union_countable",
`!s t. countable s /\ countable t ==> countable (s UNION t)`,
RWTAC [] THEN
`!x. x IN {s; t} ==> countable x` by RWTAC [] THEN
`FINITE {s; t}` by RWTAC [] THEN
`s UNION t = BIGUNION {s; t}`
          by (RWTAC [EXTENSION, IN_UNION, IN_BIGUNION] THEN
              METIS_TAC []) THEN
METIS_TAC [bigunion_countable, finite_countable]);

val union_countable_IFF = store_thm(
  "union_countable_IFF",
  ``countable (s UNION t) <=> countable s /\ countable t``,
  METIS_TAC [union_countable, SUBSET_UNION, subset_countable]);
val _ = export_rewrites ["union_countable_IFF"]

val inj_image_countable_IFF = store_thm(
  "inj_image_countable_IFF",
  ``INJ f s (IMAGE f s) ==> (countable (IMAGE f s) <=> countable s)``,
  SRW_TAC[][EQ_IMP_THM, image_countable] THEN
  METIS_TAC[countable_def, INJ_COMPOSE]);

val pow_no_surj = Q.store_thm ("pow_no_surj",
`!s. ~?f. SURJ f s (POW s)`,
RWTAC [SURJ_DEF, POW_DEF, METIS_PROVE [] ``a \/ b = ~a ==> b``] THEN
Q.EXISTS_TAC `{a | a IN s /\ a NOTIN f a}` THEN
RWTAC [EXTENSION, SUBSET_DEF] THEN
METIS_TAC []);

val infinite_pow_uncountable = Q.store_thm ("infinite_pow_uncountable",
`!s. INFINITE s ==> ~countable (POW s)`,
RWTAC [countable_surj, infinite_num_inj] THENL
[RWTAC [POW_DEF, EXTENSION, SUBSET_DEF] THEN
     METIS_TAC [],
 IMP_RES_TAC inj_surj THEN
     FSTAC [UNIV_NOT_EMPTY] THEN
     METIS_TAC [pow_no_surj, SURJ_COMPOSE]]);

val countable_Usum = store_thm(
  "countable_Usum",
  ``countable univ(:'a + 'b) <=>
      countable univ(:'a) /\ countable univ(:'b)``,
  SRW_TAC [][SUM_UNIV, inj_image_countable_IFF, INJ_INL, INJ_INR]);
val _ = export_rewrites ["countable_Usum"]

val countable_EMPTY = store_thm(
  "countable_EMPTY",
  ``countable {}``,
  SIMP_TAC (srw_ss()) [countable_def, INJ_EMPTY]);
val _ = export_rewrites ["countable_EMPTY"]

val countable_INSERT = store_thm(
  "countable_INSERT",
  ``countable (x INSERT s) <=> countable s``,
  Cases_on `x IN s` THEN1 ASM_SIMP_TAC (srw_ss()) [ABSORPTION_RWT] THEN
  SIMP_TAC (srw_ss()) [countable_def] THEN EQ_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `f` ASSUME_TAC) THENL [
    Q.EXISTS_TAC `f` THEN MATCH_MP_TAC INJ_SUBSET THEN
    Q.EXISTS_TAC `x INSERT s` THEN ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF],
    Q.EXISTS_TAC `\y. if y IN s then f y + 1 else 0` THEN
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [INJ_DEF]
  ]);
val _ = export_rewrites ["countable_INSERT"]

val cross_countable_IFF = store_thm(
  "cross_countable_IFF",
  ``countable (s CROSS t) <=>
     (s = {}) \/ (t = {}) \/ countable s /\ countable t``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM, cross_countable] THEN
  STRIP_TAC THEN
  `(s = {}) \/ ?a s0. (s = a INSERT s0) /\ a NOTIN s0`
    by METIS_TAC [SET_CASES] THEN1 SRW_TAC [][] THEN
  `(t = {}) \/ ?b t0. (t = b INSERT t0) /\ b NOTIN t0`
    by METIS_TAC [SET_CASES] THEN1 SRW_TAC [][] THEN
  `?fg:'a # 'b -> num.
     !xy1 xy2. xy1 IN s CROSS t /\ xy2 IN s CROSS t ==>
     ((fg xy1 = fg xy2) <=> (xy1 = xy2))`
    by (Q.UNDISCH_THEN `countable (s CROSS t)` MP_TAC THEN
        SIMP_TAC bool_ss [countable_def, INJ_DEF, IN_UNIV] THEN
        METIS_TAC[]) THEN
  `countable s`
    by (SIMP_TAC (srw_ss()) [countable_def] THEN
        Q.EXISTS_TAC `\x. fg (x,b)` THEN
        SIMP_TAC (srw_ss()) [INJ_DEF] THEN
        MAP_EVERY Q.X_GEN_TAC [`a1`, `a2`] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (Q.SPECL_THEN [`(a1,b)`, `(a2,b)`] MP_TAC) THEN
        NTAC 2 (POP_ASSUM MP_TAC) THEN
        ASM_SIMP_TAC (srw_ss()) []) THEN
  `countable t`
    by (SIMP_TAC (srw_ss()) [countable_def] THEN
        Q.EXISTS_TAC `\y. fg (a,y)` THEN
        SIMP_TAC (srw_ss()) [INJ_DEF] THEN
        MAP_EVERY Q.X_GEN_TAC [`b1`, `b2`] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (Q.SPECL_THEN [`(a,b1)`, `(a,b2)`] MP_TAC) THEN
        NTAC 2 (POP_ASSUM MP_TAC) THEN
        ASM_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][]);

val countable_Uprod = store_thm(
  "countable_Uprod",
  ``countable univ(:'a # 'b) <=> countable univ(:'a) /\ countable univ(:'b)``,
  SIMP_TAC (srw_ss()) [CROSS_UNIV, cross_countable_IFF]);

(* END countability theorems *)


(* Misc theorems added by Thomas Tuerk on 2009-03-24 *)

val IMAGE_BIGUNION = store_thm ("IMAGE_BIGUNION",
  ``!f M. IMAGE f (BIGUNION M) =
	  BIGUNION (IMAGE (IMAGE f) M)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC bool_ss [IN_BIGUNION, IN_IMAGE,
	GSYM LEFT_EXISTS_AND_THM,
	GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);


val SUBSET_DIFF = store_thm("SUBSET_DIFF",
``!s1 s2 s3.
(s1 SUBSET (s2 DIFF s3)) =
((s1 SUBSET s2) /\ (DISJOINT s1 s3))``,

SIMP_TAC bool_ss [SUBSET_DEF, IN_DIFF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
METIS_TAC[])

val INTER_SUBSET_EQN = store_thm ("INTER_SUBSET_EQN",

``((A INTER B = A) = (A SUBSET B)) /\
  ((A INTER B = B) = (B SUBSET A))``,

SIMP_TAC bool_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN
METIS_TAC[]);


val PSUBSET_SING = store_thm ("PSUBSET_SING",
``!s x. x PSUBSET {s} = (x = EMPTY)``,

SIMP_TAC bool_ss [PSUBSET_DEF, SUBSET_DEF, EXTENSION,
		 IN_SING, NOT_IN_EMPTY] THEN
METIS_TAC[]);


val INTER_UNION = store_thm ("INTER_UNION",
``((A UNION B) INTER A = A) /\
  ((B UNION A) INTER A = A) /\
  (A INTER (A UNION B) = A) /\
  (A INTER (B UNION A) = A)``,
SIMP_TAC bool_ss [INTER_SUBSET_EQN, SUBSET_UNION]);


val UNION_DELETE = store_thm ("UNION_DELETE",
``!A B x. (A UNION B) DELETE x =
  ((A DELETE x) UNION (B DELETE x))``,

SIMP_TAC bool_ss [EXTENSION, IN_UNION, IN_DELETE] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC bool_ss [])



val DELETE_SUBSET_INSERT = store_thm ("DELETE_SUBSET_INSERT",
``!s e s2.
  s DELETE e SUBSET s2 =
  s SUBSET e INSERT s2``,

SIMP_TAC bool_ss [SUBSET_DEF, IN_DELETE, IN_INSERT] THEN
METIS_TAC[]);



val IN_INSERT_EXPAND = store_thm ("IN_INSERT_EXPAND",
``!x y P. x IN y INSERT P =
  (x = y) \/ (~(x = y) /\ x IN P)``,

SIMP_TAC bool_ss [IN_INSERT] THEN
METIS_TAC[]);



val FINITE_INTER = store_thm ("FINITE_INTER",
``!s1 s2. ((FINITE s1) \/ (FINITE s2)) ==>
  FINITE (s1 INTER s2)``,

REPEAT GEN_TAC THEN
`((s1 INTER s2) SUBSET s1) /\ ((s1 INTER s2) SUBSET s2)` by ALL_TAC THEN1 (
   SIMP_TAC bool_ss [SUBSET_DEF, IN_INTER]
) THEN
METIS_TAC[SUBSET_FINITE]);


(* END misc thms *)


val _ = export_rewrites
    [
     (* BIGUNION/BIGINTER theorems *)
     "IN_BIGINTER", "DISJOINT_BIGUNION",
     "BIGUNION_UNION", "BIGINTER_UNION",
     "DISJOINT_BIGUNION", "BIGINTER_EMPTY", "BIGINTER_INSERT",
     (* cardinality theorems *)
     "CARD_DIFF", "CARD_EQ_0",
     "CARD_INTER_LESS_EQ", "CARD_DELETE", "CARD_DIFF",
     (* complement theorems *)
     "COMPL_CLAUSES", "COMPL_COMPL", "COMPL_EMPTY", "IN_COMPL",
     (* "DELETE" theorems *)
     "DELETE_DELETE", "DELETE_EQ_SING", "DELETE_SUBSET",
     (* "DIFF" theorems *)
     "DIFF_DIFF", "DIFF_EMPTY", "DIFF_EQ_EMPTY", "DIFF_UNIV",
     "DIFF_SUBSET",
     (* "DISJOINT" theorems *)
     "DISJOINT_EMPTY", "DISJOINT_INSERT", "DISJOINT_UNION_BOTH",
     "DISJOINT_EMPTY_REFL_RWT",
     (* "IMAGE" theorems *)
     "IMAGE_DELETE", "IMAGE_FINITE", "IMAGE_ID", "IMAGE_IN",
     "IMAGE_SUBSET", "IMAGE_UNION",
     (* "INSERT" theorems *)
     "INSERT_DELETE", "INSERT_DIFF", "INSERT_INSERT", "INSERT_SUBSET",
     (* "INTER" theorems *)
     "INTER_FINITE", "INTER_IDEMPOT",
     "INTER_SUBSET", "INTER_UNIV", "SUBSET_INTER",
     (* "PSUBSET" *)
     "PSUBSET_IRREFL",
     (* "REST" *)
     "REST_PSUBSET", "REST_SUBSET", "FINITE_REST",
     (* "SUBSET" *)
     "SUBSET_INSERT", "SUBSET_REFL",
     (* "UNION" *)
     "UNION_IDEMPOT", "UNION_SUBSET",
     "SUBSET_UNION"
];

val sspec_conv_str =
"local\n\
\  val GSPEC_t = prim_mk_const{Name = \"GSPEC\", Thy = \"pred_set\"}\n\
\  val IN_t = mk_thy_const{Name = \"IN\", Thy = \"bool\",\n\
\                          Ty = alpha --> (alpha --> bool) --> bool}\n\
\  val f_t = mk_var(\"f\", beta --> pairSyntax.mk_prod(alpha, bool))\n\
\  val x_t = mk_var(\"x\", alpha)\n\
\  \n\
\  val SET_SPEC_CONV =\n\
\    {conv = Lib.K (Lib.K (PGspec.SET_SPEC_CONV GSPECIFICATION)),\n\
\     key = SOME ([], list_mk_comb(IN_t, [x_t, mk_comb(GSPEC_t, f_t)])),\n\
\     name = \"SET_SPEC_CONV\",\n\
\     trace = 2}\n\
\  in\n\
\  val SET_SPEC_ss = simpLib.SSFRAG {name=SOME\"SET_SPEC\", ac = [], congs = [],\n\
\                                     convs = [SET_SPEC_CONV], dprocs = [],\n\
\                                     filter = NONE, rewrs = []}\n\
\  val _ = BasicProvers.augment_srw_ss [SET_SPEC_ss]\n  end\n"

fun sigps pps = (PP.add_string pps "val SET_SPEC_ss : simpLib.ssfrag";
                 PP.add_newline pps)

val _ = adjoin_to_theory {sig_ps = SOME sigps,
                          struct_ps =
                          SOME (fn pps => PP.add_string pps sspec_conv_str)}

val _ = adjoin_to_theory
  {sig_ps = NONE,
   struct_ps = SOME (fn pps =>
    let fun pp_line s = (PP.add_string pps s; PP.add_newline pps)
    in
     List.app pp_line
     ["val _ = ",
      " TypeBase.write",
      " [TypeBasePure.mk_nondatatype_info",
      "  (alpha --> bool,",
      "    {nchotomy = SOME SET_CASES,",
      "     induction = SOME FINITE_INDUCT,",
      "     size = SOME(Parse.Term`\\(obsize:'a->num) (y:'b). pred_set$SUM_IMAGE (\\x:'a. 1 + obsize x)`,SUM_IMAGE_THM),",
      "     encode=NONE})];\n"
      ] end)};

val _ = export_theory();
