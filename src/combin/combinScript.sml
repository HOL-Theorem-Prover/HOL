(* ===================================================================== *)
(* FILE          : combinScript.sml                                      *)
(* DESCRIPTION   : Basic combinator definitions and some theorems about  *)
(*                 them. Translated from hol88.                          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 87.02.26                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* AUGMENTED     : (kxs) added C and W combinators                       *)
(* ===================================================================== *)

open HolKernel Parse boolLib computeLib;

val _ = new_theory "combin";

(*---------------------------------------------------------------------------*)
(*  Some basic combinators: function composition, S, K, I, W, and C.         *)
(*---------------------------------------------------------------------------*)

fun def (s,l) p = Q.new_definition_at (DB_dtype.mkloc(s,l,false)) p

val K_DEF = def(#(FILE),#(LINE))("K_DEF",             ‘K = \x y. x’);
val S_DEF = def(#(FILE),#(LINE))("S_DEF[compute]",    ‘S = \f g x. f x (g x)’);
val I_DEF = def(#(FILE),#(LINE))("I_DEF",             ‘I = S K (K:'a->'a->'a)’);
val C_DEF = def(#(FILE),#(LINE))("C_DEF[compute]",    ‘C = \f x y. f y x’);
val W_DEF = def(#(FILE),#(LINE))("W_DEF[compute]",    ‘W = \f x. f x x’);
val o_DEF = def(#(FILE),#(LINE))("o_DEF",             ‘$o f g = \x. f(g x)’);
val _ = set_fixity "o" (Infixr 800)
val APP_DEF = def(#(FILE),#(LINE))("APP_DEF[compute]",‘$:> x f = f x’);

val UPDATE_def = def(#(FILE),#(LINE))("UPDATE_def",
   `UPDATE a b = \f c. if a = c then b else f c`);

val _ = set_fixity ":>" (Infixl 310);
val _ = set_mapped_fixity {tok = "=+", fixity = Infix(NONASSOC, 320),
                           term_name = "UPDATE"}
val _ = Parse.Unicode.unicode_version {tmnm = "o", u = UTF8.chr 0x2218}
val _ = TeX_notation {hol = "o", TeX = ("\\HOLTokenCompose", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2218, TeX = ("\\HOLTokenCompose", 1)}

val _ = let
  open combinpp
  fun addlform l r =
      add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                fixity = Suffix 2100,
                paren_style = OnlyIfNecessary,
                pp_elements = [
                  TOK l,
                  ListForm {
                    separator = [TOK ";", BreakSpace(1,0)],
                    block_info = (PP.CONSISTENT, 1),
                    cons = internal_consupd,
                    nilstr = internal_idupd
                  },
                  TOK r],
                term_name = toplevel_updname};
in
  set_mapped_fixity {fixity = Infix(NONASSOC,100),
                     term_name = mapsto_special,
                     tok = "|->"};
  set_mapped_fixity {fixity = Infix(NONASSOC,100),
                     term_name = mapsto_special,
                     tok = "↦"}; (* UOK *)
  addlform "(|" "|)";
  addlform UnicodeChars.lensel UnicodeChars.lenser;
  add_ML_dependency "combinpp";
  add_absyn_postprocessor "combin.UPDATE";
  inferior_overload_on (update_constname, ``UPDATE``);
  add_user_printer ("combin.updpp", “UPDATE k v f”)
end;

val _ = TeX_notation {TeX = ("\\llparenthesis", 1), hol = UnicodeChars.lensel}
val _ = TeX_notation {TeX = ("\\llparenthesis", 1), hol = "(|"}
val _ = TeX_notation {TeX = ("\\rrparenthesis", 1), hol = UnicodeChars.lenser}
val _ = TeX_notation {TeX = ("\\rrparenthesis", 1), hol = "|)"}
val _ = TeX_notation {TeX = ("\\HOLTokenMapto{}", 1), hol = "↦"}       (* UOK *)
val _ = TeX_notation {TeX = ("\\HOLTokenMapto{}", 1), hol = "|->"}

local open OpenTheoryMap in
  val _ = OpenTheory_const_name {const={Thy="combin",Name="K"},name=(["Function"],"const")}
  val _ = OpenTheory_const_name {const={Thy="combin",Name="C"},name=(["Function"],"flip")}
  val _ = OpenTheory_const_name {const={Thy="combin",Name="I"},name=(["Function"],"id")}
  val _ = OpenTheory_const_name {const={Thy="combin",Name="o"},name=(["Function"],"o")}
  val _ = OpenTheory_const_name {const={Thy="combin",Name="S"},name=(["Function","Combinator"],"s")}
  val _ = OpenTheory_const_name {const={Thy="combin",Name="W"},name=(["Function","Combinator"],"w")}
end

(*---------------------------------------------------------------------------*
 * In I_DEF, the type constraint is necessary in order to meet one of        *
 * the criteria for a definition : the tyvars of the lhs must be a           *
 * superset of those on the rhs.                                             *
 *---------------------------------------------------------------------------*)

Theorem o_THM[compute]:
   !f g x. (f o g) x = f(g x)
Proof
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC
QED

val o_ASSOC = store_thm("o_ASSOC",
   “!f g h. f o (g o h) = (f o g) o h”,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [ o_DEF ]
   THEN CONV_TAC (REDEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

Theorem o_ASSOC' = GSYM o_ASSOC

val o_ABS_L = store_thm(
  "o_ABS_L",
  ``(\x:'a. f x:'c) o (g:'b -> 'a) = (\x. f (g x))``,
  REWRITE_TAC [FUN_EQ_THM, o_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val o_ABS_R = store_thm(
  "o_ABS_R",
  ``f o (\x. g x) = (\x. f (g x))``,
  REWRITE_TAC [FUN_EQ_THM, o_THM] THEN BETA_TAC THEN REWRITE_TAC []);

Theorem K_THM[compute]:
    !x y. K x y = x
Proof
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ K_DEF ]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC
QED

Theorem K_PARTIAL : (* from seqTheory *)
    !x. K x = \z. x
Proof
    GEN_TAC >> PURE_REWRITE_TAC [K_DEF]
 >> BETA_TAC >> REFL_TAC
QED

val S_THM = store_thm("S_THM",
   “!f g x. S f g x = f x (g x)”,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ S_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val S_ABS_L = store_thm(
  "S_ABS_L",
  ``S (\x. f x) g = \x. (f x) (g x)``,
  REWRITE_TAC [FUN_EQ_THM, S_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val S_ABS_R = store_thm(
  "S_ABS_R",
  ``S f (\x. g x) = \x. (f x) (g x)``,
  REWRITE_TAC [FUN_EQ_THM, S_THM] THEN BETA_TAC THEN REWRITE_TAC[]);

val C_THM = store_thm("C_THM",
   “!f x y. C f x y = f y x”,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ C_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

val C_ABS_L = store_thm(
  "C_ABS_L",
  ``C (\x. f x) y = (\x. f x y)``,
  REWRITE_TAC [FUN_EQ_THM, C_THM] THEN BETA_TAC THEN REWRITE_TAC []);

val W_THM = store_thm("W_THM",
   “!f x. W f x = f x x”,
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ W_DEF ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC);

Theorem I_THM[compute]:
   !x. I x = x
Proof
   REPEAT GEN_TAC
   THEN PURE_REWRITE_TAC [ I_DEF, S_THM, K_THM ]
   THEN CONV_TAC (DEPTH_CONV BETA_CONV)
   THEN REFL_TAC
QED

Theorem I_EQ_IDABS:
  I = \x. x
Proof
  REWRITE_TAC[FUN_EQ_THM] >> BETA_TAC >> REWRITE_TAC[I_THM]
QED

val I_o_ID = store_thm("I_o_ID",
   “!f. (I o f = f) /\ (f o I = f)”,
   REWRITE_TAC [I_THM, o_THM, FUN_EQ_THM]);

Theorem K_o_THM[compute]:
  (!f v. K v o f = K v) /\ (!f v. f o K v = K (f v))
Proof
  REWRITE_TAC [o_THM, K_THM, FUN_EQ_THM]
QED

val UPDATE_APPLY = Q.store_thm("UPDATE_APPLY",
   `(!a x f. (a =+ x) f a = x) /\
    (!a b x f. a <> b ==> ((a =+ x) f b = f b))`,
   REWRITE_TAC [UPDATE_def]
   THEN BETA_TAC
   THEN REWRITE_TAC []
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC [])

Theorem UPDATE_APPLY1 = cj 1 UPDATE_APPLY

Theorem APPLY_UPDATE_THM[compute]:
  !f a b c. (a =+ b) f c = (if a = c then b else f c)
Proof
  PURE_REWRITE_TAC [UPDATE_def]
  THEN BETA_TAC THEN REWRITE_TAC []
QED

val UPDATE_COMMUTES = Q.store_thm("UPDATE_COMMUTES",
  `!f a b c d. ~(a = b) ==> ((a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f))`,
  REPEAT STRIP_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN BETA_TAC THEN GEN_TAC
  THEN NTAC 2 COND_CASES_TAC
  THEN BETA_TAC
  THEN PURE_ASM_REWRITE_TAC []
  THEN NTAC 2 (POP_ASSUM (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])))
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC []);

val UPDATE_EQ = Q.store_thm("UPDATE_EQ",
  `!f a b c. (a =+ c) ((a =+ b) f) = (a =+ c) f`,
  REPEAT STRIP_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN TRY GEN_TAC THEN BETA_TAC
  THEN NTAC 2 (TRY COND_CASES_TAC)
  THEN BETA_TAC THEN ASM_REWRITE_TAC []);

val UPDATE_APPLY_ID = Q.store_thm("UPDATE_APPLY_ID",
  `!f a b. (f a = b) = ((a =+ b) f = f)`,
  REPEAT GEN_TAC
  THEN EQ_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THENL [
    REPEAT STRIP_TAC
    THEN BETA_TAC
    THEN COND_CASES_TAC
    THEN1 POP_ASSUM (fn th => ASM_REWRITE_TAC [SYM th])
    THEN REWRITE_TAC [],
    BETA_TAC THEN STRIP_TAC
    THEN POP_ASSUM (Q.SPEC_THEN `a` ASSUME_TAC)
    THEN RULE_ASSUM_TAC (REWRITE_RULE [])
    THEN ASM_REWRITE_TAC []]);

val UPDATE_APPLY_ID' = GSYM UPDATE_APPLY_ID
Theorem UPDATE_APPLY_ID_RWT =
  CONJ UPDATE_APPLY_ID'
       (CONV_RULE (STRIP_QUANT_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)))
                  UPDATE_APPLY_ID')


val UPDATE_APPLY_IMP_ID = save_thm("UPDATE_APPLY_IMP_ID",
  GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL UPDATE_APPLY_ID))));

val APPLY_UPDATE_ID = Q.store_thm("APPLY_UPDATE_ID",
  `!f a. (a =+ f a) f = f`,
  REWRITE_TAC [GSYM UPDATE_APPLY_ID]);

Theorem UPD11_SAME_BASE:
  !f a b c d.
      ((a =+ c) f = (b =+ d) f) <=>
        a = b /\ c = d \/
        a <> b /\ (a =+ c) f = f /\ (b =+ d) f = f
Proof
  REPEAT GEN_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN BETA_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
  THEN ASM_CASES_TAC ``a = b`` THEN ASM_REWRITE_TAC []
  THENL [
    POP_ASSUM (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))
    THEN POP_ASSUM (Q.SPEC_THEN `b` ASSUME_TAC)
    THEN RULE_ASSUM_TAC (REWRITE_RULE [])
    THEN ASM_REWRITE_TAC [],
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []
    THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))
    THEN FIRST_ASSUM (Q.SPEC_THEN `x` ASSUME_TAC)
    THEN Q.PAT_ASSUM `~(a = x)` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
    THEN ASM_REWRITE_TAC []
  ]
QED

val SAME_KEY_UPDATE_DIFFER = Q.store_thm("SAME_KEY_UPDATE_DIFFER",
  `!f1 f2 a b c. ~(b = c) ==> ~((a =+ b) f = (a =+ c) f)`,
  REPEAT GEN_TAC THEN STRIP_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN BETA_TAC
  THEN STRIP_TAC
  THEN POP_ASSUM (Q.SPEC_THEN `a` ASSUME_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE [])
  THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
  THEN POP_ASSUM CONTR_TAC);

val UPD11_SAME_KEY_AND_BASE = Q.store_thm("UPD11_SAME_KEY_AND_BASE",
  `!f a b c. ((a =+ b) f = (a =+ c) f) = (b = c)`,
  REPEAT GEN_TAC THEN EQ_TAC
  THEN PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN BETA_TAC THEN STRIP_TAC
  THEN ASM_REWRITE_TAC []
  THEN POP_ASSUM (Q.SPEC_THEN `a` ASSUME_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE [])
  THEN ASM_REWRITE_TAC []);

val UPD_SAME_KEY_UNWIND = Q.store_thm("UPD_SAME_KEY_UNWIND",
  `!f1 f2 a b c.
      ((a =+ b) f1 = (a =+ c) f2) ==>
      (b = c) /\ !v. (a =+ v) f1 = (a =+ v) f2`,
  PURE_REWRITE_TAC [UPDATE_def,FUN_EQ_THM]
  THEN BETA_TAC THEN REPEAT STRIP_TAC
  THENL [
    POP_ASSUM (Q.SPEC_THEN `a` ASSUME_TAC)
    THEN RULE_ASSUM_TAC (REWRITE_RULE [])
    THEN ASM_REWRITE_TAC [],
    COND_CASES_TAC THEN REWRITE_TAC []
    THEN FIRST_ASSUM (Q.SPEC_THEN `x` ASSUME_TAC)
    THEN Q.PAT_ASSUM `~(a = x)` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
    THEN ASM_REWRITE_TAC []]);

(*---------------------------------------------------------------------------*)
(* Theorems using combinators to specify let-movements                       *)
(*---------------------------------------------------------------------------*)

val GEN_LET_RAND = store_thm(
  "GEN_LET_RAND",
  ``P (LET f v) = LET (P o f) v``,
  REWRITE_TAC [LET_THM, o_THM]);

val GEN_LET_RATOR = store_thm(
  "GEN_LET_RATOR",
  ``(LET f v) x = LET (C f x) v``,
  REWRITE_TAC [LET_THM, C_THM]);

val LET_FORALL_ELIM = store_thm(
  "LET_FORALL_ELIM",
  ``LET f v = (!) (S ((==>) o Abbrev o (C (=) v)) f)``,
  REWRITE_TAC [S_DEF, LET_THM, C_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [o_THM, markerTheory.Abbrev_def] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC
  ]);

val GEN_literal_case_RAND = store_thm(
  "GEN_literal_case_RAND",
  ``P (literal_case f v) = literal_case (P o f) v``,
  REWRITE_TAC [literal_case_THM, o_THM]);

val GEN_literal_case_RATOR = store_thm(
  "GEN_literal_case_RATOR",
  ``(literal_case f v) x = literal_case (C f x) v``,
  REWRITE_TAC [literal_case_THM, C_THM]);

val literal_case_FORALL_ELIM = store_thm(
  "literal_case_FORALL_ELIM",
  ``literal_case f v = (!) (S ((==>) o Abbrev o (C (=) v)) f)``,
  REWRITE_TAC [S_DEF, literal_case_THM, C_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [o_THM, markerTheory.Abbrev_def] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    ASM_REWRITE_TAC [],
    FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC
  ]);

(* ----------------------------------------------------------------------
    Predicates on functions
   ---------------------------------------------------------------------- *)

val ASSOC_DEF = new_definition("ASSOC_DEF",
  ``
    ASSOC (f:'a->'a->'a) <=> (!x y z. f x (f y z) = f (f x y) z)
  ``);

val COMM_DEF = new_definition("COMM_DEF",
  ``
     COMM (f:'a->'a->'b) <=> (!x y. f x y = f y x)
  ``);

val FCOMM_DEF = new_definition("FCOMM_DEF",
  ``
    FCOMM (f:'a->'b->'a) (g:'c->'a->'a) <=> (!x y z.  g x (f y z) = f (g x y) z)
  ``);

val RIGHT_ID_DEF = new_definition("RIGHT_ID_DEF",
  ``
    RIGHT_ID (f:'a->'b->'a) e <=> (!x. f x e = x)
  ``);

val LEFT_ID_DEF = new_definition("LEFT_ID_DEF",
  ``
    LEFT_ID (f:'a->'b->'b) e <=> (!x. f e x = x)
  ``);

val MONOID_DEF = new_definition("MONOID_DEF",
  ``
    MONOID (f:'a->'a->'a) e <=>
             ASSOC f /\ RIGHT_ID f e /\ LEFT_ID f e
  ``);

(* ======================================================================== *)
(*  Theorems about operators                                                *)
(* ======================================================================== *)

val ASSOC_CONJ = store_thm ("ASSOC_CONJ", ``ASSOC $/\``,
  REWRITE_TAC[ASSOC_DEF,CONJ_ASSOC]);

val ASSOC_SYM = save_thm ("ASSOC_SYM",
  CONV_RULE
    (STRIP_QUANT_CONV (RHS_CONV (STRIP_QUANT_CONV SYM_CONV)))
    ASSOC_DEF);


val ASSOC_DISJ = store_thm ("ASSOC_DISJ",
  ``ASSOC $\/``,
  REWRITE_TAC[ASSOC_DEF,DISJ_ASSOC]);

val FCOMM_ASSOC = store_thm ("FCOMM_ASSOC",
  ``!f: 'a->'a->'a. FCOMM f f = ASSOC f``,
  REWRITE_TAC[ASSOC_DEF,FCOMM_DEF]);

val MONOID_CONJ_T = store_thm ("MONOID_CONJ_T",
  ``MONOID $/\ T``,
  REWRITE_TAC[MONOID_DEF,CONJ_ASSOC, LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]);

val MONOID_DISJ_F = store_thm ("MONOID_DISJ_F",
  ``MONOID $\/ F``,
  REWRITE_TAC[MONOID_DEF,DISJ_ASSOC,
              LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]);

(*---------------------------------------------------------------------------*)
(* Congruence rule for composition. Grist for the termination condition      *)
(* extractor.                                                                *)
(*---------------------------------------------------------------------------*)

Theorem o_CONG:
  !a1 a2 g1 g2 f1 f2.
     a1 = a2 /\
     (!x. x = a2 ==> g1 x = g2 x) /\
     (!y. y = g2 a2 ==> f1 y = f2 y)
     ==>
     (f1 o g1) a1 = (f2 o g2) a2
Proof
 REPEAT STRIP_TAC THEN
 Q.PAT_X_ASSUM `a1 = a2` (SUBST_ALL_TAC o SYM) THEN
 POP_ASSUM (MP_TAC o Q.SPEC `g1 a1`) THEN
 POP_ASSUM (MP_TAC o Q.SPEC `a1`) THEN
 REWRITE_TAC[o_DEF] THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(*  Tag combinator equal to K. Used in generating ML from HOL                *)
(*---------------------------------------------------------------------------*)

val FAIL_DEF = Q.new_definition("FAIL_DEF", `FAIL = \x y. x`);

val FAIL_THM = Q.store_thm("FAIL_THM", `FAIL x y = x`,
    REPEAT GEN_TAC
    THEN PURE_REWRITE_TAC [ FAIL_DEF ]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN REFL_TAC);


Overload flip = “C”

val _ = remove_ovl_mapping "C" {Name="C", Thy = "combin"}

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(*                                                                           *)
(* (Ported from HOL-Light's sets.ml by Chun Tian)                            *)
(* ------------------------------------------------------------------------- *)

(* NOTE: the original definition in HOL-Light was:

   EXTENSIONAL s = {f :'a->'b | !x. x NOTIN s ==> f x = ARB}
 *)
val EXTENSIONAL_def = new_definition
  ("EXTENSIONAL_def",
   “EXTENSIONAL s (f :'a->'b) <=> !x. ~(x IN s) ==> f x = ARB”);

Theorem IN_EXTENSIONAL :
    !s (f :'a->'b). f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)
Proof
    REWRITE_TAC [IN_DEF]
 >> BETA_TAC
 >> rpt GEN_TAC
 >> REWRITE_TAC [FUN_EQ_THM, EXTENSIONAL_def, IN_DEF]
 >> BETA_TAC
 >> REWRITE_TAC []
QED

Theorem IN_EXTENSIONAL_UNDEFINED :
    !s (f :'a->'b) x. f IN EXTENSIONAL s /\ ~(x IN s) ==> f x = ARB
Proof
    REWRITE_TAC [IN_EXTENSIONAL]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> ASM_REWRITE_TAC []
QED

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(*                                                                           *)
(* NOTE: It's put here, so that RESTRICT in relationTheory can be defined    *)
(*       upon RESTRICTION. More theorems about RESTRICTION and EXTENSIONAL   *)
(*       are in pred_setTheory.                                              *)
(* ------------------------------------------------------------------------- *)

val RESTRICTION = new_definition
  ("RESTRICTION",
   “RESTRICTION s (f :'a->'b) x = if x IN s then f x else ARB”);

Theorem RESTRICTION_THM :
    !s (f :'a->'b). RESTRICTION s f = \x. if x IN s then f x else ARB
Proof
    rpt GEN_TAC
 >> REWRITE_TAC[FUN_EQ_THM, RESTRICTION]
 >> BETA_TAC
 >> REWRITE_TAC []
QED

Theorem RESTRICTION_DEFINED :
    !s (f :'a->'b) x. x IN s ==> RESTRICTION s f x = f x
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [RESTRICTION]
 >> COND_CASES_TAC >> REWRITE_TAC []
QED

Theorem RESTRICTION_UNDEFINED :
    !s (f :'a->'b) x. ~(x IN s) ==> RESTRICTION s f x = ARB
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [RESTRICTION]
 >> COND_CASES_TAC >> REWRITE_TAC []
QED

Theorem RESTRICTION_EQ :
    !s (f :'a->'b) x y. x IN s /\ f x = y ==> RESTRICTION s f x = y
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (fn th => (ONCE_REWRITE_TAC [SYM th]))
 >> MATCH_MP_TAC RESTRICTION_DEFINED
 >> ASM_REWRITE_TAC []
QED

(* NOTE: HOL-Light doesn't have this theorem. *)
Theorem EXTENSIONAL_RESTRICTION :
    !s (f :'a->'b). EXTENSIONAL s (RESTRICTION s (f :'a -> 'b))
Proof
    REWRITE_TAC [EXTENSIONAL_def, RESTRICTION, IN_DEF]
 >> BETA_TAC
 >> rpt STRIP_TAC
 >> reverse COND_CASES_TAC >- REFL_TAC
 >> POP_ASSUM MP_TAC
 >> ASM_REWRITE_TAC []
QED

val _ = export_theory();
