(* ===================================================================== *)
(* FILE          : listScript.sml                                        *)
(* DESCRIPTION   : The logical definition of the list type operator. The *)
(*                 type is defined and the following "axiomatization" is *)
(*                 proven from the definition of the type:               *)
(*                                                                       *)
(*                    |- !x f. ?fn. (fn [] = x) /\                       *)
(*                             (!h t. fn (h::t) = f (fn t) h t)          *)
(*                                                                       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* REVISED       : 87.03.14                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)

open HolKernel Parse boolLib BasicProvers;

open Num_conv mesonLib arithmeticTheory
     simpLib boolSimps pairTheory pred_setTheory TotalDefn metisLib
     relationTheory combinTheory quotientLib

local open pairTheory pred_setTheory Datatype OpenTheoryMap
in end;

val ERR = mk_HOL_ERR "listScript"

val arith_ss = bool_ss ++ numSimps.ARITH_ss ++ numSimps.REDUCE_ss
fun simp l = ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++numSimps.ARITH_ss) l
val rw = SRW_TAC []
val metis_tac = METIS_TAC
fun fs l = FULL_SIMP_TAC (srw_ss()) l
val std_ss = arith_ss ++ boolSimps.LET_ss;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;
val decide_tac = DECIDE_TAC;
val qexists_tac = Q.EXISTS_TAC;
val qid_spec_tac = Q.ID_SPEC_TAC;
val qx_gen_tac = Q.X_GEN_TAC;

val qxch = Q.X_CHOOSE_THEN;
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = qxch q (qxchl qs ttac);

val _ = new_theory "list";

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;
val zDefine = Lib.with_flag (computeLib.auto_import_definitions, false) Define
val dDefine = Lib.with_flag (Defn.def_suffix, "_DEF") Define
val bDefine = Lib.with_flag (Defn.def_suffix, "") Define

val NOT_SUC      = numTheory.NOT_SUC
and INV_SUC      = numTheory.INV_SUC
fun INDUCT_TAC g = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g;

val LESS_0       = prim_recTheory.LESS_0;
val NOT_LESS_0   = prim_recTheory.NOT_LESS_0;
val PRE          = prim_recTheory.PRE;
val LESS_MONO    = prim_recTheory.LESS_MONO;
val INV_SUC_EQ   = prim_recTheory.INV_SUC_EQ;
val num_Axiom    = prim_recTheory.num_Axiom;
val PAIR_EQ      = pairTheory.PAIR_EQ;

(*---------------------------------------------------------------------------*)
(* Declare the datatype of lists                                             *)
(*---------------------------------------------------------------------------*)

val _ = Datatype.Hol_datatype ‘list = NIL | CONS of 'a => list’;

local open OpenTheoryMap val cname = OpenTheory_const_name in
val ns = ["Data","List"]
val _ = OpenTheory_tyop_name{tyop={Thy="list",Tyop="list"},name=(ns,"list")}
val _ = cname{const={Thy="list",Name="APPEND"},name=(ns,"@")}
val _ = cname{const={Thy="list",Name="CONS"},name=(ns,"::")}
val _ = cname{const={Thy="list",Name="HD"},name=(ns,"head")}
val _ = cname{const={Thy="list",Name="EVERY"},name=(ns,"all")}
val _ = cname{const={Thy="list",Name="EXISTS"},name=(ns,"any")}
val _ = cname{const={Thy="list",Name="FILTER"},name=(ns,"filter")}
val _ = cname{const={Thy="list",Name="FLAT"},name=(ns,"concat")}
val _ = cname{const={Thy="list",Name="LENGTH"},name=(ns,"length")}
val _ = cname{const={Thy="list",Name="MAP"},name=(ns,"map")}
val _ = cname{const={Thy="list",Name="NIL"},name=(ns,"[]")}
val _ = cname{const={Thy="list",Name="REVERSE"},name=(ns,"reverse")}
val _ = cname{const={Thy="list",Name="TAKE"},name=(ns,"take")}
val _ = cname{const={Thy="list",Name="TL"},name=(ns,"tail")}
end

(*---------------------------------------------------------------------------*)
(* Fiddle with concrete syntax                                               *)
(*---------------------------------------------------------------------------*)

val _ = add_rule {term_name = "CONS", fixity = Infixr 490,
                  pp_elements = [TOK "::", BreakSpace(0,2)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 0))};

val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "["], rightdelim = [TOK "]"],
                      cons = "CONS", nilstr = "NIL",
                      block_info = (PP.INCONSISTENT, 1)};

(*---------------------------------------------------------------------------*)
(* Prove the axiomatization of lists                                         *)
(*---------------------------------------------------------------------------*)

val list_Axiom = TypeBase.axiom_of “:'a list”;

val list_Axiom_old = store_thm(
  "list_Axiom_old",
  Term‘!x f. ?!fn1:'a list -> 'b.
          (fn1 [] = x) /\ (!h t. fn1 (h::t) = f (fn1 t) h t)’,
  REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL [
    ASSUME_TAC list_Axiom THEN
    POP_ASSUM (ACCEPT_TAC o BETA_RULE o Q.SPECL [‘x’, ‘\x y z. f z x y’]),
    REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    HO_MATCH_MP_TAC (TypeBase.induction_of “:'a list”) THEN
    simpLib.ASM_SIMP_TAC boolSimps.bool_ss []
  ]);

(*---------------------------------------------------------------------------
     Now some definitions.
 ---------------------------------------------------------------------------*)

Definition NULL_DEF:
  (NULL []     = T) /\
  (NULL (h::t) = F)
End

Definition HD[simp]:
  HD (h::t) = h
End

Definition TL_DEF[simp]:
  TL [] = [] /\
  TL (h::t) = t
End
Theorem TL = CONJUNCT2 TL_DEF

Definition SUM:
  SUM [] = 0 /\
  SUM (h::t) = h + SUM t
End

Definition APPEND_def:
  APPEND [] l = l /\
  APPEND (h::l1) l2 = h::APPEND l1 l2
End

val _ = set_fixity "++" (Infixl 480);
val _ = overload_on ("++", Term‘APPEND’);
val _ = Unicode.unicode_version {u = UnicodeChars.doubleplus, tmnm = "++"}
val _ = TeX_notation { hol = UnicodeChars.doubleplus,
                       TeX = ("\\HOLTokenDoublePlus", 1) }

(* preserving old choice of quantification order *)
Theorem APPEND[simp]:
  (!l:'a list.  APPEND [] l = l) /\
  (!l1 l2 h:'a. APPEND (h::l1) l2 = h::(APPEND l1 l2))
Proof
  REWRITE_TAC[APPEND_def]
QED

Definition FLAT[simp]:
  FLAT []     = [] /\
  FLAT (h::t) = APPEND h (FLAT t)
End

Definition LENGTH[simp]:
  LENGTH []     = 0 /\
  LENGTH (h::t) = SUC (LENGTH t)
End

Definition MAP[simp]:
  MAP f [] = [] /\
  MAP f (h::t) = f h::MAP f t
End

Definition LIST_TO_SET_DEF[simp]:
  (LIST_TO_SET [] x <=> F) /\
  (LIST_TO_SET (h::t) x <=> (x = h) \/ LIST_TO_SET t x)
End

val _ = overload_on ("set", “LIST_TO_SET”)
val _ = overload_on ("MEM", “\h:'a l:'a list. h IN LIST_TO_SET l”)
val _ = overload_on ("", “\h:'a l:'a list. ~(h IN LIST_TO_SET l)”)
  (* last over load here causes the term ~(h IN LIST_TO_SET l) to not print
     using overloads.  In particular, this prevents the existing overload for
     NOTIN from firing in this type instance, and allows ~MEM a l to print
     because the pretty-printer will traverse into the negated term (printing
     the ~), and then the MEM overload will "fire".
  *)

Theorem LIST_TO_SET[simp]:
  LIST_TO_SET [] = {} /\
  LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t
Proof
  SRW_TAC [] [FUN_EQ_THM, IN_DEF]
QED

Definition FILTER[simp]:
  FILTER P [] = [] /\
  FILTER P (h::t) = if P h then (h::FILTER P t) else FILTER P t
End

Definition FOLDR:
  FOLDR (f:'a->'b->'b) e [] = e /\
  FOLDR f e (x::l) = f x (FOLDR f e l)
End

Definition FOLDL:
  FOLDL (f:'b->'a->'b) e [] = e /\
  FOLDL f e (x::l) = FOLDL f (f e x) l
End

Definition EVERY_DEF[simp]:
  (EVERY P [] <=> T) /\
  (EVERY P (h::t) <=> P h /\ EVERY P t)
End

Definition EXISTS_DEF[simp]:
  (EXISTS P [] <=> F) /\
  (EXISTS P (h::t) <=> P h \/ EXISTS P t)
End

Definition EL_def:
  EL 0 l = (HD l:'a) /\
  EL (SUC n) l = EL n (TL l)
End

(* preserving particular variable quantification order *)
Theorem EL:
  (!l.    EL 0 l = HD l:'a) /\
  (!l n.  EL (SUC n) l = EL n (TL l))
Proof
  REWRITE_TAC[EL_def]
QED

(* ---------------------------------------------------------------------*)
(* Definition of a function                                             *)
(*                                                                      *)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list         *)
(*                                                                      *)
(* for mapping a curried binary function down a pair of lists:          *)
(*                                                                      *)
(* |- (!f. MAP2 f[][] = []) /\                                          *)
(*   (!f h1 t1 h2 t2.                                                   *)
(*      MAP2 f(h1::t1)(h2::t2) = CONS(f h1 h2)(MAP2 f t1 t2))   *)
(*                                                                      *)
(* [TFM 92.04.21]                                                       *)
(* ---------------------------------------------------------------------*)

Definition MAP2_DEF[simp]:
  (MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2) /\
  (MAP2 f x y = [])
End

val MAP2 = store_thm ("MAP2",
“(!f. MAP2 f [] [] = []) /\
  (!f h1 t1 h2 t2. MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2)”,
METIS_TAC[MAP2_DEF]);

val MAP2_NIL = Q.store_thm(
  "MAP2_NIL[simp]",
  ‘MAP2 f x [] = []’,
  Cases_on ‘x’ >> simp[])

val LENGTH_MAP2 = Q.store_thm ("LENGTH_MAP2[simp]",
  ‘!xs ys. LENGTH (MAP2 f xs ys) = MIN (LENGTH xs) (LENGTH ys)’,
  Induct \\ rw [] \\ Cases_on ‘ys’ \\ fs [arithmeticTheory.MIN_DEF, MAP2_DEF]
  \\ SRW_TAC[][]);

val EL_MAP2 = Q.store_thm("EL_MAP2",
  ‘!ts tt n.
    n < MIN (LENGTH ts) (LENGTH tt) ==>
      (EL n (MAP2 f ts tt) = f (EL n ts) (EL n tt))’,
  Induct \\ rw [] \\ Cases_on ‘tt’ \\ Cases_on ‘n’ \\ fs [EL]);

Theorem MAP2_APPEND:
  !xs ys xs1 ys1 f.
     (LENGTH xs = LENGTH xs1) ==>
     (MAP2 f (xs ++ ys) (xs1 ++ ys1) = MAP2 f xs xs1 ++ MAP2 f ys ys1)
Proof Induct >> Cases_on ‘xs1’ >> fs [MAP2]
QED

(* ----------------------------------------------------------------------
    mapPartial : ('a -> 'b option) -> 'a list -> 'b list
   ---------------------------------------------------------------------- *)

Definition mapPartial_def[simp]:
  mapPartial f [] = [] /\
  mapPartial f (x :: xs) = case f x of NONE => mapPartial f xs
                                    | SOME y => y :: mapPartial f xs
End

Theorem mapPartial_EQ_NIL[simp]:
  mapPartial f xs = [] <=> !x. MEM x xs ==> f x = NONE
Proof
  Q.ID_SPEC_TAC ‘xs’ >> Induct >> simp[optionTheory.option_case_eq] >>
  metis_tac[]
QED

Theorem LENGTH_mapPartial:
  LENGTH (mapPartial f xs) <= LENGTH xs
Proof
  Q.ID_SPEC_TAC ‘xs’ >> Induct >>
  simp[] >> strip_tac >>
  DEEP_INTRO_TAC (GEN_ALL $ iffRL $ TypeBase.case_pred_disj_of “:'a option”) >>
  simp[] >> metis_tac[TypeBase.nchotomy_of “:'a option”]
QED

(* Some searches *)

Definition INDEX_FIND_def:
   (INDEX_FIND i P [] = NONE) /\
   (INDEX_FIND i P (h :: t) =
      if P h then SOME (i, h) else INDEX_FIND (SUC i) P t)
End

Definition FIND_def: FIND P = OPTION_MAP SND o INDEX_FIND 0 P
End
Definition INDEX_OF_def: INDEX_OF x = OPTION_MAP FST o INDEX_FIND 0 ($= x)
End

Theorem INDEX_FIND_add:
  !ls n.
    INDEX_FIND n P ls = OPTION_MAP (\(i, x). (i + n, x)) (INDEX_FIND 0 P ls)
Proof
  Induct >- ( rw[Once INDEX_FIND_def] \\ rw[Once INDEX_FIND_def] )
  \\ simp_tac(srw_ss())[Once INDEX_FIND_def, SimpRHS]
  \\ simp_tac(srw_ss())[Once INDEX_FIND_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp_tac(srw_ss())[]
  \\ first_assum(Q.SPEC_THEN`SUC n`(fn th => simp_tac(srw_ss())[th]))
  \\ first_x_assum(Q.SPEC_THEN`1`(fn th => simp_tac(srw_ss())[th]))
  \\ Cases_on`INDEX_FIND 0 P ls` \\ simp[]
  \\ simp[UNCURRY]
QED

Theorem FIND_thm:
  (FIND P [] = NONE) /\
  (FIND P (h::t) = if P h then SOME h else FIND P t)
Proof
  rw[FIND_def, INDEX_FIND_def] >> simp[Once INDEX_FIND_add, SimpLHS] >>
  simp[optionTheory.OPTION_MAP_COMPOSE, o_UNCURRY_R, combinTheory.o_ABS_R] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM, FORALL_PROD]
QED


Theorem INDEX_OF_eq_NONE:
  !x l. INDEX_OF x l = NONE <=> ~MEM x l
Proof
  gen_tac \\ Induct
  \\ rw[INDEX_OF_def, INDEX_FIND_def]
  \\ rw[Once INDEX_FIND_add]
  \\ fs[INDEX_OF_def]
QED

Theorem INDEX_OF_eq_SOME:
  !x l i. INDEX_OF x l = SOME i <=>
    (i < LENGTH l) /\ (EL i l = x) /\ (!j. (j < i) ==> EL j l <> x)
Proof
  gen_tac \\ Induct
  \\ simp[INDEX_OF_def, INDEX_FIND_def]
  \\ rpt gen_tac
  \\ simp[Once INDEX_FIND_add]
  \\ fs[INDEX_OF_def]
  \\ rw[PULL_EXISTS, UNCURRY]
  >- (
    Cases_on`i` \\ rw[EL]
    \\ rpt disj2_tac
    \\ Q.EXISTS_TAC`0` \\ rw[EL] )
  \\ Cases_on`i` \\ rw[arithmeticTheory.ADD1, EL]
  \\ rw[Once arithmeticTheory.FORALL_NUM, SimpRHS]
  \\ rw[arithmeticTheory.ADD1, EL]
QED

(* ---------------------------------------------------------------------*)
(* Proofs of some theorems about lists.                                 *)
(* ---------------------------------------------------------------------*)

val NULL = store_thm ("NULL",
 “NULL ([] :'a list) /\ (!h t. ~NULL(CONS (h:'a) t))”,
   REWRITE_TAC [NULL_DEF]);

(*---------------------------------------------------------------------------*)
(* List induction                                                            *)
(* |- P [] /\ (!t. P t ==> !h. P(h::t)) ==> (!x.P x)                         *)
(*---------------------------------------------------------------------------*)

val list_INDUCT0 = save_thm("list_INDUCT0",TypeBase.induction_of “:'a list”);

val list_INDUCT = Q.store_thm
("list_INDUCT",
 ‘!P. P [] /\ (!t. P t ==> !h. P (h::t)) ==> !l. P l’,
 REWRITE_TAC [list_INDUCT0]);  (* must use REWRITE_TAC, ACCEPT_TAC refuses
                                   to respect bound variable names *)

Theorem list_induction[allow_rebind] = list_INDUCT
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(*---------------------------------------------------------------------------*)
(* Cases theorem: |- !l. (l = []) \/ (?t h. l = h::t)                        *)
(*---------------------------------------------------------------------------*)

val list_cases = TypeBase.nchotomy_of “:'a list”;


val list_CASES = store_thm
("list_CASES",
 “!l. (l = []) \/ (?h t. l = h::t)”,
 mesonLib.MESON_TAC [list_cases]);

Theorem list_nchotomy[allow_rebind] = list_CASES

(*---------------------------------------------------------------------------*)
(* Definition of list_case more suitable to call-by-value computations       *)
(*---------------------------------------------------------------------------*)

val list_case_def = TypeBase.case_def_of “:'a list”;

val list_case_compute = store_thm("list_case_compute",
 “!(l:'a list). list_CASE l (b:'b) f =
                  if NULL l then b else f (HD l) (TL l)”,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [list_case_def, HD, TL, NULL_DEF]);

(*---------------------------------------------------------------------------*)
(* CONS_11:  |- !h t h' t'. (h::t = h' :: t') = (h = h') /\ (t = t')         *)
(*---------------------------------------------------------------------------*)

val CONS_11 = save_thm("CONS_11", TypeBase.one_one_of “:'a list”)

val NOT_NIL_CONS = save_thm("NOT_NIL_CONS", TypeBase.distinct_of “:'a list”);

val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);

val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 “!l1 l2. ~(l1 = l2) ==> !h1:'a. !h2. ~(h1::l1 = h2::l2)”,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [CONS_11]);

val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 “!h1:'a. !h2. ~(h1 = h2) ==> !l1 l2. ~(h1::l1 = h2::l2)”,
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [CONS_11]);

val EQ_LIST = store_thm("EQ_LIST",
 “!h1:'a.!h2.(h1=h2) ==> !l1 l2. (l1 = l2) ==> (h1::l1 = h2::l2)”,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [CONS_11]);

(* Theorem: ls <> [] <=> (ls = HD ls::TL ls) *)
(* Proof:
   If part: ls <> [] ==> (ls = HD ls::TL ls)
       ls <> []
   ==> ?h t. ls = h::t         by list_CASES
   ==> ls = (HD ls)::(TL ls)   by HD, TL
   Only-if part: (ls = HD ls::TL ls) ==> ls <> []
   This is true                by NOT_NIL_CONS
*)
val LIST_NOT_NIL = store_thm(
  "LIST_NOT_NIL",
  ``!ls. ls <> [] <=> (ls = HD ls::TL ls)``,
  metis_tac[list_CASES, HD, TL, NOT_NIL_CONS]);

Theorem CONS:
  !l : 'a list. ~NULL l ==> HD l :: TL l = l
Proof
  STRIP_TAC THEN
  STRIP_ASSUME_TAC (SPEC “l:'a list” list_CASES) THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_REWRITE_TAC [HD, TL, NULL]
QED

Theorem APPEND_NIL[simp]:
  !(l:'a list). APPEND l [] = l
Proof LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]
QED


Theorem APPEND_ASSOC:
 !(l1:'a list) l2 l3.
   APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3
Proof LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]
QED

Theorem LENGTH_APPEND[simp]:
  !(l1:'a list) (l2:'a list).
    LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2
Proof
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, APPEND, ADD_CLAUSES]
QED

Theorem MAP_APPEND[simp]:
  !(f:'a->'b) l1 l2.
    MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)
Proof
  STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, APPEND]
QED

Theorem MAP_ID[simp]:
  (MAP (\x. x) l = l) /\ (MAP I l = l)
Proof
  Induct_on ‘l’ THEN SRW_TAC [] [MAP]
QED

Theorem MAP_ID_I[quotient_simp]:
  MAP I = I
Proof
  simp[FUN_EQ_THM]
QED

Theorem LENGTH_MAP[simp]:
  !l (f:'a->'b). LENGTH (MAP f l) = LENGTH l
Proof
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH]
QED

Theorem MAP_EQ_NIL[simp]:
  !(l:'a list) (f:'a->'b).
    (MAP f l = [] <=> l = []) /\
    ([] = MAP f l <=> l = [])
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, NOT_CONS_NIL, NOT_NIL_CONS]
QED

Theorem MAP_EQ_CONS:
  MAP (f:'a -> 'b) l = h::t <=> ?x0 t0. l = x0::t0 /\ h = f x0 /\ t = MAP f t0
Proof
  Q.ISPEC_THEN ‘l’ STRUCT_CASES_TAC list_CASES THEN SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC[]
QED

Theorem MAP_EQ_SING[simp]:
  (MAP (f:'a -> 'b) l = [x]) <=> ?x0. (l = [x0]) /\ (x = f x0)
Proof SIMP_TAC (srw_ss()) [MAP_EQ_CONS]
QED

Theorem MAP_EQ_f:
  !f1 f2 l. MAP f1 l = MAP f2 l <=>  !e. MEM e l ==> f1 e = f2 e
Proof
  Induct_on ‘l’ THEN
  ASM_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, MAP, CONS_11, FORALL_AND_THM]
QED

Theorem MAP_o:
  !f:'b->'c. !g:'a->'b.  MAP (f o g) = (MAP f) o (MAP g)
Proof
  REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, o_THM]
QED

val MAP_MAP_o = store_thm("MAP_MAP_o",
    (“!(f:'b->'c) (g:'a->'b) l. MAP f (MAP g l) = MAP (f o g) l”),
    REPEAT GEN_TAC THEN REWRITE_TAC [MAP_o, o_DEF]
    THEN BETA_TAC THEN REFL_TAC);

(* Theorem alias *)
val MAP_COMPOSE = save_thm("MAP_COMPOSE", MAP_MAP_o);
(* val MAP_COMPOSE = |- !f g l. MAP f (MAP g l) = MAP (f o g) l: thm *)

val EL_MAP = store_thm("EL_MAP",
    (“!n l. n < (LENGTH l) ==> !f:'a->'b. EL n (MAP f l) = f (EL n l)”),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH, EL, MAP, LESS_MONO_EQ, NOT_LESS_0, HD, TL]);

val EL_APPEND_EQN = store_thm(
  "EL_APPEND_EQN",
  “!l1 l2 n.
       EL n (l1 ++ l2) =
       if n < LENGTH l1 then EL n l1 else EL (n - LENGTH l1) l2”,
  LIST_INDUCT_TAC >> simp_tac (srw_ss()) [] >> Cases_on ‘n’ >>
  asm_simp_tac (srw_ss()) [EL])

val MAP_TL = Q.store_thm("MAP_TL",
  ‘!l f. MAP f (TL l) = TL (MAP f l)’,
  Induct THEN REWRITE_TAC [TL_DEF, MAP]);

Theorem MEM_TL:
 !l x. MEM x (TL l) ==> MEM x l
Proof
 Induct \\ simp [TL]
QED

val EVERY_EL = store_thm ("EVERY_EL",
 “!(l:'a list) P. EVERY P l = !n. n < LENGTH l ==> P (EL n l)”,
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF, LENGTH, NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN INDUCT_TAC THENL
       [ASM_REWRITE_TAC [EL, HD],
        ASM_REWRITE_TAC [LESS_MONO_EQ, EL, TL]],
       REPEAT STRIP_TAC THENL
       [POP_ASSUM (MP_TAC o (SPEC (“0”))) THEN
        REWRITE_TAC [LESS_0, EL, HD],
        POP_ASSUM ((ANTE_RES_THEN ASSUME_TAC) o (MATCH_MP LESS_MONO)) THEN
        POP_ASSUM MP_TAC THEN REWRITE_TAC [EL, TL]]]);

val EVERY_CONJ = store_thm("EVERY_CONJ",
 “!P Q l. EVERY (\(x:'a). (P x) /\ (Q x)) l = (EVERY P l /\ EVERY Q l)”,
     NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

val EVERY_MEM = store_thm(
  "EVERY_MEM",
  “!P l:'a list. EVERY P l = !e. MEM e l ==> P e”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, LIST_TO_SET, IN_INSERT, NOT_IN_EMPTY] THEN
  mesonLib.MESON_TAC []);

val EVERY_MAP = store_thm(
  "EVERY_MAP",
  “!P f l:'a list. EVERY P (MAP f l) = EVERY (\x. P (f x)) l”,
  NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, MAP] THEN BETA_TAC THEN REWRITE_TAC []);

Theorem EVERY_SIMP:
  !c l:'a list. EVERY (\x. c) l <=> l = [] \/ c
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, NOT_CONS_NIL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
QED

val MONO_EVERY = store_thm(
  "MONO_EVERY",
  “(!x. P x ==> Q x) ==> (EVERY P l ==> EVERY Q l)”,
  Q.ID_SPEC_TAC ‘l’ THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (srw_ss()) []);
val _ = IndDefLib.export_mono "MONO_EVERY"

val EXISTS_MEM = store_thm(
  "EXISTS_MEM",
  “!P l:'a list. EXISTS P l = ?e. MEM e l /\ P e”,
  Induct_on ‘l’ THEN SRW_TAC [] [] THEN MESON_TAC[]);

val EXISTS_MAP = store_thm(
  "EXISTS_MAP",
  “!P f l:'a list. EXISTS P (MAP f l) = EXISTS (\x. P (f x)) l”,
  NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXISTS_DEF, MAP] THEN BETA_TAC THEN REWRITE_TAC []);

Theorem LIST_EXISTS_SIMP[simp]:
  !c l:'a list. EXISTS (\x. c) l <=> l <> [] /\ c
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXISTS_DEF, NOT_CONS_NIL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
QED

Theorem LIST_EXISTS_MONO[mono]:
  (!x. P x ==> Q x) ==> (EXISTS P l ==> EXISTS Q l)
Proof
  Q.ID_SPEC_TAC ‘l’ THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [DISJ_IMP_THM]
QED

val EVERY_NOT_EXISTS = store_thm(
  "EVERY_NOT_EXISTS",
  “!P l. EVERY P l = ~EXISTS (\x. ~P x) l”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [DE_MORGAN_THM]);

val EXISTS_NOT_EVERY = store_thm(
  "EXISTS_NOT_EVERY",
  “!P l. EXISTS P l = ~EVERY (\x. ~P x) l”,
  REWRITE_TAC [EVERY_NOT_EXISTS] THEN BETA_TAC THEN REWRITE_TAC [] THEN
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN REWRITE_TAC []);

Theorem MEM_APPEND[simp]:
  !e l1 l2. MEM e (APPEND l1 l2) <=> MEM e l1 \/ MEM e l2
Proof
  Induct_on ‘l1’ THEN SRW_TAC [] [DISJ_ASSOC]
QED

Theorem MEM_FILTER:
  !P L x. MEM x (FILTER P L) <=> P x /\ MEM x L
Proof Induct_on ‘L’ THEN SRW_TAC [] [] THEN PROVE_TAC[]
QED

val MEM_FLAT = Q.store_thm
("MEM_FLAT",
 ‘!x L. MEM x (FLAT L) = (?l. MEM l L /\ MEM x l)’,
 Induct_on ‘L’ THEN SRW_TAC [] [FLAT] THEN PROVE_TAC[]);

val FLAT_APPEND = Q.store_thm ("FLAT_APPEND",
   ‘!l1 l2. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)’,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [APPEND, FLAT]
   THEN ASM_REWRITE_TAC [APPEND_ASSOC]);
val _ = export_rewrites ["FLAT_APPEND"]

val FLAT_compute = Q.store_thm(
  "FLAT_compute",
  ‘(FLAT [] = []) /\
   (FLAT ([]::t) = FLAT t) /\
   (FLAT ((h::t1)::t2) = h::FLAT (t1::t2))’,
  SIMP_TAC (srw_ss()) []);

Theorem EVERY_FLAT:
  EVERY P (FLAT ls) <=> EVERY (EVERY P) ls
Proof  rw[EVERY_MEM,MEM_FLAT,PULL_EXISTS] >> metis_tac[]
QED

Theorem EVERY_APPEND:
  !P (l1:'a list) l2.
        EVERY P (APPEND l1 l2) <=> EVERY P l1 /\ EVERY P l2
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, EVERY_DEF, CONJ_ASSOC]
QED

Theorem EXISTS_APPEND:
  !P (l1:'a list) l2.
       EXISTS P (APPEND l1 l2) <=> EXISTS P l1 \/ EXISTS P l2
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, EXISTS_DEF, DISJ_ASSOC]
QED

val NOT_EVERY = store_thm(
  "NOT_EVERY",
  “!P l. ~EVERY P l = EXISTS ($~ o P) l”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF, DE_MORGAN_THM,
                   o_THM]);

val NOT_EXISTS = store_thm(
  "NOT_EXISTS",
  “!P l. ~EXISTS P l = EVERY ($~ o P) l”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF, DE_MORGAN_THM,
                   o_THM]);

val MEM_MAP = store_thm(
  "MEM_MAP",
  “!(l:'a list) (f:'a -> 'b) x.
       MEM x (MAP f l) = ?y. (x = f y) /\ MEM y l”,
  LIST_INDUCT_TAC THEN SRW_TAC [] [MAP] THEN PROVE_TAC[]);

Theorem MEM_MAP_f:
  !f l a. MEM a l ==> MEM (f a) (MAP f l)
Proof
  PROVE_TAC[MEM_MAP]
QED

val LENGTH_NIL = store_thm("LENGTH_NIL[simp]",
 “!l:'a list. (LENGTH l = 0) = (l = [])”,
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL]);

(* Note: There is LENGTH_NIL, but no LENGTH_NON_NIL *)

(* Theorem: 0 < LENGTH l <=> l <> [] *)
(* Proof:
   Since  (LENGTH l = 0) <=> (l = [])   by LENGTH_NIL
   l <> [] <=> LENGTH l <> 0,
            or 0 < LENGTH l             by NOT_ZERO_LT_ZERO
*)
val LENGTH_NON_NIL = store_thm(
  "LENGTH_NON_NIL",
  ``!l. 0 < LENGTH l <=> l <> []``,
  metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO]);

(* val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_EQ_NUM |> CONJUNCT1); *)
val LENGTH_EQ_0 = save_thm("LENGTH_EQ_0", LENGTH_NIL);
(* > val LENGTH_EQ_0 = |- !l. (LENGTH l = 0) <=> (l = []): thm *)

Theorem LENGTH1 :
    (1 = LENGTH l) <=> ?e. l = [e]
Proof
    Cases_on `l` >> srw_tac [][LENGTH_NIL]
QED

(* Theorem: (LENGTH l = 1) <=> ?x. l = [x] *)
(* Proof:
   If part: (LENGTH l = 1) ==> ?x. l = [x]
     Since LENGTH l <> 0, l <> []  by LENGTH_NIL
        or ?h t. l = h::t          by list_CASES
       and LENGTH t = 0            by LENGTH
        so t = []                  by LENGTH_NIL
     Hence l = [x]
   Only-if part: (l = [x]) ==> (LENGTH l = 1)
     True by LENGTH.
*)
val LENGTH_EQ_1 = store_thm(
  "LENGTH_EQ_1",
  ``!l. (LENGTH l = 1) <=> ?x. l = [x]``,
  rw [GSYM LENGTH1]
(*rw[EQ_IMP_THM] >| [
    `LENGTH l <> 0` by decide_tac >>
    `?h t. l = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
    `SUC (LENGTH t) = 1` by metis_tac[LENGTH] >>
    `LENGTH t = 0` by decide_tac >>
    metis_tac[LENGTH_NIL],
    rw[]
  ]*));

Theorem LENGTH2 :
    (2 = LENGTH l) <=> ?a b. l = [a;b]
Proof
    Cases_on `l` >> srw_tac [][LENGTH1]
QED

val LENGTH_NIL_SYM = store_thm (
   "LENGTH_NIL_SYM[simp]",
   “(0 = LENGTH l) = (l = [])”,
   PROVE_TAC[LENGTH_NIL]);

Theorem SING_HD[simp]:
  (([HD xs] = xs) <=> (LENGTH xs = 1)) /\
  ((xs = [HD xs]) <=> (LENGTH xs = 1))
Proof
  Cases_on ‘xs’ >> full_simp_tac(srw_ss())[LENGTH_NIL] >> metis_tac []
QED

val NULL_EQ = store_thm("NULL_EQ",
 “!l. NULL l = (l = [])”,
   Cases_on ‘l’ THEN REWRITE_TAC[NULL, NOT_CONS_NIL]);

val NULL_LENGTH = Q.store_thm("NULL_LENGTH",
  ‘!l. NULL l = (LENGTH l = 0)’,
  REWRITE_TAC[NULL_EQ, LENGTH_NIL]);

val LENGTH_CONS = store_thm("LENGTH_CONS",
 “!l n. (LENGTH l = SUC n) =
          ?h:'a. ?l'. (LENGTH l' = n) /\ (l = CONS h l')”,
    LIST_INDUCT_TAC THENL [
      REWRITE_TAC [LENGTH, NOT_EQ_SYM(SPEC_ALL NOT_SUC), NOT_NIL_CONS],
      REWRITE_TAC [LENGTH, INV_SUC_EQ, CONS_11] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      simpLib.ASM_SIMP_TAC boolSimps.bool_ss []
    ]);

val LENGTH_EQ_CONS = store_thm("LENGTH_EQ_CONS",
 “!P:'a list->bool.
    !n:num.
      (!l. (LENGTH l = SUC n) ==> P l) =
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)”,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH, NOT_NIL_CONS, NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH, INV_SUC_EQ, CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);

Theorem LENGTH_EQ_SUM:
  !l:'a list n1 n2.
    LENGTH l = n1+n2 <=>
    ?l1 l2. LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ l = l1++l2
Proof
  Induct_on ‘n1’ THEN1 (
     SIMP_TAC arith_ss [LENGTH_NIL, APPEND]
  ) THEN
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_CLAUSES, LENGTH_CONS,
    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM, APPEND] THEN
  PROVE_TAC[]
QED

Theorem LENGTH_EQ_NUM:
  (!l:'a list. LENGTH l = 0 <=> l = []) /\
  (!l:'a list n.
     LENGTH l = SUC n <=> ?h l'. LENGTH l' = n /\ l = h::l') /\
  (!l:'a list n1 n2.
     LENGTH l = n1+n2 <=>
     ?l1 l2. LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ l = l1++l2)
Proof
  SIMP_TAC arith_ss [LENGTH_NIL, LENGTH_CONS, LENGTH_EQ_SUM]
QED

val LENGTH_EQ_NUM_compute = save_thm ("LENGTH_EQ_NUM_compute",
   CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LENGTH_EQ_NUM);


val LENGTH_EQ_NIL = store_thm("LENGTH_EQ_NIL",
 “!P: 'a list->bool.
    (!l. (LENGTH l = 0) ==> P l) = P []”,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LENGTH],
    DISCH_TAC THEN
    INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [LENGTH, NOT_SUC]]]);;

val CONS_ACYCLIC = store_thm("CONS_ACYCLIC",
Term‘!l x. ~(l = x::l) /\ ~(x::l = l)’,
 LIST_INDUCT_TAC
 THEN ASM_REWRITE_TAC[CONS_11, NOT_NIL_CONS, NOT_CONS_NIL, LENGTH_NIL]);

Theorem APPEND_eq_NIL[simp]:
  (!l1 l2:'a list. ([] = APPEND l1 l2) <=> (l1=[]) /\ (l2=[])) /\
  (!l1 l2:'a list. (APPEND l1 l2 = []) <=> (l1=[]) /\ (l2=[]))
Proof
  CONJ_TAC THEN
  INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC
   THEN REWRITE_TAC [CONS_11, NOT_NIL_CONS, NOT_CONS_NIL, APPEND]
   THEN GEN_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
QED

Theorem NULL_APPEND[simp]:
  NULL (l1 ++ l2) <=> NULL l1 /\ NULL l2
Proof simp[NULL_LENGTH]
QED

Theorem MAP_EQ_APPEND:
  MAP (f:'a -> 'b) l = l1 ++ l2 <=>
  ?l10 l20. l = l10 ++ l20 /\ l1 = MAP f l10 /\ l2 = MAP f l20
Proof
  REVERSE EQ_TAC THEN1 SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [MAP_APPEND] THEN
  MAP_EVERY Q.ID_SPEC_TAC [‘l1’, ‘l2’, ‘l’] THEN LIST_INDUCT_TAC THEN
  SIMP_TAC (srw_ss()) [] THEN MAP_EVERY Q.X_GEN_TAC [‘h’, ‘l2’, ‘l1’] THEN
  Cases_on ‘l1’ THEN SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [MAP_EQ_CONS] THEN
  METIS_TAC[]
QED

val APPEND_EQ_SING = store_thm(
  "APPEND_EQ_SING",
  “(l1 ++ l2 = [e:'a]) <=>
      (l1 = [e]) /\ (l2 = []) \/ (l1 = []) /\ (l2 = [e])”,
  Cases_on ‘l1’ THEN SRW_TAC [] [CONJ_ASSOC]);

val APPEND_11 = store_thm(
  "APPEND_11",
  Term‘(!l1 l2 l3:'a list. (APPEND l1 l2 = APPEND l1 l3) = (l2 = l3)) /\
       (!l1 l2 l3:'a list. (APPEND l2 l1 = APPEND l3 l1) = (l2 = l3))’,
  CONJ_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, CONS_11, APPEND_NIL] THEN
  Q.SUBGOAL_THEN
    ‘!h l1 l2:'a list. APPEND l1 (h::l2) = APPEND (APPEND l1 [h]) l2’
    (ONCE_REWRITE_TAC o C cons [])
  THENL [
    GEN_TAC THEN POP_ASSUM (K ALL_TAC) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [APPEND, CONS_11] THEN POP_ASSUM ACCEPT_TAC,
    ASM_REWRITE_TAC [] THEN GEN_TAC THEN POP_ASSUM (K ALL_TAC) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND, CONS_11] THENL [
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [APPEND, CONS_11, NOT_NIL_CONS, DE_MORGAN_THM,
                   APPEND_eq_NIL, NOT_CONS_NIL],
      GEN_TAC THEN LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [APPEND, CONS_11, APPEND_eq_NIL, NOT_CONS_NIL,
                       NOT_NIL_CONS]
    ]
  ]);

Theorem APPEND_LENGTH_EQ:
  !l1 l1'. (LENGTH l1 = LENGTH l1') ==>
  !l2 l2'. (LENGTH l2 = LENGTH l2') ==>
           ((l1 ++ l2 = l1' ++ l2') <=> (l1 = l1') /\ (l2 = l2'))
Proof
  Induct THEN1
     (GEN_TAC THEN STRIP_TAC THEN ‘l1' = []’ by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [] []) THEN
  MAP_EVERY Q.X_GEN_TAC [‘h’,‘l1'’] THEN SRW_TAC [] [] THEN
  ‘?h' t'. l1' = h'::t'’ by METIS_TAC [LENGTH_CONS] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []
QED

val APPEND_11_LENGTH = save_thm ("APPEND_11_LENGTH",
 SIMP_RULE bool_ss [DISJ_IMP_THM, FORALL_AND_THM] (prove (
 (“!l1 l2 l1' l2'.
        ((LENGTH l1 = LENGTH l1') \/ (LENGTH l2 = LENGTH l2')) ==>
        (((l1 ++ l2) = (l1' ++ l2')) = ((l1 = l1') /\ (l2 = l2')))”),
     REPEAT GEN_TAC
     THEN Tactical.REVERSE
        (Cases_on ‘(LENGTH l1 = LENGTH l1') /\ (LENGTH l2 = LENGTH l2')’) THEN1
(
           DISCH_TAC
           THEN ‘~((l1 = l1') /\ (l2 = l2'))’ by PROVE_TAC[]
           THEN ASM_REWRITE_TAC[]
           THEN ‘~(LENGTH (l1 ++ l2) = LENGTH (l1' ++ l2'))’
             suffices_by PROVE_TAC[]
           THEN FULL_SIMP_TAC arith_ss [LENGTH_APPEND]
     ) THEN PROVE_TAC[APPEND_LENGTH_EQ])));


val APPEND_EQ_SELF = store_thm(
"APPEND_EQ_SELF",
“(!l1 l2:'a list. ((l1 ++ l2 = l1) = (l2 = []))) /\
  (!l1 l2:'a list. ((l1 ++ l2 = l2) = (l1 = []))) /\
  (!l1 l2:'a list. ((l1 = l1 ++ l2) = (l2 = []))) /\
  (!l1 l2:'a list. ((l2 = l1 ++ l2) = (l1 = [])))”,
PROVE_TAC[APPEND_11, APPEND_NIL, APPEND]);

Theorem mapPartial_EQ_CONS:
  !f xs y ys.
    mapPartial f xs = y::ys <=>
    ?p x s. xs = p ++ [x] ++ s /\ (!x0. MEM x0 p ==> f x0 = NONE) /\
            f x = SOME y /\ mapPartial f s = ys
Proof
  gen_tac >> Induct >> simp[APPEND_eq_NIL] >> rpt gen_tac >>
  Q.RENAME_TAC [‘option_CASE (f x)’] >> Cases_on ‘f x’ >> simp[]
  >- (rw[EQ_IMP_THM]
      >- (REWRITE_TAC [GSYM $ cj 2 APPEND] >>
          rpt $ irule_at Any EQ_REFL >> simp[DISJ_IMP_THM]) >>
      Q.RENAME_TAC [‘x::xs = p ++ [e] ++ s’] >> Cases_on ‘p’ >> fs[] >>
      rw[] >> metis_tac[]) >>
  iff_tac
  >- (rw[] >> Q.EXISTS_TAC ‘[]’ >> simp[])
  >- (strip_tac >> Q.RENAME_TAC [‘x::xs = p ++ [e] ++ s’] >>
      Cases_on ‘p’ >> fs[])
QED

val MEM_SPLIT = Q.store_thm
("MEM_SPLIT",
 ‘!x l. (MEM x l) = ?l1 l2. (l = l1 ++ x::l2)’,
 Induct_on ‘l’ THEN SRW_TAC [] [] THEN EQ_TAC THENL [
   SRW_TAC [][] THEN1 (MAP_EVERY Q.EXISTS_TAC [‘[]’,‘l’] THEN SRW_TAC [][]) THEN
   MAP_EVERY Q.EXISTS_TAC [‘a::l1’, ‘l2’] THEN SRW_TAC [] [],
   DISCH_THEN (Q.X_CHOOSE_THEN ‘l1’ (Q.X_CHOOSE_THEN ‘l2’ ASSUME_TAC)) THEN
   Cases_on ‘l1’ THEN FULL_SIMP_TAC(srw_ss()) [] THEN PROVE_TAC[]
 ])

val LIST_EQ_REWRITE = Q.store_thm
("LIST_EQ_REWRITE",
 ‘!l1 l2. (l1 = l2) =
      ((LENGTH l1 = LENGTH l2) /\
       ((!x. (x < LENGTH l1) ==> (EL x l1 = EL x l2))))’,

 LIST_INDUCT_TAC THEN Cases_on ‘l2’ THEN (
   ASM_SIMP_TAC arith_ss [LENGTH, NOT_CONS_NIL, CONS_11, EL]
 ) THEN
 GEN_TAC THEN EQ_TAC THEN SIMP_TAC arith_ss [] THENL [
   REPEAT STRIP_TAC THEN Cases_on ‘x’ THEN (
     ASM_SIMP_TAC arith_ss [EL, HD, TL]
   ),
   REPEAT STRIP_TAC THENL [
     POP_ASSUM (MP_TAC o SPEC “0:num”) THEN
     ASM_SIMP_TAC arith_ss [EL, HD, TL],
     Q.PAT_X_ASSUM ‘!x. x < Y ==> P x’ (MP_TAC o SPEC “SUC x”) THEN
     ASM_SIMP_TAC arith_ss [EL, HD, TL]
   ]
 ]);

val LIST_EQ = save_thm("LIST_EQ",
    GENL[“l1:'a list”, “l2:'a list”]
    (snd(EQ_IMP_RULE (SPEC_ALL LIST_EQ_REWRITE))));

val FOLDL_EQ_FOLDR = Q.store_thm
("FOLDL_EQ_FOLDR",
 ‘!f l e. (ASSOC f /\ COMM f) ==>
          ((FOLDL f e l) = (FOLDR f e l))’,
GEN_TAC THEN
FULL_SIMP_TAC bool_ss [RIGHT_FORALL_IMP_THM, COMM_DEF,
  ASSOC_DEF] THEN
STRIP_TAC THEN LIST_INDUCT_TAC THENL [
  SIMP_TAC bool_ss [FOLDR, FOLDL],

  ASM_SIMP_TAC bool_ss [FOLDR, FOLDL] THEN
  POP_ASSUM (K ALL_TAC) THEN
  Q.SPEC_TAC (‘l’, ‘l’) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [FOLDR]
]);

val FOLDR_CONS = store_thm(
"FOLDR_CONS",
“!f ls a. FOLDR (\x y. f x :: y) a ls = (MAP f ls)++a”,
GEN_TAC THEN Induct THEN SRW_TAC[] [FOLDR, MAP])

val LENGTH_TL = Q.store_thm
("LENGTH_TL",
  ‘!l. 0 < LENGTH l ==> (LENGTH (TL l) = LENGTH l - 1)’,
  Cases_on ‘l’ THEN SIMP_TAC arith_ss [LENGTH, TL]);

val FILTER_EQ_NIL = Q.store_thm
("FILTER_EQ_NIL",
 ‘!P l. (FILTER P l = []) = (EVERY (\x. ~(P x)) l)’,
 GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN (
    ASM_SIMP_TAC bool_ss [FILTER, EVERY_DEF, COND_RATOR, COND_RAND,
                          NOT_CONS_NIL]
 ));

val FILTER_NEQ_NIL = Q.store_thm
("FILTER_NEQ_NIL",
 ‘!P l. ~(FILTER P l = []) = ?x. MEM x l /\ P x’,
 SIMP_TAC bool_ss [FILTER_EQ_NIL, EVERY_NOT_EXISTS, EXISTS_MEM]);

val FILTER_EQ_ID = Q.store_thm
("FILTER_EQ_ID",
 ‘!P l. (FILTER P l = l) = (EVERY P l)’,
 Induct_on ‘l’ THEN SRW_TAC [] [] THEN
 DISCH_THEN (ASSUME_TAC o Q.AP_TERM ‘MEM a’) THEN
 FULL_SIMP_TAC (srw_ss()) [MEM_FILTER]);

val FILTER_NEQ_ID = Q.store_thm
("FILTER_NEQ_ID",
 ‘!P l. ~(FILTER P l = l) = ?x. MEM x l /\ ~(P x)’,
 SIMP_TAC bool_ss [FILTER_EQ_ID, EVERY_NOT_EXISTS, EXISTS_MEM]);

Theorem FILTER_EQ_CONS:
  !P l h lr.
    FILTER P l = h::lr <=>
    ?l1 l2. l = l1++[h]++l2 /\ FILTER P l1 = [] /\ FILTER P l2 = lr /\ P h
Proof
  GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN
  ASM_SIMP_TAC bool_ss [FILTER, NOT_CONS_NIL, APPEND_eq_NIL] THEN
  REPEAT STRIP_TAC THEN Cases_on ‘P h’ THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC ‘[]’ THEN Q.EXISTS_TAC ‘l’ THEN
    FULL_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER],

    Cases_on ‘l1’ THEN
    FULL_SIMP_TAC bool_ss
      [APPEND, CONS_11, FILTER, COND_RAND, COND_RATOR, NOT_CONS_NIL],

    Q.EXISTS_TAC ‘h::l1’ THEN Q.EXISTS_TAC ‘l2’ THEN
    ASM_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER],

    Cases_on ‘l1’ THENL [
      FULL_SIMP_TAC bool_ss [APPEND, CONS_11],
      Q.EXISTS_TAC ‘l'’ THEN Q.EXISTS_TAC ‘l2’ THEN
      FULL_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER, COND_RATOR,
                             COND_RAND, NOT_CONS_NIL]
    ]
  ]
QED

Theorem FILTER_F[simp]:
  !xs. FILTER (\x. F) xs = []
Proof Induct >> simp[]
QED

Theorem FILTER_T[simp]:
  !xs. FILTER (\x. T) xs = xs
Proof Induct >> simp[]
QED

val FILTER_APPEND_DISTRIB = Q.store_thm
("FILTER_APPEND_DISTRIB",
 ‘!P L M. FILTER P (APPEND L M) = APPEND (FILTER P L) (FILTER P M)’,
   GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN RW_TAC bool_ss [FILTER, APPEND]);

Theorem MEM[simp]:
  (!x:'a. MEM x [] <=> F) /\ (!x:'a h t. MEM x (h::t) <=> x = h \/ MEM x t)
Proof SRW_TAC [] []
QED

val FILTER_EQ_APPEND = Q.store_thm
("FILTER_EQ_APPEND",
 ‘!P l l1 l2.
  (FILTER P l = l1 ++ l2) =
  (?l3 l4. (l = l3++l4) /\ (FILTER P l3 = l1) /\ (FILTER P l4 = l2))’,
GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN1 (
  ASM_SIMP_TAC bool_ss [FILTER, APPEND_eq_NIL] THEN PROVE_TAC[]
) THEN
REPEAT STRIP_TAC THEN Cases_on ‘P h’ THEN
ASM_SIMP_TAC bool_ss [FILTER] THENL [
  Cases_on ‘l1’ THENL [
    Cases_on ‘l2’ THENL [
      SIMP_TAC bool_ss [APPEND, NOT_CONS_NIL, FILTER_EQ_NIL, EVERY_MEM] THEN
      PROVE_TAC[MEM_APPEND, MEM],

      ASM_SIMP_TAC bool_ss [APPEND, CONS_11] THEN
      EQ_TAC THEN STRIP_TAC THENL [
        Q.EXISTS_TAC ‘[]’ THEN Q.EXISTS_TAC ‘h::l’ THEN
        FULL_SIMP_TAC bool_ss [APPEND, FILTER],

        Tactical.REVERSE (Cases_on ‘l3’) THEN1 (
           FULL_SIMP_TAC bool_ss [CONS_11, FILTER, APPEND,
                                  COND_RAND, COND_RATOR, NOT_CONS_NIL]
        ) THEN
        Cases_on ‘l4’ THEN (
          FULL_SIMP_TAC bool_ss [FILTER, NOT_CONS_NIL, APPEND,
                                 COND_RATOR, COND_RAND, CONS_11] THEN
          PROVE_TAC[]
        )
      ]
    ],

    ASM_SIMP_TAC bool_ss [APPEND, CONS_11] THEN
    EQ_TAC THEN STRIP_TAC THENL [
       Q.EXISTS_TAC ‘h::l3’ THEN Q.EXISTS_TAC ‘l4’ THEN
       FULL_SIMP_TAC bool_ss [APPEND, FILTER],

       Cases_on ‘l3’ THEN (
         FULL_SIMP_TAC bool_ss [APPEND, FILTER, NOT_CONS_NIL, FILTER, CONS_11,
                                COND_RAND, COND_RATOR] THEN
         PROVE_TAC[]
       )
    ]
  ],

  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC ‘h::l3’ THEN Q.EXISTS_TAC ‘l4’ THEN
    ASM_SIMP_TAC bool_ss [APPEND, FILTER],

    Cases_on ‘l3’ THENL [
       Cases_on ‘l4’ THEN
       FULL_SIMP_TAC bool_ss [APPEND, NOT_CONS_NIL, CONS_11] THEN
       Q.EXISTS_TAC ‘[]’ THEN Q.EXISTS_TAC ‘l’ THEN
       FULL_SIMP_TAC bool_ss [FILTER, APPEND] THEN
       PROVE_TAC[],

       Q.EXISTS_TAC ‘l'’ THEN Q.EXISTS_TAC ‘l4’ THEN
       FULL_SIMP_TAC bool_ss [FILTER, APPEND, CONS_11] THEN
       PROVE_TAC[]
    ]
  ]
]);

val EVERY_FILTER = Q.store_thm
("EVERY_FILTER",
 ‘!P1 P2 l. EVERY P1 (FILTER P2 l) =
            EVERY (\x. P2 x ==> P1 x) l’,

GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN (
  ASM_SIMP_TAC bool_ss [FILTER, EVERY_DEF, COND_RATOR, COND_RAND]
));

val EVERY_FILTER_IMP = Q.store_thm
("EVERY_FILTER_IMP",
 ‘!P1 P2 l. EVERY P1 l ==> EVERY P1 (FILTER P2 l)’,
GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN (
  ASM_SIMP_TAC bool_ss [FILTER, EVERY_DEF, COND_RATOR, COND_RAND]
));

val FILTER_COND_REWRITE = Q.store_thm
("FILTER_COND_REWRITE",
 ‘(FILTER P [] = []) /\
  (!h. (P h) ==> ((FILTER P (h::l) = h::FILTER P l))) /\
  (!h. ~(P h) ==> (FILTER P (h::l) = FILTER P l))’,
SIMP_TAC bool_ss [FILTER]);

val NOT_NULL_MEM = Q.store_thm
("NOT_NULL_MEM",
 ‘!l. ~(NULL l) = (?e. MEM e l)’,
  Cases_on ‘l’ THEN SIMP_TAC bool_ss [EXISTS_OR_THM, MEM, NOT_CONS_NIL, NULL]);

(* Computing EL when n is in numeral representation *)
Theorem EL_compute[allow_rebind]:
  !n. EL n l = if n=0 then HD l else EL (PRE n) (TL l)
Proof INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC, EL, PRE]
QED

(* a version of the above that is safe to use in the simplifier *)
(* only bother with BIT1/2 cases because the zero case is already provided
   by the definition. *)
val EL_simp = store_thm(
  "EL_simp",
  “(EL (NUMERAL (BIT1 n)) l = EL (PRE (NUMERAL (BIT1 n))) (TL l)) /\
    (EL (NUMERAL (BIT2 n)) l = EL (NUMERAL (BIT1 n)) (TL l))”,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
               arithmeticTheory.BIT1, arithmeticTheory.BIT2,
               arithmeticTheory.ADD_CLAUSES,
               prim_recTheory.PRE, EL]);

val EL_restricted = store_thm(
  "EL_restricted",
  “(EL 0 = HD) /\
    (EL (SUC n) (l::ls) = EL n ls)”,
  REWRITE_TAC [FUN_EQ_THM, EL, TL, HD]);
val _ = export_rewrites ["EL_restricted"]

val EL_simp_restricted = store_thm(
  "EL_simp_restricted",
  “(EL (NUMERAL (BIT1 n)) (l::ls) = EL (PRE (NUMERAL (BIT1 n))) ls) /\
    (EL (NUMERAL (BIT2 n)) (l::ls) = EL (NUMERAL (BIT1 n)) ls)”,
  REWRITE_TAC [EL_simp, TL]);
val _ = export_rewrites ["EL_simp_restricted"]

val SUM_eq_0 = store_thm("SUM_eq_0",
  “!ls. (SUM ls = 0) = !x. MEM x ls ==> (x = 0)”,
  LIST_INDUCT_TAC THEN SRW_TAC[] [SUM, MEM] THEN METIS_TAC[])

val NULL_FILTER = store_thm("NULL_FILTER",
  “!P ls. NULL (FILTER P ls) = !x. MEM x ls ==> ~P x”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  SRW_TAC[] [NULL, FILTER, MEM] THEN METIS_TAC[])


val WF_LIST_PRED = store_thm("WF_LIST_PRED",
Term‘WF \L1 L2. ?h:'a. L2 = h::L1’,
REWRITE_TAC[relationTheory.WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC CONTRAPOS_CONV
  THEN Ho_Rewrite.REWRITE_TAC
         [NOT_FORALL_THM, NOT_EXISTS_THM, NOT_IMP, DE_MORGAN_THM]
  THEN REWRITE_TAC [GSYM IMP_DISJ_THM] THEN STRIP_TAC
  THEN LIST_INDUCT_TAC THENL [ALL_TAC, GEN_TAC]
  THEN STRIP_TAC THEN RES_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_NIL_CONS, CONS_11])
  THENL [FIRST_ASSUM ACCEPT_TAC,
         PAT_X_ASSUM (Term‘x /\ y’) (SUBST_ALL_TAC o CONJUNCT2) THEN RES_TAC]);

(* ----------------------------------------------------------------------
    LIST_REL : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

    Lifts a relation point-wise to two lists
   ---------------------------------------------------------------------- *)

val (LIST_REL_rules, LIST_REL_ind, LIST_REL_cases) = IndDefLib.Hol_reln‘
  (LIST_REL R [] []) /\
  (!h1 h2 t1 t2. R h1 h2 /\ LIST_REL R t1 t2 ==> LIST_REL R (h1::t1) (h2::t2))
’;

val _ = overload_on ("listRel", “LIST_REL”)
val _ = overload_on ("LIST_REL", “LIST_REL”)

val LIST_REL_EL_EQN = store_thm(
  "LIST_REL_EL_EQN",
  “!R l1 l2. LIST_REL R l1 l2 <=>
              (LENGTH l1 = LENGTH l2) /\
              !n. n < LENGTH l1 ==> R (EL n l1) (EL n l2)”,
  GEN_TAC THEN SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    Induct_on ‘LIST_REL’ THEN SRW_TAC [] [] THEN
    Cases_on ‘n’ THEN FULL_SIMP_TAC (srw_ss()) [],
    Induct_on ‘l1’ THEN Cases_on ‘l2’ THEN SRW_TAC [] [LIST_REL_rules] THEN
    POP_ASSUM (fn th => Q.SPEC_THEN ‘0’ MP_TAC th THEN
                        Q.SPEC_THEN ‘SUC m’ (MP_TAC o Q.GEN ‘m’) th) THEN
    SRW_TAC [] [LIST_REL_rules]
  ]);

val LIST_REL_def = store_thm(
  "LIST_REL_def",
  “(LIST_REL R [][] <=> T) /\
    (LIST_REL R (a::as) [] <=> F) /\
    (LIST_REL R [] (b::bs) <=> F) /\
    (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs)”,
  REPEAT CONJ_TAC THEN SRW_TAC [] [Once LIST_REL_cases, SimpLHS]);
val _ = export_rewrites ["LIST_REL_def"]

val LIST_REL_mono = store_thm(
  "LIST_REL_mono",
  “(!x y. R1 x y ==> R2 x y) ==> LIST_REL R1 l1 l2 ==> LIST_REL R2 l1 l2”,
  SRW_TAC [] [LIST_REL_EL_EQN]);
val _ = IndDefLib.export_mono "LIST_REL_mono"

val LIST_REL_NIL = store_thm(
  "LIST_REL_NIL",
  “(LIST_REL R [] y <=> (y = [])) /\ (LIST_REL R x [] <=> (x = []))”,
  Cases_on ‘x’ THEN Cases_on ‘y’ THEN SRW_TAC [] []);
val _ = export_rewrites ["LIST_REL_NIL"]

val LIST_REL_CONS1 = store_thm(
  "LIST_REL_CONS1",
  “LIST_REL R (h::t) xs <=> ?h' t'. (xs = h'::t') /\ R h h' /\ LIST_REL R t t'”,
  Cases_on ‘xs’ THEN SRW_TAC [] []);

val LIST_REL_CONS2 = store_thm(
  "LIST_REL_CONS2",
  “LIST_REL R xs (h::t) <=> ?h' t'. (xs = h'::t') /\ R h' h /\ LIST_REL R t' t”,
  Cases_on ‘xs’ THEN SRW_TAC [] []);

val LIST_REL_CONJ = store_thm(
  "LIST_REL_CONJ",
  “LIST_REL (\a b. P a b /\ Q a b) l1 l2 <=>
      LIST_REL (\a b. P a b) l1 l2 /\ LIST_REL (\a b. Q a b) l1 l2”,
  SRW_TAC [] [LIST_REL_EL_EQN] THEN METIS_TAC []);

val LIST_REL_MAP1 = store_thm(
  "LIST_REL_MAP1",
  “LIST_REL R (MAP f l1) l2 <=> LIST_REL (R o f) l1 l2”,
  SRW_TAC [] [LIST_REL_EL_EQN, EL_MAP, LENGTH_MAP]);

val LIST_REL_MAP2 = store_thm(
  "LIST_REL_MAP2",
  “LIST_REL (\a b. R a b) l1 (MAP f l2) <=>
      LIST_REL (\a b. R a (f b)) l1 l2”,
  SRW_TAC [CONJ_ss] [LIST_REL_EL_EQN, EL_MAP, LENGTH_MAP]);

val LIST_REL_LENGTH = store_thm(
  "LIST_REL_LENGTH",
  “!x y. LIST_REL R x y ==> (LENGTH x = LENGTH y)”,
  Induct_on ‘LIST_REL’ THEN SRW_TAC [] [LENGTH]);

val LIST_REL_SPLIT1 = Q.store_thm("LIST_REL_SPLIT1",
  ‘!xs1 zs.
      LIST_REL P (xs1 ++ xs2) zs <=>
      ?ys1 ys2. (zs = ys1 ++ ys2) /\ LIST_REL P xs1 ys1 /\ LIST_REL P xs2 ys2’,
  Induct >> fs[APPEND] >> Cases_on ‘zs’ >> fs[] >> rpt strip_tac >>
  simp[LIST_REL_CONS1, PULL_EXISTS] >> metis_tac[]);

val LIST_REL_SPLIT2 = Q.store_thm("LIST_REL_SPLIT2",
  ‘!xs1 zs.
      LIST_REL P zs (xs1 ++ xs2) <=>
      ?ys1 ys2. (zs = ys1 ++ ys2) /\ LIST_REL P ys1 xs1 /\ LIST_REL P ys2 xs2’,
  Induct >> fs[APPEND] >> Cases_on ‘zs’ >> fs[] >> rpt strip_tac >>
  simp[LIST_REL_CONS2, PULL_EXISTS] >> metis_tac[]);

(* example of LIST_REL in action :
val (rules,ind,cases) = IndDefLib.Hol_reln`
  (!n m. n < m ==> R n m) /\
  (!n m. R n m ==> R1 (INL n) (INL m)) /\
  (!l1 l2. LIST_REL R l1 l2 ==> R1 (INR l1) (INR l2))
`
val strong = IndDefLib.derive_strong_induction (rules,ind)
*)

Theorem LIST_REL_equivalence :
    !R. equivalence R ==> equivalence (LIST_REL R)
Proof
    SRW_TAC [] [equivalence_def, reflexive_def, symmetric_def,
                transitive_def, LIST_REL_EL_EQN]
 >- (EQ_TAC >> SRW_TAC [][])
 >> Q.PAT_X_ASSUM `!x y z. R x y /\ R y z ==> R x z` MATCH_MP_TAC
 >> Q.EXISTS_TAC `EL n y`
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC
 >> ASM_REWRITE_TAC []
QED

(*---------------------------------------------------------------------------
     Congruence rules for higher-order functions. Used when making
     recursive definitions by so-called higher-order recursion.
 ---------------------------------------------------------------------------*)

val list_size_def =
  REWRITE_RULE [arithmeticTheory.ADD_ASSOC]
               (#2 (TypeBase.size_of “:'a list”));

val Induct = INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC;

Theorem list_size_cong[defncong]:
  !M N f f'.
    M=N /\ (!x. MEM x N ==> (f x = f' x))
          ==>
    list_size f M = list_size f' N
Proof
Induct
  THEN REWRITE_TAC [list_size_def, MEM]
  THEN REPEAT STRIP_TAC
  THEN PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM)
  THEN REWRITE_TAC [list_size_def]
  THEN MK_COMB_TAC THENL
  [NTAC 2 (MK_COMB_TAC THEN TRY REFL_TAC)
     THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [MEM],
   FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [] THEN GEN_TAC
     THEN PAT_X_ASSUM (Term‘!x. MEM x l ==> Q x’)
                    (MP_TAC o SPEC (Term‘x:'a’))
     THEN REWRITE_TAC [MEM] THEN REPEAT STRIP_TAC
     THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]
QED

Theorem list_size_append:
  !f xs ys. list_size f (xs ++ ys) = list_size f xs + list_size f ys
Proof
  GEN_TAC \\ Induct \\ FULL_SIMP_TAC arith_ss [APPEND, list_size_def]
QED

Theorem FOLDR_CONG[defncong]:
  !l l' b b' (f:'a->'b->'b) f'.
    l=l' /\ b=b' /\ (!x a. MEM x l' ==> (f x a = f' x a))
          ==>
    FOLDR f b l = FOLDR f' b' l'
Proof
Induct
  THEN REWRITE_TAC [FOLDR, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [FOLDR]
  THEN POP_ASSUM (fn th => MP_TAC (SPEC (Term‘h’) th) THEN ASSUME_TAC th)
  THEN REWRITE_TAC [MEM]
  THEN DISCH_TAC
  THEN MK_COMB_TAC
  THENL [CONV_TAC FUN_EQ_CONV THEN ASM_REWRITE_TAC [],
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
           THEN REPEAT STRIP_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]
QED

Theorem FOLDL_CONG[defncong]:
  !l l' b b' (f:'b->'a->'b) f'.
    l=l' /\ b=b' /\ (!x a. MEM x l' ==> (f a x = f' a x))
          ==>
    FOLDL f b l = FOLDL f' b' l'
Proof
Induct
  THEN REWRITE_TAC [FOLDL, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [FOLDL]
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN REWRITE_TAC[]
  THEN CONJ_TAC
  THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [MEM],
         REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]
QED


Theorem MAP_CONG[defncong]:
  !l1 l2 f f'.
    l1=l2 /\ (!x. MEM x l2 ==> (f x = f' x)) ==>
    MAP f l1 = MAP f' l2
Proof
Induct THEN REWRITE_TAC [MAP, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [MAP]
  THEN MK_COMB_TAC
  THENL [MK_COMB_TAC THEN TRY REFL_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN REWRITE_TAC [MEM],
         FIRST_ASSUM MATCH_MP_TAC
             THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC [MEM]]
QED

Theorem MAP2_CONG[defncong]:
  !l1 l1' l2 l2' f f'.
    l1=l1' /\ l2=l2' /\
    (!x y. MEM x l1' /\ MEM y l2' ==> (f x y = f' x y))
    ==>
    (MAP2 f l1 l2 = MAP2 f' l1' l2')
Proof
  Induct THEN SRW_TAC[] [MAP2_DEF, MEM] THEN
  SRW_TAC[] [MAP2_DEF] THEN
  Cases_on ‘l2’ THEN
  SRW_TAC[][MAP2_DEF]
QED

Theorem EXISTS_CONG[defncong]:
 !l1 l2 P P'.
    (l1=l2) /\ (!x. MEM x l2 ==> (P x = P' x))
          ==>
    (EXISTS P l1 = EXISTS P' l2)
Proof
Induct THEN REWRITE_TAC [EXISTS_DEF, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THENL [PAT_X_ASSUM (Term‘EXISTS x y’) MP_TAC THEN REWRITE_TAC [EXISTS_DEF],
         REWRITE_TAC [EXISTS_DEF]
           THEN MK_COMB_TAC
           THENL [MK_COMB_TAC THEN TRY REFL_TAC
                    THEN FIRST_ASSUM MATCH_MP_TAC
                    THEN REWRITE_TAC [MEM],
                  FIRST_ASSUM MATCH_MP_TAC
                    THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
                    THEN FIRST_ASSUM MATCH_MP_TAC
                    THEN ASM_REWRITE_TAC [MEM]]]
QED


Theorem EVERY_CONG[defncong]:
  !l1 l2 P P'.
    l1=l2 /\ (!x. MEM x l2 ==> (P x <=> P' x))
    ==>
    (EVERY P l1 <=> EVERY P' l2)
Proof
Induct THEN REWRITE_TAC [EVERY_DEF, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [EVERY_DEF]
  THEN MK_COMB_TAC
  THENL [MK_COMB_TAC THEN TRY REFL_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [MEM],
         FIRST_ASSUM MATCH_MP_TAC
           THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]
QED

val EVERY_MONOTONIC = store_thm(
  "EVERY_MONOTONIC",
  “!(P:'a -> bool) Q.
       (!x. P x ==> Q x) ==> !l. EVERY P l ==> EVERY Q l”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [EVERY_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC);

(* ----------------------------------------------------------------------
   ZIP and UNZIP functions (taken from rich_listTheory)
   ---------------------------------------------------------------------- *)
val ZIP_def =
    let val lemma = prove(
    (“?ZIP.
       (!l2. ZIP ([], l2) = []) /\
       (!l1. ZIP (l1, []) = []) /\
       (!(x1:'a) l1 (x2:'b) l2.
        ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))”),
    let val th = prove_rec_fn_exists list_Axiom
        (“(fn [] l = []) /\
         (fn (CONS (x:'a) l') (l:'b list) =
            if l = [] then [] else
              CONS (x, (HD l)) (fn  l' (TL l)))”)
        in
    STRIP_ASSUME_TAC th
    THEN EXISTS_TAC
           (“UNCURRY (fn:('a)list -> (('b)list -> ('a # 'b)list))”)
    THEN ASM_REWRITE_TAC[pairTheory.UNCURRY_DEF, HD, TL, NOT_CONS_NIL]
    THEN STRIP_TAC
    THEN STRIP_ASSUME_TAC (SPEC “l1:'a list” list_CASES)
    THEN ASM_REWRITE_TAC[]
     end)
    in
    Rsyntax.new_specification
        {consts = [{const_name = "ZIP", fixity = NONE}],
         name = "ZIP_def",
         sat_thm = lemma
        }
    end;

Theorem ZIP_ind:
  !P. (!l2. P ([], l2)) /\ (!l1. P(l1, [])) /\
      (!l1 l2 h1 h2. P (l1, l2) ==> P (h1::l1, h2::l2)) ==>
      !p. P p
Proof
  gen_tac >> strip_tac >> simp[pairTheory.FORALL_PROD] >> Induct >> simp[] >>
  gen_tac >> Cases >> simp[]
QED

val _ = DefnBase.register_indn(ZIP_ind, [{Thy = "list", Name = "ZIP"}])

val ZIP = store_thm("ZIP",
  “(ZIP ([],[]) = []) /\
    (!(x1:'a) l1 (x2:'b) l2.
       ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))”,
  REWRITE_TAC [ZIP_def]);

val UNZIP = new_recursive_definition {
  name = "UNZIP",   rec_axiom = list_Axiom,
  def  = “(UNZIP [] = ([], [])) /\
    (!x l. UNZIP (CONS (x:'a # 'b) l) =
               (CONS (FST x) (FST (UNZIP l)),
                CONS (SND x) (SND (UNZIP l))))”}

val UNZIP_THM = Q.store_thm
("UNZIP_THM",
 ‘(UNZIP [] = ([]:'a list,[]:'b list)) /\
  (UNZIP ((x:'a,y:'b)::t) = let (L1,L2) = UNZIP t in (x::L1, y::L2))’,
 RW_TAC bool_ss [UNZIP]
   THEN Cases_on ‘UNZIP t’
   THEN RW_TAC bool_ss [LET_THM, pairTheory.UNCURRY_DEF,
                        pairTheory.FST, pairTheory.SND]);

val UNZIP_MAP = Q.store_thm
("UNZIP_MAP",
 ‘!L. UNZIP L = (MAP FST L, MAP SND L)’,
 LIST_INDUCT_TAC THEN
 ASM_SIMP_TAC arith_ss [UNZIP, MAP,
    PAIR_EQ, pairTheory.FST, pairTheory.SND]);

val SUC_NOT = arithmeticTheory.SUC_NOT
val LENGTH_ZIP = store_thm("LENGTH_ZIP",
  “!(l1:'a list) (l2:'b list).
         (LENGTH l1 = LENGTH l2) ==>
         (LENGTH(ZIP(l1,l2)) = LENGTH l1) /\
         (LENGTH(ZIP(l1,l2)) = LENGTH l2)”,
  LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (“l2:'b list”)) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ZIP, LENGTH, NOT_SUC, SUC_NOT, INV_SUC_EQ] THEN
  DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

Theorem LENGTH_ZIP_MIN[simp]:
  !xs ys. LENGTH (ZIP (xs,ys)) = MIN (LENGTH xs) (LENGTH ys)
Proof
  Induct >> fs [LENGTH,ZIP_def] >> Cases_on ‘ys’ >> fs [LENGTH,ZIP_def] >>
  rw [arithmeticTheory.MIN_DEF]
QED

val LENGTH_UNZIP = store_thm(
  "LENGTH_UNZIP",
  “!pl. (LENGTH (FST (UNZIP pl)) = LENGTH pl) /\
         (LENGTH (SND (UNZIP pl)) = LENGTH pl)”,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [UNZIP, LENGTH]);

val ZIP_UNZIP = store_thm("ZIP_UNZIP",
    (“!l:('a # 'b)list. ZIP(UNZIP l) = l”),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP, ZIP]);

val UNZIP_ZIP = store_thm("UNZIP_ZIP",
    (“!l1:'a list. !l2:'b list.
     (LENGTH l1 = LENGTH l2) ==> (UNZIP(ZIP(l1,l2)) = (l1,l2))”),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (“l2:'b list”))
    THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[UNZIP, ZIP, LENGTH, NOT_SUC, SUC_NOT, INV_SUC_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);


val ZIP_MAP = store_thm(
  "ZIP_MAP",
  “!l1 l2 f1 f2.
       (LENGTH l1 = LENGTH l2) ==>
       (ZIP (MAP f1 l1, l2) = MAP (\p. (f1 (FST p), SND p)) (ZIP (l1, l2))) /\
       (ZIP (l1, MAP f2 l2) = MAP (\p. (FST p, f2 (SND p))) (ZIP (l1, l2)))”,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LENGTH] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL [
    Q.SUBGOAL_THEN ‘l2 = []’ SUBST_ALL_TAC THEN
    REWRITE_TAC [ZIP, MAP] THEN mesonLib.ASM_MESON_TAC [LENGTH_NIL],
    Q.SUBGOAL_THEN
       ‘?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)’
    STRIP_ASSUME_TAC THENL [
      mesonLib.ASM_MESON_TAC [LENGTH_CONS],
      ASM_SIMP_TAC bool_ss [ZIP, MAP, FST, SND]
    ]
  ]);

val MEM_ZIP = store_thm(
  "MEM_ZIP",
  “!(l1:'a list) (l2:'b list) p.
       (LENGTH l1 = LENGTH l2) ==>
       (MEM p (ZIP(l1, l2)) =
        ?n. n < LENGTH l1 /\ (p = (EL n l1, EL n l2)))”,
  LIST_INDUCT_TAC THEN SIMP_TAC bool_ss [LENGTH] THEN REPEAT STRIP_TAC THENL [
    ‘l2 = []’  by ASM_MESON_TAC [LENGTH_NIL] THEN
    FULL_SIMP_TAC arith_ss [ZIP, MEM, LENGTH],
    ‘?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)’
      by ASM_MESON_TAC [LENGTH_CONS] THEN
    FULL_SIMP_TAC arith_ss [MEM, ZIP, LENGTH] THEN EQ_TAC THEN
    STRIP_TAC THENL [
      Q.EXISTS_TAC ‘0’ THEN ASM_SIMP_TAC arith_ss [EL, HD],
      Q.EXISTS_TAC ‘SUC n’ THEN ASM_SIMP_TAC arith_ss [EL, TL],
      Cases_on ‘n’ THEN FULL_SIMP_TAC arith_ss [EL, HD, TL] THEN
      ASM_MESON_TAC []
    ]
  ]);

val EL_ZIP = store_thm(
  "EL_ZIP",
  “!(l1:'a list) (l2:'b list) n.
        (LENGTH l1 = LENGTH l2) /\ n < LENGTH l1 ==>
        (EL n (ZIP (l1, l2)) = (EL n l1, EL n l2))”,
  Induct THEN SIMP_TAC arith_ss [LENGTH] THEN REPEAT STRIP_TAC THEN
  ‘?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)’
     by ASM_MESON_TAC [LENGTH_CONS] THEN
  FULL_SIMP_TAC arith_ss [ZIP, LENGTH] THEN
  Cases_on ‘n’ THEN ASM_SIMP_TAC arith_ss [ZIP, EL, HD, TL]);


val MAP2_ZIP = store_thm("MAP2_ZIP",
    (“!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !f:'a->'b->'c. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))”),
    let val UNCURRY_DEF = pairTheory.UNCURRY_DEF
    in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (“l2:'b list”))
    THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[MAP, MAP2, ZIP, LENGTH, NOT_SUC, SUC_NOT]
    THEN ASM_REWRITE_TAC[CONS_11, UNCURRY_DEF, INV_SUC_EQ]
    end);

val MAP2_MAP = save_thm("MAP2_MAP",MAP2_ZIP)

val MAP_ZIP = Q.store_thm(
  "MAP_ZIP",
  ‘(LENGTH l1 = LENGTH l2) ==>
     (MAP FST (ZIP (l1,l2)) = l1) /\
     (MAP SND (ZIP (l1,l2)) = l2) /\
     (MAP (f o FST) (ZIP (l1,l2)) = MAP f l1) /\
     (MAP (g o SND) (ZIP (l1,l2)) = MAP g l2)’,
  Q.ID_SPEC_TAC ‘l2’ THEN Induct_on ‘l1’ THEN
  SRW_TAC [] [] THEN TRY(Cases_on ‘l2’) THEN
  FULL_SIMP_TAC (srw_ss()) [ZIP, MAP]);

val MEM_EL = store_thm(
  "MEM_EL",
  “!(l:'a list) x. MEM x l = ?n. n < LENGTH l /\ (x = EL n l)”,
  Induct THEN ASM_SIMP_TAC arith_ss [MEM, LENGTH] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC ‘0’ THEN ASM_SIMP_TAC arith_ss [EL, HD],
    Q.EXISTS_TAC ‘SUC n’ THEN ASM_SIMP_TAC arith_ss [EL, TL],
    Cases_on ‘n’ THEN FULL_SIMP_TAC arith_ss [EL, HD, TL] THEN
    ASM_MESON_TAC []
  ]);

val SUM_MAP_PLUS_ZIP = store_thm(
  "SUM_MAP_PLUS_ZIP",
  “!ls1 ls2.
     (LENGTH ls1 = LENGTH ls2) /\ (!x y. f (x,y) = g x + h y) ==>
     (SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2))”,
  Induct THEN Cases_on ‘ls2’ THEN
  SRW_TAC [numSimps.ARITH_ss] [MAP, ZIP, MAP_ZIP, SUM]);

Theorem LIST_REL_EVERY_ZIP:
  !R l1 l2.
    LIST_REL R l1 l2 <=>
    LENGTH l1 = LENGTH l2 /\ EVERY (UNCURRY R) (ZIP (l1,l2))
Proof
  GEN_TAC THEN Induct THEN SRW_TAC[] [LENGTH_NIL_SYM] THEN
  SRW_TAC [] [EQ_IMP_THM, LIST_REL_CONS1] THEN SRW_TAC [] [EVERY_DEF, ZIP] THEN
  Cases_on ‘l2’ THEN FULL_SIMP_TAC(srw_ss())[EVERY_DEF, ZIP]
QED

Theorem NOT_EVERY_EXISTS_FIRST :
    !P l. ~EVERY P l <=> ?i. i < LENGTH l /\ ~P (EL i l) /\ !j. j < i ==> P (EL j l)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC
 >- (rw [NOT_EVERY, EXISTS_MEM] \\
     Q.EXISTS_TAC ‘EL i l’ >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> rw [])
 >> rw [EVERY_EL, EXISTS_MEM, MEM_EL]
 >> Q.EXISTS_TAC ‘LEAST n. n < LENGTH l /\ ~P (EL n l)’
 >> numLib.LEAST_ELIM_TAC
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> rw [])
 >> Q.X_GEN_TAC ‘i’ >> rw []
 >> Q.PAT_X_ASSUM ‘!m. m < i ==> _’ (MP_TAC o (Q.SPEC ‘j’))
 >> ‘j < LENGTH l’ by RW_TAC arith_ss []
 >> RW_TAC bool_ss []
QED

Theorem EXISTS_FIRST :
    !P l. EXISTS P l <=> ?i. i < LENGTH l /\ P (EL i l) /\ !j. j < i ==> ~P (EL j l)
Proof
    rw [EXISTS_NOT_EVERY]
 >> MP_TAC (Q.SPEC ‘\x. ~P x’ NOT_EVERY_EXISTS_FIRST) >> rw []
QED

(* --------------------------------------------------------------------- *)
(* REVERSE                                                               *)
(* --------------------------------------------------------------------- *)

val REVERSE_DEF = new_recursive_definition {
  name = "REVERSE_DEF",
  rec_axiom = list_Axiom,
  def = “(REVERSE [] = []) /\
          (REVERSE (h::t) = (REVERSE t) ++ [h])”};
val _ = export_rewrites ["REVERSE_DEF"]

val REVERSE_APPEND = store_thm(
  "REVERSE_APPEND",
  “!l1 l2:'a list.
       REVERSE (l1 ++ l2) = (REVERSE l2) ++ (REVERSE l1)”,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, REVERSE_DEF, APPEND_NIL, APPEND_ASSOC]);

val REVERSE_REVERSE = store_thm(
  "REVERSE_REVERSE",
  “!l:'a list. REVERSE (REVERSE l) = l”,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE_DEF, REVERSE_APPEND, APPEND]);
val _ = export_rewrites ["REVERSE_REVERSE"]

val REVERSE_11 = store_thm(
  "REVERSE_11",
 “!l1 l2:'a list. (REVERSE l1 = REVERSE l2) <=> (l1 = l2)”,
 REPEAT GEN_TAC THEN EQ_TAC THEN1
   (DISCH_THEN (MP_TAC o AP_TERM “REVERSE : 'a list -> 'a list”) THEN
    REWRITE_TAC [REVERSE_REVERSE]) THEN
 STRIP_TAC THEN ASM_REWRITE_TAC []);
val _ = export_rewrites ["REVERSE_11"]

val MEM_REVERSE = store_thm(
  "MEM_REVERSE",
  “!l x. MEM x (REVERSE l) = MEM x l”,
  Induct THEN SRW_TAC [] [] THEN PROVE_TAC []);
val _ = export_rewrites ["MEM_REVERSE"]

val LENGTH_REVERSE = store_thm(
  "LENGTH_REVERSE",
  “!l. LENGTH (REVERSE l) = LENGTH l”,
  Induct THEN SRW_TAC [] [arithmeticTheory.ADD1]);
val _ = export_rewrites ["LENGTH_REVERSE"]

val REVERSE_EQ_NIL = store_thm(
  "REVERSE_EQ_NIL",
  “(REVERSE l = []) <=> (l = [])”,
  Cases_on ‘l’ THEN SRW_TAC [] []);
val _ = export_rewrites ["REVERSE_EQ_NIL"]

val REVERSE_EQ_SING = store_thm(
  "REVERSE_EQ_SING",
  “(REVERSE l = [e:'a]) <=> (l = [e])”,
  Cases_on ‘l’ THEN SRW_TAC [] [APPEND_EQ_SING, CONJ_COMM]);
val _ = export_rewrites ["REVERSE_EQ_SING"]

val FILTER_REVERSE = store_thm(
  "FILTER_REVERSE",
  “!l P. FILTER P (REVERSE l) = REVERSE (FILTER P l)”,
  Induct THEN
  ASM_SIMP_TAC bool_ss [FILTER, REVERSE_DEF, FILTER_APPEND_DISTRIB,
    COND_RAND, COND_RATOR, APPEND_NIL]);

(* ----------------------------------------------------------------------
    FRONT and LAST
   ---------------------------------------------------------------------- *)

val LAST_DEF = new_recursive_definition {
  name = "LAST_DEF",
  rec_axiom = list_Axiom,
  def = “LAST (h::t) = if t = [] then h else LAST t”};

val FRONT_DEF = new_recursive_definition {
  name = "FRONT_DEF",
  rec_axiom = list_Axiom,
  def = “FRONT (h::t) = if t = [] then [] else h :: FRONT t”};

val LAST_CONS = store_thm(
  "LAST_CONS",
  “(!x:'a. LAST [x] = x) /\
    (!(x:'a) y z. LAST (x::y::z) = LAST(y::z))”,
  REWRITE_TAC [LAST_DEF, NOT_CONS_NIL]);
val _ = export_rewrites ["LAST_CONS"]

val LAST_EL = store_thm(
"LAST_EL",
“!ls. (ls <> []) ==> (LAST ls = EL (PRE (LENGTH ls)) ls)”,
Induct THEN SRW_TAC[] [] THEN
Cases_on ‘ls’ THEN FULL_SIMP_TAC (srw_ss()) [])

Theorem LAST_MAP[simp]:
  !l f. l <> [] ==> (LAST (MAP f l) = f (LAST l))
Proof
  rpt strip_tac >> ‘?h t. l = h::t’ by METIS_TAC[list_CASES] >>
  srw_tac[][MAP] >> Q.ID_SPEC_TAC ‘h’ >> Induct_on ‘t’ >>
  asm_simp_tac (srw_ss()) []
QED

val FRONT_CONS = store_thm(
  "FRONT_CONS",
  “(!x:'a. FRONT [x] = []) /\
    (!x:'a y z. FRONT (x::y::z) = x :: FRONT (y::z))”,
  REWRITE_TAC [FRONT_DEF, NOT_CONS_NIL]);
val _ = export_rewrites ["FRONT_CONS"]

val LENGTH_FRONT_CONS = store_thm ("LENGTH_FRONT_CONS",
“!x xs. LENGTH (FRONT (x::xs)) = LENGTH xs”,
Induct_on ‘xs’ THEN ASM_SIMP_TAC bool_ss [FRONT_CONS, LENGTH])
val _ = export_rewrites ["LENGTH_FRONT_CONS"]

val FRONT_CONS_EQ_NIL = store_thm ("FRONT_CONS_EQ_NIL",
“(!x:'a xs. (FRONT (x::xs) = []) = (xs = [])) /\
  (!x:'a xs. ([] = FRONT (x::xs)) = (xs = [])) /\
  (!x:'a xs. NULL (FRONT (x::xs)) = NULL xs)”,
SIMP_TAC bool_ss [GSYM FORALL_AND_THM] THEN
Cases_on ‘xs’ THEN SIMP_TAC bool_ss [FRONT_CONS, NOT_NIL_CONS, NULL_DEF]);
val _ = export_rewrites ["FRONT_CONS_EQ_NIL"]

val APPEND_FRONT_LAST = store_thm(
  "APPEND_FRONT_LAST",
  “!l:'a list. ~(l = []) ==> (APPEND (FRONT l) [LAST l] = l)”,
  LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL] THEN
  POP_ASSUM MP_TAC THEN Q.SPEC_THEN ‘l’ STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC [NOT_CONS_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [FRONT_CONS, LAST_CONS, APPEND]);

val LAST_CONS_cond = store_thm(
  "LAST_CONS_cond",
  “LAST (h::t) = if t = [] then h else LAST t”,
  Cases_on ‘t’ THEN SRW_TAC [] []);

val LAST_APPEND_CONS = store_thm(
  "LAST_APPEND_CONS",
  “!h l1 l2. LAST (l1 ++ h::l2) = LAST (h::l2)”,
  Induct_on ‘l1’ THEN SRW_TAC [] [LAST_CONS_cond]);
val _ = export_rewrites ["LAST_APPEND_CONS"]


(* ----------------------------------------------------------------------
    TAKE and DROP
   ---------------------------------------------------------------------- *)

(* these are FIRSTN and BUTFIRSTN from rich_listTheory, but made total *)

Definition TAKE_def[nocompute]:
  (TAKE n [] = []) /\
  (TAKE n (x::xs) = if n = 0 then [] else x :: TAKE (n - 1) xs)
End

Definition DROP_def[nocompute]:
  (DROP n [] = []) /\
  (DROP n (x::xs) = if n = 0 then x::xs else DROP (n - 1) xs)
End

Theorem TAKE_nil[simp] = cj 1 TAKE_def

val TAKE_cons = store_thm(
  "TAKE_cons", “0 < n ==> (TAKE n (x::xs) = x::(TAKE (n-1) xs))”,
  SRW_TAC[][TAKE_def]);
val _ = export_rewrites ["TAKE_cons"];

Theorem DROP_nil[simp] = CONJUNCT1 DROP_def

val DROP_cons = store_thm(
  "DROP_cons",“0 < n ==> (DROP n (x::xs) = DROP (n-1) xs)”,
  SRW_TAC[][DROP_def]);
val _ = export_rewrites ["DROP_cons"];

val TAKE_0 = store_thm(
  "TAKE_0",
  “TAKE 0 l = []”,
  Cases_on ‘l’ THEN SRW_TAC [] [TAKE_def]);
val _  = export_rewrites ["TAKE_0"]

val TAKE_LENGTH_ID = store_thm(
  "TAKE_LENGTH_ID",
  “!l. TAKE (LENGTH l) l = l”,
  Induct_on ‘l’ THEN SRW_TAC [] []);
val _ = export_rewrites ["TAKE_LENGTH_ID"]

val LENGTH_TAKE = store_thm(
  "LENGTH_TAKE",
  “!n l. n <= LENGTH l ==> (LENGTH (TAKE n l) = n)”,
  Induct_on ‘l’ THEN SRW_TAC [numSimps.ARITH_ss] [TAKE_def]);
val _ = export_rewrites ["LENGTH_TAKE"]

Theorem TAKE_LENGTH_TOO_LONG:
  !l n. LENGTH l <= n ==> (TAKE n l = l)
Proof
  Induct THEN SRW_TAC [numSimps.ARITH_ss] []
QED

Theorem LENGTH_TAKE_EQ:
  LENGTH (TAKE n xs) = if n <= LENGTH xs then n else LENGTH xs
Proof
  SRW_TAC [] [] THEN fs [GSYM NOT_LESS] THEN AP_TERM_TAC
  THEN MATCH_MP_TAC TAKE_LENGTH_TOO_LONG THEN numLib.DECIDE_TAC
QED

Theorem EL_TAKE:
  !n x l. x < n ==> (EL x (TAKE n l) = EL x l)
Proof
  Induct_on ‘n’ >> ASM_SIMP_TAC (srw_ss()) [TAKE_def] >>
  Cases_on ‘x’ >> Cases_on ‘l’ >>
  ASM_SIMP_TAC (srw_ss()) [TAKE_def]
QED

(* |- !n l. 0 < n ==> HD (TAKE n l) = HD l *)
Theorem HD_TAKE = GEN_ALL (REWRITE_RULE [EL] (Q.SPECL [‘n’, ‘0’] EL_TAKE))

val MAP_TAKE = store_thm(
  "MAP_TAKE",
  “!f n l. MAP f (TAKE n l) = TAKE n (MAP f l)”,
  Induct_on‘l’ THEN SRW_TAC[][TAKE_def]);

val TAKE_APPEND1 = store_thm(
  "TAKE_APPEND1",
  “!n. n <= LENGTH l1 ==> (TAKE n (APPEND l1 l2) = TAKE n l1)”,
  Induct_on ‘l1’ THEN SRW_TAC [numSimps.ARITH_ss] [TAKE_def]);

val TAKE_APPEND2 = store_thm(
  "TAKE_APPEND2",
  “!n. LENGTH l1 < n ==> (TAKE n (l1 ++ l2) = l1 ++ TAKE (n - LENGTH l1) l2)”,
  Induct_on ‘l1’ THEN SRW_TAC [numSimps.ARITH_ss] [arithmeticTheory.ADD1]);

Theorem DROP_0[simp]:
  DROP 0 l = l
Proof
  Induct_on ‘l’ THEN SRW_TAC [] [DROP_def]
QED

Theorem DROP_LENGTH_NIL[simp]:
  !l. DROP (LENGTH l) l = []
Proof
  Induct >> simp[]
QED

Theorem DROP_APPEND1:
  !n l1. n <= LENGTH l1 ==> !l2. DROP n (l1 ++ l2) = DROP n l1 ++ l2
Proof
  Induct_on ‘l1’ >> simp[] >> Cases_on ‘n’ >> simp[]
QED

Theorem DROP_APPEND2:
  !l1 n. LENGTH l1 <= n ==> !l2. DROP n (l1 ++ l2) = DROP (n - LENGTH l1) l2
Proof
  Induct >> simp[] >> Cases_on ‘n’ >> simp[GSYM arithmeticTheory.ADD1]
QED

Theorem DROP_APPEND:
  !n l1 l2. DROP n (l1 ++ l2) = DROP n l1 ++ DROP (n - LENGTH l1) l2
Proof
  Induct_on ‘l1’ >> simp[] >> Cases_on ‘n’ >> simp[]
QED

val TAKE_DROP = store_thm(
  "TAKE_DROP",
  “!n l. TAKE n l ++ DROP n l = l”,
  Induct_on ‘l’ THEN SRW_TAC [numSimps.ARITH_ss] [TAKE_def]);
val _ = export_rewrites ["TAKE_DROP"]

Theorem TAKE1:
  !l. l <> [] ==> (TAKE 1 l = [EL 0 l])
Proof Induct_on ‘l’ >> srw_tac[][]
QED

Theorem TAKE1_DROP:
  !n l. n < LENGTH l ==> (TAKE 1 (DROP n l) = [EL n l])
Proof
  Induct_on ‘l’ >> rw[] >> Cases_on ‘n’ >> fs[EL_restricted]
QED

Theorem TAKE_EQ_NIL[simp]:
  (TAKE n l = []) <=> (n = 0) \/ (l = [])
Proof
  Q.ID_SPEC_TAC ‘l’ THEN Induct_on ‘n’ THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases THEN ASM_SIMP_TAC (srw_ss()) []
QED

Theorem TAKE_EQ_REWRITE :
    !l m n. m <= LENGTH l /\ n <= LENGTH l ==> (TAKE m l = TAKE n l <=> m = n)
Proof
    rpt STRIP_TAC
 >> rw [LIST_EQ_REWRITE]
 >> EQ_TAC >> rw []
QED

Theorem TAKE_TAKE_MIN:
  !m n. TAKE n (TAKE m l) = TAKE (MIN n m) l
Proof
  Induct_on‘l’ >> rw[] >>
  Cases_on‘m’ >> Cases_on‘n’ >>
  SRW_TAC[numSimps.ARITH_ss][arithmeticTheory.MIN_DEF, arithmeticTheory.ADD1] >>
  FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []
QED

Theorem FRONT_TAKE :
    !l n. 0 < n /\ n <= LENGTH l ==> (FRONT (TAKE n l) = TAKE (n - 1) l)
Proof
  Induct THEN SRW_TAC [numSimps.ARITH_ss][TAKE_def, DROP_def] >>
  `0 < n - 1 /\ n - 1 <= LENGTH l` by numLib.DECIDE_TAC THEN
  SRW_TAC [][FRONT_DEF] THENL [
    fs [],
    `(n - 1) - 1 = n - 2` by numLib.DECIDE_TAC THEN
    SRW_TAC [][]
  ]
QED

val LENGTH_DROP = store_thm(
  "LENGTH_DROP",
  “!n l. LENGTH (DROP n l) = LENGTH l - n”,
  Induct_on ‘l’ THEN SRW_TAC [numSimps.ARITH_ss] [DROP_def]);
val _ = export_rewrites ["LENGTH_DROP"]

Theorem DROP_LENGTH_TOO_LONG:
  !l n. LENGTH l <= n ==> (DROP n l = [])
Proof Induct THEN SRW_TAC [numSimps.ARITH_ss] []
QED

Theorem LT_SUC[local] = arithmeticTheory.LT_SUC

Theorem MEM_DROP:
  !x ls n. MEM x (DROP n ls) <=>
           ?m. m + n < LENGTH ls /\ x = EL (m + n) ls
Proof
  Induct_on ‘ls’ >> rw[DROP_def, LT_SUC] >> asm_simp_tac(srw_ss() ++ DNF_ss)[]
  >- simp[MEM_EL] >>
  Q.RENAME_TAC [‘n <> 0’] >> Cases_on ‘n’ >> fs[] >>
  asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss ++ CONJ_ss)
    [GSYM arithmeticTheory.ADD1, ADD_CLAUSES]
QED

Theorem DROP_EQ_NIL[simp]:
 !ls n. DROP n ls = [] <=> LENGTH ls <= n
Proof
 Induct THEN SRW_TAC[] [DROP_def] THEN numLib.DECIDE_TAC
QED

Theorem HD_DROP:
  !n l. n < LENGTH l ==> (HD (DROP n l) = EL n l)
Proof   Induct_on ‘l’ >> asm_simp_tac (srw_ss() ++ DNF_ss) [LT_SUC]
QED

Theorem EL_DROP:
  !m n l. m + n < LENGTH l ==> (EL m (DROP n l) = EL (m + n) l)
Proof
  Induct_on ‘l’ >> SIMP_TAC (srw_ss()) [] >> Cases_on ‘n’ >>
  FULL_SIMP_TAC (srw_ss()) [DROP_def, ADD_CLAUSES]
QED

Theorem MAP_DROP:
  !l i. MAP f (DROP i l) = DROP i (MAP f l)
Proof   Induct \\ simp[DROP_def] \\ rw[]
QED

Theorem MAP_FRONT:
  !ls. ls <> [] ==> (MAP f (FRONT ls) = FRONT (MAP f ls))
Proof  Induct \\ simp[] \\ Cases_on‘ls’\\fs[]
QED

(* More functions for operating on pairs of lists *)

Definition FOLDL2_def[simp]:
  (FOLDL2 f a (b::bs) (c::cs) = FOLDL2 f (f a b c) bs cs) /\
  (FOLDL2 f a bs cs = a)
End

Theorem FOLDL2_cong[defncong]:
  !l1 l1' l2 l2' a a' f f'.
    l1 = l1' /\ l2 = l2' /\ a = a' /\
    (!z b c. MEM b l1' /\ MEM c l2' ==> (f z b c = f' z b c)) ==>
    FOLDL2 f a l1 l2 = FOLDL2 f' a' l1' l2'
Proof
Induct THEN SIMP_TAC(srw_ss()) [FOLDL2_def] THEN
GEN_TAC THEN Cases THEN SRW_TAC[] [FOLDL2_def]
QED

Theorem FOLDL2_FOLDL:
  !l1 l2. LENGTH l1 = LENGTH l2 ==>
          !f a. FOLDL2 f a l1 l2 = FOLDL (\a. UNCURRY (f a)) a (ZIP (l1,l2))
Proof
  Induct THEN1 SRW_TAC[] [LENGTH_NIL_SYM, ZIP, FOLDL] THEN
  GEN_TAC THEN Cases THEN SRW_TAC [] [ZIP, FOLDL]
QED

Overload EVERY2[inferior] = “LIST_REL”

Theorem EVERY2_cong[defncong]:
  !l1 l1' l2 l2' P P'.
    l1 = l1' /\ l2 = l2' /\
    (!x y. MEM x l1' /\ MEM y l2' ==> (P x y = P' x y)) ==>
    (EVERY2 P l1 l2 <=> EVERY2 P' l1' l2')
Proof
  Induct THEN SIMP_TAC (srw_ss()) [] THEN
  GEN_TAC THEN Cases THEN SRW_TAC [] [] THEN
  METIS_TAC[]
QED

Theorem MAP_EQ_EVERY2:
  !f1 f2 l1 l2. (MAP f1 l1 = MAP f2 l2) <=>
                  (LENGTH l1 = LENGTH l2) /\
                  LIST_REL (\x y. f1 x = f2 y) l1 l2
Proof
NTAC 2 GEN_TAC THEN
Induct THEN SRW_TAC [] [LENGTH_NIL_SYM, MAP] THEN
Cases_on ‘l2’ THEN SRW_TAC [] [MAP] THEN
PROVE_TAC[]
QED

Theorem EVERY2_EVERY:
  !l1 l2 f. EVERY2 f l1 l2 <=>
            LENGTH l1 = LENGTH l2 /\ EVERY (UNCURRY f) (ZIP (l1,l2))
Proof
Induct THEN1 SRW_TAC [] [LENGTH_NIL_SYM, EQ_IMP_THM, ZIP] THEN
GEN_TAC THEN Cases THEN SRW_TAC [] [ZIP, EQ_IMP_THM]
QED

val EVERY2_LENGTH = store_thm(
"EVERY2_LENGTH",
“!P l1 l2. EVERY2 P l1 l2 ==> (LENGTH l1 = LENGTH l2)”,
PROVE_TAC[EVERY2_EVERY])

Theorem EVERY2_mono = LIST_REL_mono

(* ----------------------------------------------------------------------
    ALL_DISTINCT
   ---------------------------------------------------------------------- *)

val ALL_DISTINCT = new_recursive_definition {
  def = Term‘(ALL_DISTINCT [] <=> T) /\
             (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t)’,
  name = "ALL_DISTINCT",
  rec_axiom = list_Axiom};
val _ = export_rewrites ["ALL_DISTINCT"]

val lemma = prove(
  “!l x. (FILTER ((=) x) l = []) = ~MEM x l”,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (bool_ss ++ COND_elim_ss)
               [FILTER, MEM, NOT_CONS_NIL, EQ_IMP_THM,
                LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]);

val ALL_DISTINCT_FILTER = store_thm(
  "ALL_DISTINCT_FILTER",
  “!l. ALL_DISTINCT l = !x. MEM x l ==> (FILTER ((=) x) l = [x])”,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (bool_ss ++ COND_elim_ss)
               [ALL_DISTINCT, MEM, FILTER, DISJ_IMP_THM,
                FORALL_AND_THM, CONS_11, EQ_IMP_THM, lemma] THEN
  metisLib.METIS_TAC []);

val FILTER_ALL_DISTINCT = store_thm (
  "FILTER_ALL_DISTINCT",
  “!P l. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)”,
  Induct_on ‘l’ THEN SRW_TAC [] [MEM_FILTER]);

val ALL_DISTINCT_MAP = store_thm(
"ALL_DISTINCT_MAP",
“!f ls. ALL_DISTINCT (MAP f ls) ==> ALL_DISTINCT ls”,
GEN_TAC THEN Induct THEN SRW_TAC[][ALL_DISTINCT, MAP, MEM_MAP] THEN PROVE_TAC[])

val EL_ALL_DISTINCT_EL_EQ = store_thm (
   "EL_ALL_DISTINCT_EL_EQ",
   “!l. ALL_DISTINCT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
                 ((EL n1 l = EL n2 l) = (n1 = n2)))”,
  Induct THEN SRW_TAC [] [] THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN Cases_on ‘n1’ THEN Cases_on ‘n2’ THEN
    SRW_TAC [numSimps.ARITH_ss] [] THEN PROVE_TAC [MEM_EL, LESS_MONO_EQ],

    REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [‘0’, ‘SUC n’] MP_TAC) THEN
      SRW_TAC [] [],

      FIRST_X_ASSUM (Q.SPECL_THEN [‘SUC n1’, ‘SUC n2’] MP_TAC) THEN
      SRW_TAC [] []
    ]
  ]);

val ALL_DISTINCT_EL_IMP = store_thm (
   "ALL_DISTINCT_EL_IMP",
   “!l n1 n2. ALL_DISTINCT l /\ n1 < LENGTH l /\ n2 < LENGTH l ==>
               ((EL n1 l = EL n2 l) = (n1 = n2))”,
   PROVE_TAC[EL_ALL_DISTINCT_EL_EQ]);


val ALL_DISTINCT_APPEND = store_thm (
   "ALL_DISTINCT_APPEND",
   “!l1 l2. ALL_DISTINCT (l1++l2) =
             (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
             (!e. MEM e l1 ==> ~(MEM e l2)))”,
  Induct THEN SRW_TAC [] [] THEN PROVE_TAC []);

val ALL_DISTINCT_SING = store_thm(
   "ALL_DISTINCT_SING",
   “!x. ALL_DISTINCT [x]”,
   SRW_TAC [] []);

Theorem ALL_DISTINCT_ZIP:
   !l1 l2. ALL_DISTINCT l1 /\ (LENGTH l1 = LENGTH l2) ==>
            ALL_DISTINCT (ZIP (l1,l2))
Proof
  Induct THEN Cases_on `l2` THEN SRW_TAC [] [ZIP] THEN
  FULL_SIMP_TAC (srw_ss()) [MEM_EL, MEM_ZIP]
QED

val ALL_DISTINCT_ZIP_SWAP = store_thm(
   "ALL_DISTINCT_ZIP_SWAP",
   “!l1 l2. ALL_DISTINCT (ZIP (l1,l2)) /\ (LENGTH l1 = LENGTH l2) ==>
            ALL_DISTINCT (ZIP (l2,l1))”,
   SRW_TAC [] [EL_ALL_DISTINCT_EL_EQ] THEN
   Q.PAT_X_ASSUM ‘X = Y’ (ASSUME_TAC o SYM) THEN
   FULL_SIMP_TAC (srw_ss()) [EL_ZIP, LENGTH_ZIP] THEN
   METIS_TAC [])

val ALL_DISTINCT_REVERSE = store_thm (
   "ALL_DISTINCT_REVERSE[simp]",
   “!l. ALL_DISTINCT (REVERSE l) = ALL_DISTINCT l”,
   SIMP_TAC bool_ss [ALL_DISTINCT_FILTER, MEM_REVERSE, FILTER_REVERSE] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      RES_TAC THEN
      ‘(FILTER ($= x) l) = REVERSE [x]’ by METIS_TAC[REVERSE_REVERSE] THEN
      FULL_SIMP_TAC bool_ss [REVERSE_DEF, APPEND],
      ASM_SIMP_TAC bool_ss [REVERSE_DEF, APPEND]
   ]);

val ALL_DISTINCT_FLAT_REVERSE = store_thm("ALL_DISTINCT_FLAT_REVERSE[simp]",
  “!xs. ALL_DISTINCT (FLAT (REVERSE xs)) = ALL_DISTINCT (FLAT xs)”,
  Induct \\ FULL_SIMP_TAC(srw_ss())[ALL_DISTINCT_APPEND]
  \\ FULL_SIMP_TAC(srw_ss())[MEM_FLAT,PULL_EXISTS] \\ METIS_TAC []);

Theorem ALL_DISTINCT_INDEX_OF_EL:
  !l n.
    (ALL_DISTINCT l /\ n < LENGTH l) ==>
    INDEX_OF (EL n l) l = SOME n
Proof
  Induct
  \\ rw[INDEX_OF_def]
  \\ rw[INDEX_FIND_def]
  >- (
    Cases_on`n` \\ fs[]
    \\ metis_tac[MEM_EL] )
  \\ rw[Once INDEX_FIND_add, PULL_EXISTS]
  \\ fs[INDEX_OF_def]
  \\ Cases_on`n` \\ fs[]
  \\ first_x_assum drule
  \\ rw[]
  \\ rw[UNCURRY, arithmeticTheory.ADD1]
QED

(* ----------------------------------------------------------------------
    LRC
      Where NRC has the number of steps in a transitive path,
      LRC has a list of the elements in the path (excluding the rightmost)
   ---------------------------------------------------------------------- *)

Definition LRC_def:
  (LRC R [] x y <=> (x = y)) /\
  (LRC R (h::t) x y <=>
     x = h /\ ?z. R x z /\ LRC R t z y)
End

val NRC_LRC = Q.store_thm(
"NRC_LRC",
‘NRC R n x y <=> ?ls. LRC R ls x y /\ (LENGTH ls = n)’,
MAP_EVERY Q.ID_SPEC_TAC [‘y’,‘x’] THEN
Induct_on ‘n’ THEN SRW_TAC [] [] THEN1 (
  SRW_TAC [] [EQ_IMP_THM] THEN1 (
    SRW_TAC [] [LRC_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [LRC_def]
) THEN
SRW_TAC [] [arithmeticTheory.NRC, EQ_IMP_THM] THEN1 (
  Q.EXISTS_TAC ‘x::ls’ THEN
  SRW_TAC [] [LRC_def] THEN
  METIS_TAC [] ) THEN
Cases_on ‘ls’ THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
SRW_TAC [] [] THEN METIS_TAC []);

val LRC_MEM = Q.store_thm(
"LRC_MEM",
‘LRC R ls x y /\ MEM e ls ==> ?z t. R e z /\ LRC R t z y’,
Q_TAC SUFF_TAC
‘!ls x y. LRC R ls x y ==> !e. MEM e ls ==> ?z t. R e z /\ LRC R t z y’
THEN1 METIS_TAC [] THEN
Induct THEN SRW_TAC [] [LRC_def] THEN METIS_TAC []);

Theorem LRC_MEM_right:
  LRC R (h::t) x y /\ MEM e t ==> ?z p. R z e /\ LRC R p x z
Proof
  Q_TAC SUFF_TAC
        ‘!ls x y. LRC R ls x y ==>
                  !h t e. (ls = h::t) /\ MEM e t ==> ?z p. R z e /\ LRC R p x z’
  THEN1 METIS_TAC [] THEN
  Induct THEN SRW_TAC [] [LRC_def] THEN
  Cases_on ‘ls’ THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
  SRW_TAC [] [] THENL [
    MAP_EVERY Q.EXISTS_TAC [‘h’,‘[]’] THEN SRW_TAC [] [LRC_def],
    RES_TAC THEN
    MAP_EVERY Q.EXISTS_TAC  [‘z''’,‘h::p’] THEN
    SRW_TAC [] [LRC_def] THEN
    METIS_TAC []
  ]
QED

(* ----------------------------------------------------------------------
    Theorems relating (finite) sets and lists.  First

       LIST_TO_SET : 'a list -> 'a set

    which is overloaded to "set".
   ---------------------------------------------------------------------- *)

val LIST_TO_SET_APPEND = Q.store_thm
("LIST_TO_SET_APPEND",
 ‘!l1 l2. set (l1 ++ l2) = set l1 UNION set l2’,
 Induct THEN SRW_TAC [] [INSERT_UNION_EQ]);
val _ = export_rewrites ["LIST_TO_SET_APPEND"]

val UNION_APPEND = save_thm ("UNION_APPEND", GSYM LIST_TO_SET_APPEND)

val LIST_TO_SET_EQ_EMPTY = store_thm(
  "LIST_TO_SET_EQ_EMPTY",
  “((set l = {}) <=> (l = [])) /\ (({} = set l) <=> (l = []))”,
  Cases_on ‘l’ THEN SRW_TAC [] []);
val _ = export_rewrites ["LIST_TO_SET_EQ_EMPTY"]

val FINITE_LIST_TO_SET = Q.store_thm
("FINITE_LIST_TO_SET",
 ‘!l. FINITE (set l)’,
 Induct THEN SRW_TAC [] []);
val _ = export_rewrites ["FINITE_LIST_TO_SET"]

val SUM_IMAGE_LIST_TO_SET_upper_bound = store_thm(
  "SUM_IMAGE_LIST_TO_SET_upper_bound",
  “!ls. SIGMA f (set ls) <= SUM (MAP f ls)”,
  Induct THEN
  SRW_TAC [] [MAP, SUM, SUM_IMAGE_THM, SUM_IMAGE_DELETE] THEN
  numLib.DECIDE_TAC);

val SUM_MAP_MEM_bound = store_thm(
"SUM_MAP_MEM_bound",
“!f x ls. MEM x ls ==> f x <= SUM (MAP f ls)”,
NTAC 2 GEN_TAC THEN Induct THEN SRW_TAC[] [] THEN
FULL_SIMP_TAC(srw_ss()++numSimps.ARITH_ss)[MEM, MAP, SUM])

Theorem INJ_MAP_EQ:
  !f l1 l2. INJ f (set l1 UNION set l2) UNIV /\ MAP f l1 = MAP f l2 ==>
            l1 = l2
Proof
  GEN_TAC THEN Induct THEN1 SRW_TAC[] [MAP] THEN
  GEN_TAC THEN Cases THEN SRW_TAC[] [MAP]
  THEN1 (IMP_RES_TAC INJ_DEF THEN
         FIRST_X_ASSUM (MATCH_MP_TAC o MP_CANON) THEN
         SRW_TAC [] []) THEN
  PROVE_TAC[INJ_SUBSET, SUBSET_REFL, SUBSET_DEF, IN_UNION, IN_INSERT]
QED

(* this turns out to be more useful; in particular, INJ_MAP_EQ can't
   be used as an introduction rule without explicit instantiation of
   its beta type variable, which only appears in the assumption *)
val INJ_MAP_EQ_IFF = store_thm(
  "INJ_MAP_EQ_IFF",
  “!f l1 l2.
      INJ f (set l1 UNION set l2) UNIV ==>
      ((MAP f l1 = MAP f l2) <=> (l1 = l2))”,
  rw[] >> EQ_TAC >- metis_tac[INJ_MAP_EQ] >> rw[])

local open numLib in
val CARD_LIST_TO_SET = Q.store_thm(
"CARD_LIST_TO_SET",
‘CARD (set ls) <= LENGTH ls’,
Induct_on ‘ls’ THEN SRW_TAC [] [] THEN
DECIDE_TAC);
end

val ALL_DISTINCT_CARD_LIST_TO_SET = Q.store_thm(
"ALL_DISTINCT_CARD_LIST_TO_SET",
‘!ls. ALL_DISTINCT ls ==> (CARD (set ls) = LENGTH ls)’,
Induct THEN SRW_TAC [] []);

val th1 = MATCH_MP arithmeticTheory.LESS_EQ_IMP_LESS_SUC CARD_LIST_TO_SET ;
val th2 = MATCH_MP prim_recTheory.LESS_NOT_EQ th1 ;

val CARD_LIST_TO_SET_ALL_DISTINCT = Q.store_thm(
"CARD_LIST_TO_SET_ALL_DISTINCT",
‘!ls. (CARD (set ls) = LENGTH ls) ==> ALL_DISTINCT ls’,
Induct THEN SRW_TAC [] [th2]);

val LIST_TO_SET_REVERSE = store_thm(
  "LIST_TO_SET_REVERSE",
  “!ls: 'a list. set (REVERSE ls) = set ls”,
  Induct THEN SRW_TAC [] [pred_setTheory.EXTENSION]);
val _ = export_rewrites ["LIST_TO_SET_REVERSE"]

val LIST_TO_SET_THM = save_thm("LIST_TO_SET_THM", LIST_TO_SET)
val LIST_TO_SET_MAP = store_thm ("LIST_TO_SET_MAP",
“!f l. LIST_TO_SET (MAP f l) = IMAGE f (LIST_TO_SET l)”,
Induct_on ‘l’ THEN
ASM_SIMP_TAC bool_ss [pred_setTheory.IMAGE_EMPTY, pred_setTheory.IMAGE_INSERT,
   MAP, LIST_TO_SET_THM]);

val LIST_TO_SET_FILTER = store_thm(
  "LIST_TO_SET_FILTER",
  “LIST_TO_SET (FILTER P l) = { x | P x } INTER LIST_TO_SET l”,
  SRW_TAC [] [pred_setTheory.EXTENSION, MEM_FILTER]);


(* ----------------------------------------------------------------------
    SET_TO_LIST : 'a set -> 'a list

    Only defined if the set is finite; order of elements in list is
    unspecified.
   ---------------------------------------------------------------------- *)

val SET_TO_LIST_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "SET_TO_LIST"
  ‘SET_TO_LIST s =
     if FINITE s then
        if s={} then []
        else CHOICE s :: SET_TO_LIST (REST s)
     else ARB’;

(*---------------------------------------------------------------------------
       Termination of SET_TO_LIST.
 ---------------------------------------------------------------------------*)

val (SET_TO_LIST_EQN, SET_TO_LIST_IND) =
 Defn.tprove (SET_TO_LIST_defn,
   TotalDefn.WF_REL_TAC ‘measure CARD’ THEN
   PROVE_TAC [CARD_PSUBSET, REST_PSUBSET]);

(*---------------------------------------------------------------------------
      Desired recursion equation.

      FINITE s |- SET_TO_LIST s = if s = {} then []
                               else CHOICE s::SET_TO_LIST (REST s)

 ---------------------------------------------------------------------------*)

val SET_TO_LIST_THM = save_thm("SET_TO_LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME “FINITE s”] SET_TO_LIST_EQN));

val SET_TO_LIST_IND = save_thm("SET_TO_LIST_IND", SET_TO_LIST_IND);



(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_EMPTY = store_thm(
  "SET_TO_LIST_EMPTY",
  “SET_TO_LIST {} = []”,
  SRW_TAC [] [SET_TO_LIST_THM])
val _ = export_rewrites ["SET_TO_LIST_EMPTY"]

Theorem SET_TO_LIST_EMPTY_IFF:
  !s. FINITE s ==>
  (SET_TO_LIST s = [] <=> s = {})
Proof
  ho_match_mp_tac FINITE_INDUCT \\ rw[SET_TO_LIST_THM]
QED

val SET_TO_LIST_INV = Q.store_thm("SET_TO_LIST_INV",
‘!s. FINITE s ==> (LIST_TO_SET(SET_TO_LIST s) = s)’,
 Induction.recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [LIST_TO_SET_THM]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, CHOICE_INSERT_REST]);

val SET_TO_LIST_CARD = Q.store_thm("SET_TO_LIST_CARD",
‘!s. FINITE s ==> (LENGTH (SET_TO_LIST s) = CARD s)’,
 Induction.recInduct SET_TO_LIST_IND
   THEN REPEAT STRIP_TAC
   THEN SRW_TAC [] [Once (UNDISCH SET_TO_LIST_THM)]
   THEN ‘FINITE (REST s)’ by METIS_TAC [REST_DEF, FINITE_DELETE]
   THEN ‘~(CARD s = 0)’ by METIS_TAC [CARD_EQ_0]
   THEN SRW_TAC [numSimps.ARITH_ss] [REST_DEF, CHOICE_DEF]);

Theorem SET_TO_LIST_IN_MEM:
  !s. FINITE s ==> !x. x IN s <=> MEM x (SET_TO_LIST s)
Proof
 Induction.recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [MEM, NOT_IN_EMPTY]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, IN_INSERT, CHOICE_INSERT_REST]
QED

(* this version of the above is a more likely rewrite: a complicated LHS
   turns into a simple RHS *)
Theorem MEM_SET_TO_LIST[simp]:
  !s. FINITE s ==> !x. MEM x (SET_TO_LIST s) <=> x IN s
Proof METIS_TAC [SET_TO_LIST_IN_MEM]
QED

val SET_TO_LIST_SING = store_thm(
  "SET_TO_LIST_SING",
  “SET_TO_LIST {x} = [x]”,
  SRW_TAC [] [SET_TO_LIST_THM]);
val _ = export_rewrites ["SET_TO_LIST_SING"]

Theorem LIST_TO_SET_TAKE:
  !i l. set (TAKE i l) SUBSET set l
Proof
  simp[SUBSET_DEF] >> Induct_on ‘l’ >> simp[] >>
  Cases_on ‘i’ >> simp[DISJ_IMP_THM] >> metis_tac[]
QED

Theorem LIST_TO_SET_DROP:
  !i l. set (DROP i l) SUBSET set l
Proof
  simp[SUBSET_DEF] >> Induct_on ‘l’ >> simp[] >>
  Cases_on ‘i’ >> simp[DISJ_IMP_THM] >> metis_tac[]
QED

val op >>~- = Q.>>~-
val op >~ = Q.>~


val ALL_DISTINCT_SET_TO_LIST = store_thm("ALL_DISTINCT_SET_TO_LIST",
  “!s. FINITE s ==> ALL_DISTINCT (SET_TO_LIST s)”,
  Induction.recInduct SET_TO_LIST_IND THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SET_TO_LIST_THM THEN
  ‘FINITE (REST s)’ by PROVE_TAC[pred_setTheory.FINITE_DELETE,
                                 pred_setTheory.REST_DEF] THEN
  Cases_on ‘s = EMPTY’ THEN
  FULL_SIMP_TAC bool_ss [ALL_DISTINCT, MEM_SET_TO_LIST,
                         pred_setTheory.CHOICE_NOT_IN_REST]);
val _ = export_rewrites ["ALL_DISTINCT_SET_TO_LIST"];

val ITSET_eq_FOLDL_SET_TO_LIST = Q.store_thm(
"ITSET_eq_FOLDL_SET_TO_LIST",
‘!s. FINITE s ==> !f a. ITSET f s a = FOLDL (combin$C f) a (SET_TO_LIST s)’,
HO_MATCH_MP_TAC pred_setTheory.FINITE_COMPLETE_INDUCTION THEN
SRW_TAC [] [pred_setTheory.ITSET_THM, SET_TO_LIST_THM, FOLDL]);

Theorem LIST_TO_SET_SING :
    !vs x. ALL_DISTINCT vs /\ set vs = {x} <=> vs = [x]
Proof
    rpt GEN_TAC >> reverse EQ_TAC >- rw []
 (* necessary case analysis, to use ALL_DISTINCT *)
 >> Cases_on ‘vs’ >> rw []
 >- (fs [Once EXTENSION] >> METIS_TAC [])
 >> Q_TAC KNOW_TAC ‘a = x’
 >- (fs [Once EXTENSION] >> METIS_TAC [])
 >> DISCH_THEN (fn th => fs [th])
 >> Cases_on ‘set l = {}’ >- fs []
 >> ‘?y. y IN set l’ by METIS_TAC [MEMBER_NOT_EMPTY]
 >> Cases_on ‘x = y’ >- PROVE_TAC []
 >> fs [Once EXTENSION]
 >> METIS_TAC []
QED

(* ----------------------------------------------------------------------
    FINITE set of lists
   ---------------------------------------------------------------------- *)

Theorem bounded_length_FINITE:
  FINITE (UNIV:'a set) ==>
  !m (s:'a list set). (!x. x IN s ==> LENGTH x <= m) ==> FINITE s
Proof
  strip_tac
  \\ ho_match_mp_tac numTheory.INDUCTION
  \\ rw[]
  >- (
    Cases_on`s` \\ fs[]
    \\ `x = []` by metis_tac[] \\ rw[]
    \\ Cases_on`t` \\ fs[] \\ metis_tac[] )
  \\ `s SUBSET
      [] INSERT BIGUNION (IMAGE (\f. IMAGE (f o TL) s) (IMAGE CONS UNIV))`
    by (rw[SUBSET_DEF, PULL_EXISTS]
        \\ res_tac
        \\ Cases_on`x` \\ fs[]
        \\ Q.EXISTS_TAC`a::l` \\ simp[] )
  \\ match_mp_tac (MP_CANON SUBSET_FINITE)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rewrite_tac[FINITE_INSERT]
  \\ match_mp_tac FINITE_BIGUNION
  \\ simp[PULL_EXISTS]
  \\ simp[IMAGE_COMPOSE]
  \\ first_x_assum match_mp_tac
  \\ Q.X_GEN_TAC`z`
  \\ rw[PULL_EXISTS]
  \\ res_tac
  \\ Cases_on`x` \\ fs[]
QED

(* ----------------------------------------------------------------------
    isPREFIX
   ---------------------------------------------------------------------- *)

Definition isPREFIX[simp]:
  (isPREFIX [] l = T) /\
  (isPREFIX (h::t) l = case l of [] => F
                               | h'::t' => (h = h') /\ isPREFIX t t')
End

Overload "<<=" = “isPREFIX”

(* type annotations are there solely to make theorem have only one
   type variable; without them the theorem ends up with three (because the
   three clauses are independent). *)
val isPREFIX_THM = store_thm(
  "isPREFIX_THM",
  “(([]:'a list) <<= l <=> T) /\
    ((h::t:'a list) <<= [] <=> F) /\
    ((h1::t1:'a list) <<= h2::t2 <=> (h1 = h2) /\ isPREFIX t1 t2)”,
  SRW_TAC [] [])
val _ = export_rewrites ["isPREFIX_THM"]

val isPREFIX_NILR = Q.store_thm(
  "isPREFIX_NILR[simp]",
  ‘x <<= [] <=> (x = [])’,
  Cases_on ‘x’ >> simp[]);

val isPREFIX_CONSR = Q.store_thm(
  "isPREFIX_CONSR",
  ‘x <<= y::ys <=> (x = []) \/ ?xs. (x = y::xs) /\ xs <<= ys’,
  Cases_on ‘x’ >> simp[]);

(* ----------------------------------------------------------------------
    SNOC
   ---------------------------------------------------------------------- *)

(* use new_recursive_definition to get quantification and variable names
   exactly as they were in rich_listTheory *)
val SNOC = new_recursive_definition {
  def = “(!x:'a. SNOC x [] = [x]) /\
          (!x:'a x' l. SNOC x (CONS x' l) = CONS x' (SNOC x l))”,
  name = "SNOC",
  rec_axiom = list_Axiom
};
val _ = BasicProvers.export_rewrites ["SNOC"]

val SNOC_NIL = save_thm("SNOC_NIL", SNOC |> CONJUNCT1);
(* > val SNOC_NIL = |- !x. SNOC x [] = [x]: thm *)
val SNOC_CONS = save_thm("SNOC_CONS", SNOC |> CONJUNCT2);
(* > val SNOC_CONS = |- !x x' l. SNOC x (x'::l) = x'::SNOC x l: thm *)

val LENGTH_SNOC = store_thm(
  "LENGTH_SNOC",
  “!(x:'a) l. LENGTH (SNOC x l) = SUC (LENGTH l)”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, SNOC]);
val _ = export_rewrites ["LENGTH_SNOC"]

val LAST_SNOC = store_thm(
  "LAST_SNOC",
  “!x:'a l. LAST (SNOC x l) = x”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW_TAC bool_ss [SNOC, LAST_DEF] THEN
  POP_ASSUM MP_TAC THEN
  Q.SPEC_THEN ‘l’  STRUCT_CASES_TAC list_CASES THEN
  RW_TAC bool_ss [SNOC]);
val _ = export_rewrites ["LAST_SNOC"]

val FRONT_SNOC = store_thm(
  "FRONT_SNOC",
  “!x:'a l. FRONT (SNOC x l) = l”,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW_TAC bool_ss [SNOC, FRONT_DEF] THEN
  POP_ASSUM MP_TAC THEN
  Q.SPEC_THEN ‘l’ STRUCT_CASES_TAC list_CASES THEN
  RW_TAC bool_ss [SNOC]);
val _ = export_rewrites ["FRONT_SNOC"]

val SNOC_APPEND = store_thm("SNOC_APPEND",
   “!x (l:('a) list). SNOC x l = APPEND l [x]”,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC, APPEND]);

(* |- !l. l <> [] ==> SNOC (LAST l) (FRONT l) = l *)
Theorem SNOC_LAST_FRONT =
     REWRITE_RULE [GSYM SNOC_APPEND] APPEND_FRONT_LAST

val LIST_TO_SET_SNOC = Q.store_thm("LIST_TO_SET_SNOC",
    ‘set (SNOC x ls) = x INSERT set ls’,
    Induct_on ‘ls’ THEN SRW_TAC [] [INSERT_COMM]);

val MAP_SNOC  = store_thm("MAP_SNOC",
    (“!(f:'a->'b) x (l:'a list). MAP f(SNOC x l) = SNOC(f x)(MAP f l)”),
     (REWRITE_TAC [SNOC_APPEND, MAP_APPEND, MAP]));

val EL_SNOC = store_thm("EL_SNOC",
    (“!n (l:'a list). n < (LENGTH l) ==> (!x. EL n (SNOC x l) = EL n l)”),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH, NOT_LESS_0]
    THENL[
        REWRITE_TAC[SNOC, EL, HD],
        REWRITE_TAC[SNOC, EL, TL, LESS_MONO_EQ]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val EL_LENGTH_SNOC = store_thm("EL_LENGTH_SNOC",
    (“!l:'a list. !x. EL (LENGTH l) (SNOC x l) = x”),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EL, SNOC, HD, TL, LENGTH]);

val APPEND_SNOC = store_thm("APPEND_SNOC",
    (“!l1 (x:'a) l2. APPEND l1 (SNOC x l2) = SNOC x (APPEND l1 l2)”),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND, SNOC]);

Theorem EVERY_SNOC:
  !P (x:'a) l. EVERY P (SNOC x l) <=> EVERY P l /\ P x
Proof
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC, EVERY_DEF, CONJ_ASSOC]
QED

Theorem EXISTS_SNOC:
  !P (x:'a) l. EXISTS P (SNOC x l) <=> P x \/ (EXISTS P l)
Proof
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC, EXISTS_DEF] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC
QED

Theorem MEM_SNOC[simp]:
  !(y:'a) x l. MEM y (SNOC x l) <=> (y = x) \/ MEM y l
Proof
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC, MEM] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC
QED

val SNOC_11 = store_thm(
  "SNOC_11",
  “!x y a b. (SNOC x y = SNOC a b) <=> (x = a) /\ (y = b)”,
  SRW_TAC [] [EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o Q.AP_TERM ‘LAST’) THEN SRW_TAC [] [LAST_SNOC],
    POP_ASSUM (MP_TAC o Q.AP_TERM ‘FRONT’) THEN SRW_TAC [] [FRONT_SNOC]
  ]);
val _ = export_rewrites ["SNOC_11"]

val REVERSE_SNOC_DEF = store_thm (
  "REVERSE_SNOC_DEF",
    “(REVERSE [] = []) /\
        (!x:'a l. REVERSE (x::l) = SNOC x (REVERSE l))”,
          REWRITE_TAC [REVERSE_DEF, SNOC_APPEND]);

val REVERSE_SNOC = store_thm(
  "REVERSE_SNOC",
    “!(x:'a) l. REVERSE (SNOC x l) = CONS x (REVERSE l)”,
      GEN_TAC THEN LIST_INDUCT_TAC
      THEN ASM_REWRITE_TAC[SNOC, REVERSE_SNOC_DEF]);

val forall_REVERSE = TAC_PROOF(([],
    (“!P. (!l:('a)list. P(REVERSE l)) = (!l. P l)”)),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC (“REVERSE l:('a)list”)))));

val f_REVERSE_lemma = TAC_PROOF (([],
    (“!f1 f2.
    ((\x. (f1:('a)list->'b) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)”)),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (fn x => ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN (“x:('a)list”) (BETA_RULE (AP_THM x (“REVERSE (x:('a)list)”))))))),
      ASM_REWRITE_TAC[]]);

val SNOC_Axiom_old = prove(
  “!(e:'b) (f:'b -> ('a -> (('a)list -> 'b))).
        ?! fn1.
          (fn1[] = e) /\
          (!x l. fn1(SNOC x l) = f(fn1 l)x l)”,

 let val  lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
         [“e:'b”,“(\ft x l. f ft x (REVERSE l)):'b -> ('a -> (('a)list -> 'b))”]
        (PURE_ONCE_REWRITE_RULE
         [SYM (CONJUNCT1 REVERSE_DEF),
          PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
           (BETA_RULE (SPEC (“\l:('a)list.fn1(CONS x l) =
                       (f:'b -> ('a -> (('a)list -> 'b)))(fn1 l)x l”)
             (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
            list_Axiom_old))))
 in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL
    [
      EXISTS_TAC (“(fn1:('a)list->'b) o REVERSE”)
      THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[],

      REPEAT GEN_TAC THEN
      POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
                 REWRITE_RULE[REVERSE_REVERSE, f_REVERSE_lemma] o
                 BETA_RULE o REWRITE_RULE[o_DEF] o
                 SPECL [“(fn1' o REVERSE):('a)list->'b”,
                        “(fn1'' o REVERSE):('a)list->'b”])
     ]
  end);

val SNOC_Axiom = store_thm(
  "SNOC_Axiom",
  “!e f. ?fn:'a list -> 'b.
       (fn [] = e) /\
       (!x l. fn (SNOC x l) = f x l (fn l))”,
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC (CONV_RULE EXISTS_UNIQUE_CONV
                    (BETA_RULE
                     (Q.SPECL [‘e’, ‘\x y z. f y z x’] SNOC_Axiom_old))) THEN
  Q.EXISTS_TAC ‘fn1’ THEN ASM_REWRITE_TAC []);

val SNOC_INDUCT = save_thm("SNOC_INDUCT", prove_induction_thm SNOC_Axiom_old);
val SNOC_CASES =  save_thm("SNOC_CASES", hd (prove_cases_thm SNOC_INDUCT));

(* cf. rich_listTheory.IS_PREFIX_SNOC *)
Theorem isPREFIX_SNOC[simp] :
    l <<= SNOC x l
Proof
    Induct_on ‘l’ >> rw [SNOC, isPREFIX]
QED

local val REVERSE = REVERSE_SNOC_DEF
in
val MAP_REVERSE = Q.store_thm ("MAP_REVERSE",
   `!f l. MAP f (REVERSE l) = REVERSE (MAP f l)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [REVERSE, MAP, MAP_SNOC]);
end;

(*--------------------------------------------------------------*)
(* List generator                                               *)
(*  GENLIST f n = [f 0;...; f(n-1)]                             *)
(*--------------------------------------------------------------*)

Definition GENLIST:
  GENLIST (f:num->'a) 0 = [] /\
  GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)
End

Theorem LENGTH_GENLIST[simp]:
  !(f:num->'a) n. LENGTH(GENLIST f n) = n
Proof
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[GENLIST, LENGTH, LENGTH_SNOC]
QED

Definition GENLIST_AUX:
  (GENLIST_AUX f 0 l = l) /\
  (GENLIST_AUX f (SUC n) l = GENLIST_AUX f n ((f n)::l))
End
val _ = export_rewrites ["GENLIST_AUX_compute"]

(*---------------------------------------------------------------------------
       List padding (left and right)
 ---------------------------------------------------------------------------*)

Definition PAD_LEFT:
  PAD_LEFT c n s = (GENLIST (K c) (n - LENGTH s)) ++ s
End

Definition PAD_RIGHT:
  PAD_RIGHT c n s = s ++ (GENLIST (K c) (n - LENGTH s))
End

(*---------------------------------------------------------------------------
   Theorems about genlist. From Anthony Fox's theories. Added by Thomas Tuerk.
   Moved from rich_listTheory.
 ---------------------------------------------------------------------------*)

val MAP_GENLIST = store_thm("MAP_GENLIST",
  “!f g n. MAP f (GENLIST g n) = GENLIST (f o g) n”,
  Induct_on ‘n’
  THEN ASM_SIMP_TAC arith_ss [GENLIST, MAP_SNOC, MAP, o_THM]);

val EL_GENLIST = store_thm("EL_GENLIST",
  “!f n x. x < n ==> (EL x (GENLIST f n) = f x)”,
  Induct_on ‘n’ THEN1 SIMP_TAC arith_ss [] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [GENLIST] THEN
  Cases_on ‘x < n’ THEN
  POP_ASSUM (fn th => ASSUME_TAC
           (SUBS [(GSYM o Q.SPECL [‘f’,‘n’]) LENGTH_GENLIST] th) THEN
            ASSUME_TAC th) THEN1 (
    ASM_SIMP_TAC bool_ss [EL_SNOC]
  ) THEN
  ‘x = LENGTH (GENLIST f n)’ by FULL_SIMP_TAC arith_ss [LENGTH_GENLIST] THEN
  ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC] THEN
  REWRITE_TAC [LENGTH_GENLIST]);
val _ = export_rewrites ["EL_GENLIST"]

val HD_GENLIST = save_thm("HD_GENLIST",
  (SIMP_RULE arith_ss [EL] o Q.SPECL [‘f’,‘SUC n’,‘0’]) EL_GENLIST);

val HD_GENLIST_COR = Q.store_thm("HD_GENLIST_COR",
  ‘!n f. 0 < n ==> (HD (GENLIST f n) = f 0)’,
  Cases THEN REWRITE_TAC [prim_recTheory.LESS_REFL, HD_GENLIST]);

val GENLIST_FUN_EQ = store_thm("GENLIST_FUN_EQ",
  “!n f g. (GENLIST f n = GENLIST g n) = (!x. x < n ==> (f x = g x))”,
  SIMP_TAC bool_ss [LIST_EQ_REWRITE, LENGTH_GENLIST, EL_GENLIST]);

val GENLIST_APPEND = store_thm("GENLIST_APPEND",
  “!f a b. GENLIST f (a + b) = (GENLIST f b) ++ (GENLIST (\t. f (t + b)) a)”,
  Induct_on ‘a’ THEN
  ASM_SIMP_TAC arith_ss
    [GENLIST, APPEND_SNOC, APPEND_NIL, arithmeticTheory.ADD_CLAUSES]
);

val EVERY_GENLIST = store_thm("EVERY_GENLIST",
  “!n. EVERY P (GENLIST f n) = (!i. i < n ==> P (f i))”,
  Induct_on ‘n’ THEN ASM_SIMP_TAC arith_ss [GENLIST, EVERY_SNOC, EVERY_DEF]
    THEN metisLib.METIS_TAC [prim_recTheory.LESS_THM]);

val EXISTS_GENLIST = store_thm ("EXISTS_GENLIST",
  “!n. EXISTS P (GENLIST f n) = (?i. i < n /\ P (f i))”,
  Induct_on ‘n’ THEN RW_TAC arith_ss [GENLIST, EXISTS_SNOC, EXISTS_DEF]
    THEN metisLib.METIS_TAC [prim_recTheory.LESS_THM]);

val TL_GENLIST = Q.store_thm ("TL_GENLIST",
  ‘!f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n’,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_EQ
    THEN SRW_TAC [] [EL_GENLIST, LENGTH_GENLIST, LENGTH_TL]
    THEN ONCE_REWRITE_TAC [EL |> CONJUNCT2 |> GSYM]
    THEN ‘SUC x < SUC n’ by numLib.DECIDE_TAC
    THEN IMP_RES_TAC EL_GENLIST
    THEN ASM_SIMP_TAC arith_ss []);

val ZIP_GENLIST = store_thm("ZIP_GENLIST",
  “!l f n. (LENGTH l = n) ==>
      (ZIP (l,GENLIST f n) = GENLIST (\x. (EL x l,f x)) n)”,
  REPEAT STRIP_TAC THEN
  ‘LENGTH (ZIP (l,GENLIST f n)) = LENGTH (GENLIST (\x. (EL x l,f x)) n)’
    by ASM_SIMP_TAC arith_ss [LENGTH_GENLIST, LENGTH_ZIP] THEN
  ASM_SIMP_TAC arith_ss [LIST_EQ_REWRITE, LENGTH_GENLIST, LENGTH_ZIP,
                         EL_ZIP, EL_GENLIST]);

val GENLIST_CONS = store_thm(
  "GENLIST_CONS",
  “GENLIST f (SUC n) = f 0 :: (GENLIST (f o SUC) n)”,
  Induct_on ‘n’ THEN SRW_TAC [] [GENLIST, SNOC]);

Theorem GENLIST_ID:
  !x. GENLIST (\i. EL i x) (LENGTH x) = x
Proof
  Induct >> simp[GENLIST_CONS, GENLIST, combinTheory.o_ABS_L]
QED

val NULL_GENLIST = Q.store_thm("NULL_GENLIST",
  ‘!n f. NULL (GENLIST f n) = (n = 0)’,
  Cases THEN
  REWRITE_TAC [numTheory.NOT_SUC, NULL_DEF, CONJUNCT1 GENLIST, GENLIST_CONS]);

val GENLIST_AUX_lem = Q.prove(
  ‘!n l1 l2. GENLIST_AUX f n l1 ++ l2 = GENLIST_AUX f n (l1 ++ l2)’,
  Induct_on ‘n’ THEN SRW_TAC [] [GENLIST_AUX]);

val GENLIST_GENLIST_AUX = Q.store_thm("GENLIST_GENLIST_AUX",
  ‘!n. GENLIST f n = GENLIST_AUX f n []’,
  Induct_on ‘n’
  THEN RW_TAC bool_ss
         [SNOC_APPEND, APPEND, GENLIST_AUX, GENLIST_AUX_lem, GENLIST]);

val GENLIST_NUMERALS = store_thm(
  "GENLIST_NUMERALS",
  “(GENLIST f 0 = []) /\
    (GENLIST f (NUMERAL n) = GENLIST_AUX f (NUMERAL n) [])”,
  REWRITE_TAC [GENLIST_GENLIST_AUX, GENLIST_AUX]);
val _ = export_rewrites ["GENLIST_NUMERALS"]

(* Theorem: GENLIST f 0 = [] *)
(* Proof: by GENLIST *)
val GENLIST_0 = store_thm(
  "GENLIST_0",
  ``!f. GENLIST f 0 = []``,
  rw[]);

(* Theorem: GENLIST f 1 = [f 0] *)
(* Proof:
      GENLIST f 1
    = GENLIST f (SUC 0)          by ONE
    = SNOC (f 0) (GENLIST f 0)   by GENLIST
    = SNOC (f 0) []              by GENLIST
    = [f 0]                      by SNOC
*)
val GENLIST_1 = store_thm(
  "GENLIST_1",
  ``!f. GENLIST f 1 = [f 0]``,
  rw[]);

val MEM_GENLIST = Q.store_thm(
"MEM_GENLIST",
‘MEM x (GENLIST f n) <=> ?m. m < n /\ (x = f m)’,
SRW_TAC [] [MEM_EL, EL_GENLIST, EQ_IMP_THM] THEN
PROVE_TAC [EL_GENLIST] )

Theorem ALL_DISTINCT_SNOC:
  !x l. ALL_DISTINCT (SNOC x l) <=> ~MEM x l /\ ALL_DISTINCT l
Proof SRW_TAC [] [SNOC_APPEND, ALL_DISTINCT_APPEND] THEN PROVE_TAC[]
QED

Theorem ALL_DISTINCT_GENLIST:
  ALL_DISTINCT (GENLIST f n) <=>
   (!m1 m2. m1 < n /\ m2 < n /\ (f m1 = f m2) ==> (m1 = m2))
Proof
  Induct_on `n` THEN
  SRW_TAC [] [GENLIST, ALL_DISTINCT_SNOC, MEM_EL] THEN
  SRW_TAC [] [EQ_IMP_THM] THEN1 (
   IMP_RES_TAC prim_recTheory.LESS_SUC_IMP THEN
   Cases_on `m1 = n` THEN Cases_on `m2 = n` THEN SRW_TAC [] [] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    NTAC 2 (FIRST_X_ASSUM (Q.SPEC_THEN `m2` MP_TAC)) THEN
     SRW_TAC [] [] ) THEN
   NTAC 2 (FIRST_X_ASSUM (Q.SPEC_THEN `m1` MP_TAC)) THEN
   SRW_TAC [] [] )
  THEN1 (Q.RENAME_TAC [‘~(m < n)’, ‘f n = EL m (GENLIST f n)’] THEN
         STRIP_TAC THEN
         FIRST_X_ASSUM (Q.SPECL_THEN [`m`,`n`] MP_TAC) THEN
         SRW_TAC [] [prim_recTheory.LESS_SUC] THEN
         METIS_TAC [prim_recTheory.LESS_REFL] ) THEN
  METIS_TAC [prim_recTheory.LESS_SUC]
QED

Theorem TAKE_GENLIST:
  TAKE n (GENLIST f m) = GENLIST f (MIN n m)
Proof
  SRW_TAC[numSimps.ARITH_ss][LIST_EQ_REWRITE, LENGTH_TAKE_EQ,
                             arithmeticTheory.MIN_DEF, EL_TAKE]
QED

Theorem DROP_GENLIST:
  DROP n (GENLIST f m) = GENLIST (f o (+) n) (m-n)
Proof
  SRW_TAC[numSimps.ARITH_ss][LIST_EQ_REWRITE,EL_DROP]
QED

Theorem GENLIST_CONG[defncong]:
  !n1 n2 f1 f2.
    n1 = n2 /\ (!m. m < n2 ==> f1 m = f2 m) ==> GENLIST f1 n1 = GENLIST f2 n2
Proof
  simp[] >>
  Prim_rec.INDUCT_THEN (TypeBase.induction_of “:num”) strip_assume_tac >>
  simp[GENLIST_CONS]
QED

(* Theorem alias *)
Theorem GENLIST_EQ =
   GENLIST_CONG |> GEN ``n:num`` |> GEN ``f2:num -> 'a``
                |> GEN ``f1:num -> 'a``;
(*
val GENLIST_EQ = |- !f1 f2 n. (!m. m < n ==> f1 m = f2 m) ==> GENLIST f1 n = GENLIST f2 n: thm
*)

Theorem LIST_REL_O:
  !R1 R2. LIST_REL (R1 O R2) = LIST_REL R1 O LIST_REL R2
Proof
  simp[FUN_EQ_THM, O_DEF, LIST_REL_EL_EQN, EQ_IMP_THM] >> rw[]
  >- (full_simp_tac(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
      Q.RENAME_TAC [‘LENGTH as = LENGTH cs’, ‘R2 (EL _ as) (f _)’,
                    ‘R1 (f _) (EL _ cs)’] >>
      Q.EXISTS_TAC‘GENLIST f (LENGTH cs)’ >> simp[])
  >- simp[]
  >- metis_tac[]
QED

(* Theorem: (GENLIST f n = []) <=> (n = 0) *)
(* Proof:
   If part: GENLIST f n = [] ==> n = 0
      By contradiction, suppose n <> 0.
      Then LENGTH (GENLIST f n) = n <> 0  by LENGTH_GENLIST
      This contradicts LENGTH [] = 0.
   Only-if part: GENLIST f 0 = [], true   by GENLIST_0
*)
val GENLIST_EQ_NIL = store_thm(
  "GENLIST_EQ_NIL",
  ``!f n. (GENLIST f n = []) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  metis_tac[LENGTH_GENLIST, LENGTH_NIL]);

(* Theorem: LAST (GENLIST f (SUC n)) = f n *)
(* Proof:
     LAST (GENLIST f (SUC n))
   = LAST (SNOC (f n) (GENLIST f n))  by GENLIST
   = f n                              by LAST_SNOC
*)
val GENLIST_LAST = store_thm(
  "GENLIST_LAST",
  ``!f n. LAST (GENLIST f (SUC n)) = f n``,
  rw[GENLIST]);

(* Note:

- EVERY_MAP;
> val it = |- !P f l. EVERY P (MAP f l) <=> EVERY (\x. P (f x)) l : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
*)

(* Note: the following can use EVERY_GENLIST. *)

(* Theorem: !k. (k < n ==> f k = c) <=> EVERY (\x. x = c) (GENLIST f n) *)
(* Proof: by induction on n.
   Base case: !c. (!k. k < 0 ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f 0)
     Since GENLIST f 0 = [], this is true as no k < 0.
   Step case: (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n) ==>
              (!k. k < SUC n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f (SUC n))
         EVERY (\x. x = c) (GENLIST f (SUC n))
     <=> EVERY (\x. x = c) (SNOC (f n) (GENLIST f n))  by GENLIST
     <=> EVERY (\x. x = c) (GENLIST f n) /\ (f n = c)  by EVERY_SNOC
     <=> (!k. k < n ==> (f k = c)) /\ (f n = c)        by induction hypothesis
     <=> !k. k < SUC n ==> (f k = c)
*)
val GENLIST_CONSTANT = store_thm(
  "GENLIST_CONSTANT",
  ``!f n c. (!k. k < n ==> (f k = c)) <=> EVERY (\x. x = c) (GENLIST f n)``,
  strip_tac >>
  Induct_on ‘n’ >-
  rw[] >>
  rw_tac std_ss[EVERY_DEF, GENLIST, EVERY_SNOC, EQ_IMP_THM] >-
  metis_tac[prim_recTheory.LESS_SUC] >>
  Cases_on `k = n` >-
  rw_tac std_ss[] >>
  metis_tac[prim_recTheory.LESS_THM]);

Theorem isPREFIX_NIL :
    !x. [] <<= x /\ (x <<= [] <=> (x = []))
Proof
    qx_gen_tac ‘x’
 >> Cases_on ‘x’ >- rw []
 >> rw [isPREFIX]
QED

Theorem isPREFIX_REFL :
    !x. x <<= x
Proof
    Induct_on ‘x’ >> rw [isPREFIX]
QED

Theorem isPREFIX_TRANS :
    !x y z. x <<= y /\ y <<= z ==> x <<= z
Proof
    Induct_on ‘x’ >- rw []
 >> rpt GEN_TAC
 >> Cases_on ‘y’ >- rw []
 >> Cases_on ‘z’ >- rw []
 >> rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘l’ >> rw []
QED

Theorem isPREFIX_ANTISYM :
    !x y. x <<= y /\ y <<= x ==> x = y
Proof
    Induct_on ‘x’ >- rw []
 >> rpt GEN_TAC
 >> Cases_on ‘y’ >- rw []
 >> STRIP_TAC
 >> rw []
 >> fs []
QED

Theorem isPREFIX_SNOC_EQ :
   !x y z. z <<= SNOC x y <=> z <<= y \/ z = SNOC x y
Proof
    NTAC 2 GEN_TAC
 >> Q.ID_SPEC_TAC `x`
 >> Q.ID_SPEC_TAC `y`
 >> INDUCT_THEN list_INDUCT ASSUME_TAC
 >- (rpt GEN_TAC \\
     MP_TAC (Q.SPEC `z` list_CASES) \\
     STRIP_TAC \\
     rw [SNOC, isPREFIX_NIL, isPREFIX, CONS_11, NOT_CONS_NIL])
 >> rpt GEN_TAC
 >> MP_TAC (Q.SPEC `z` list_CASES)
 >> STRIP_TAC
 >> rw [SNOC, isPREFIX_NIL, isPREFIX, CONS_11, NOT_CONS_NIL]
 >> PROVE_TAC []
QED

Theorem isPREFIX_GENLIST_lemma[local] :
    !f m n. m <= n ==> GENLIST f m <<= GENLIST f n
Proof
    qx_gen_tac ‘f’
 >> Induct_on ‘n’ >- rw []
 >> rpt STRIP_TAC
 >> ‘m = SUC n \/ m <= n’ by METIS_TAC [LE]
 >- rw [isPREFIX_REFL]
 >> MATCH_MP_TAC isPREFIX_TRANS
 >> Q.EXISTS_TAC ‘GENLIST f n’ >> rw []
 >> rw [GENLIST, isPREFIX_SNOC]
QED

Theorem isPREFIX_GENLIST :
    !(f :num -> 'a) m n. GENLIST f m <<= GENLIST f n <=> m <= n
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- rw [isPREFIX_GENLIST_lemma]
 >> qid_spec_tac ‘m’
 >> qid_spec_tac ‘n’
 >> Induct_on ‘n’
 >- (rw [] >> fs [GENLIST_EQ_NIL])
 >> GEN_TAC
 >> simp [GENLIST, isPREFIX_SNOC_EQ]
 >> STRIP_TAC
 >- (MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> fs [LIST_EQ_REWRITE]
QED

Theorem isPREFIX_MAP :
    !f l1 l2. l1 <<= l2 ==> MAP f l1 <<= MAP f l2
Proof
    qx_gen_tac ‘f’
 >> Induct_on ‘l1’ >- rw []
 >> rpt STRIP_TAC
 >> Cases_on ‘l2’ >- fs []
 >> fs []
QED

(* ---------------------------------------------------------------------- *)

val FOLDL_SNOC = store_thm("FOLDL_SNOC",
    (“!(f:'b->'a->'b) e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x”),
    let val lem = prove(
        (“!l (f:'b->'a->'b) e x. FOLDL f e (SNOC x l) = f (FOLDL f e l) x”),
        LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC, FOLDL]
        THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[])
   in
    MATCH_ACCEPT_TAC lem
   end);

local open arithmeticTheory in
val SUM_SNOC = store_thm("SUM_SNOC",
    (“!x l. SUM (SNOC x l) = (SUM l) + x”),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUM, SNOC, ADD, ADD_0]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC]);

val SUM_APPEND = store_thm("SUM_APPEND",
    (“!l1 l2. SUM (APPEND l1 l2) = SUM l1 + SUM l2”),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM, APPEND, ADD, ADD_0, ADD_ASSOC]);
end

val SUM_MAP_FOLDL = Q.store_thm(
"SUM_MAP_FOLDL",
‘!ls. SUM (MAP f ls) = FOLDL (\a e. a + f e) 0 ls’,
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [] [FOLDL_SNOC, MAP_SNOC, SUM_SNOC, MAP, SUM, FOLDL]);

val SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST = Q.store_thm(
"SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST",
‘FINITE s ==> (SIGMA f s = SUM (MAP f (SET_TO_LIST s)))’,
SRW_TAC [] [SUM_IMAGE_DEF] THEN
SRW_TAC [] [ITSET_eq_FOLDL_SET_TO_LIST, SUM_MAP_FOLDL] THEN
AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
SRW_TAC [] [FUN_EQ_THM, arithmeticTheory.ADD_COMM]);

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

local open arithmeticTheory prim_recTheory in
val EL_REVERSE = store_thm("EL_REVERSE",
    “!n (l:'a list). n < (LENGTH l) ==>
     (EL n (REVERSE l) = EL (PRE(LENGTH l - n)) l)”,
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH, LENGTH_SNOC,
        EL, HD, TL, NOT_LESS_0, LESS_MONO_EQ, SUB_0] THENL[
        REWRITE_TAC[REVERSE_SNOC, PRE, EL_LENGTH_SNOC, HD],
        REWRITE_TAC[REVERSE_SNOC, SUB_MONO_EQ, TL]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
        THEN MATCH_MP_TAC (GSYM EL_SNOC)
        THEN REWRITE_TAC(PRE_SUB1 :: (map GSYM [SUB_PLUS, ADD1]))
        THEN numLib.DECIDE_TAC]);
end

val REVERSE_GENLIST = Q.store_thm("REVERSE_GENLIST",
‘REVERSE (GENLIST f n) = GENLIST (\m. f (PRE n - m)) n’,
  MATCH_MP_TAC LIST_EQ THEN
  SRW_TAC [] [EL_REVERSE] THEN
  ‘PRE (n - x) < n’ by numLib.DECIDE_TAC THEN
  SRW_TAC [] [EL_GENLIST] THEN
  AP_TERM_TAC THEN numLib.DECIDE_TAC)

val FOLDL_UNION_BIGUNION = store_thm(
"FOLDL_UNION_BIGUNION",
“!f ls s. FOLDL (\s x. s UNION f x) s ls = s UNION BIGUNION (IMAGE f (set ls))”,
GEN_TAC THEN Induct THEN SRW_TAC[] [FOLDL, UNION_ASSOC])

Theorem FOLDL_UNION_BIGUNION_paired:
  !f ls s. FOLDL (\s (x,y). s UNION f x y) s ls =
           s UNION BIGUNION (IMAGE (UNCURRY f) (set ls))
Proof
  GEN_TAC THEN Induct THEN1 SRW_TAC[] [FOLDL] THEN
  Cases THEN SRW_TAC[] [FOLDL, UNION_ASSOC, GSYM pairTheory.LAMBDA_PROD]
QED

val FOLDL_ZIP_SAME = store_thm(
"FOLDL_ZIP_SAME",
“!ls f e. FOLDL f e (ZIP (ls,ls)) = FOLDL (\x y. f x (y,y)) e ls”,
Induct THEN SRW_TAC[] [FOLDL, ZIP])
val _ = export_rewrites["FOLDL_ZIP_SAME"]

val MAP_ZIP_SAME = store_thm(
"MAP_ZIP_SAME",
“!ls f. MAP f (ZIP (ls,ls)) = MAP (\x. f (x,x)) ls”,
Induct THEN SRW_TAC [] [MAP, ZIP])
val _ = export_rewrites["MAP_ZIP_SAME"]

(* ----------------------------------------------------------------------
    All lists have infinite universes
   ---------------------------------------------------------------------- *)

val INFINITE_LIST_UNIV = store_thm(
  "INFINITE_LIST_UNIV",
  “INFINITE univ(:'a list)”,
  REWRITE_TAC [] THEN
  SRW_TAC [] [INFINITE_UNIV] THEN
  Q.EXISTS_TAC ‘\l. x::l’ THEN SRW_TAC [] [] THEN
  Q.EXISTS_TAC ‘[]’ THEN SRW_TAC [] [])
val _ = export_rewrites ["INFINITE_LIST_UNIV"]


(*---------------------------------------------------------------------------*)
(* Tail recursive versions for better memory usage when applied in ML        *)
(*---------------------------------------------------------------------------*)

(* EVAL performance of LEN seems to be worse than of LENGTH *)

Definition LEN_DEF:
  LEN [] n = n /\
  LEN (h::t) n = LEN t (n+1)
End

Definition REV_DEF:
  (REV [] acc = acc) /\
  (REV (h::t) acc = REV t (h::acc))
End

val LEN_LENGTH_LEM = Q.store_thm
("LEN_LENGTH_LEM",
 ‘!L n. LEN L n = LENGTH L + n’,
 Induct THEN RW_TAC arith_ss [LEN_DEF, LENGTH]);

val REV_REVERSE_LEM = Q.store_thm
("REV_REVERSE_LEM",
 ‘!L1 L2. REV L1 L2 = (REVERSE L1) ++ L2’,
 Induct THEN RW_TAC arith_ss [REV_DEF, REVERSE_DEF, APPEND]
        THEN REWRITE_TAC [GSYM APPEND_ASSOC]
        THEN RW_TAC bool_ss [APPEND]);

val LENGTH_LEN = Q.store_thm
("LENGTH_LEN",
 ‘!L. LENGTH L = LEN L 0’,
 RW_TAC arith_ss [LEN_LENGTH_LEM]);

val REVERSE_REV = Q.store_thm
("REVERSE_REV",
 ‘!L. REVERSE L = REV L []’,
 PROVE_TAC [REV_REVERSE_LEM, APPEND_NIL]);

val SUM_ACC_DEF = dDefine
  ‘(SUM_ACC [] acc = acc) /\
   (SUM_ACC (h::t) acc = SUM_ACC t (h+acc))’

val SUM_ACC_SUM_LEM = store_thm
("SUM_ACC_SUM_LEM",
 “!L n. SUM_ACC L n = SUM L + n”,
 Induct THEN RW_TAC arith_ss [SUM_ACC_DEF, SUM]);

val SUM_SUM_ACC = store_thm
("SUM_SUM_ACC",
  “!L. SUM L = SUM_ACC L 0”,
  PROVE_TAC [SUM_ACC_SUM_LEM, arithmeticTheory.ADD_0])

(* ----------------------------------------------------------------------
    List "splitting" results
   ---------------------------------------------------------------------- *)

(* These loop! Use with care *)
val EXISTS_LIST = store_thm(
  "EXISTS_LIST",
  “(?l. P l) <=> P [] \/ ?h t. P (h::t)”,
  METIS_TAC [list_CASES]);

val FORALL_LIST = store_thm(
  "FORALL_LIST",
  “(!l. P l) <=> P [] /\ !h t. P (h::t)”,
  METIS_TAC [list_CASES]);

(* now on with the show *)
val MEM_SPLIT_APPEND_first = store_thm(
  "MEM_SPLIT_APPEND_first",
  “MEM e l <=> ?pfx sfx. (l = pfx ++ [e] ++ sfx) /\ ~MEM e pfx”,
  Induct_on ‘l’ THEN SRW_TAC [] [] THEN Cases_on ‘e = a’ THEN
  SRW_TAC [] [] THENL[
    MAP_EVERY Q.EXISTS_TAC [‘[]’, ‘l’] THEN SRW_TAC [] [],
    SRW_TAC [] [SimpRHS, Once EXISTS_LIST]
  ]);

val MEM_SPLIT_APPEND_last = store_thm(
  "MEM_SPLIT_APPEND_last",
  “MEM e l <=> ?pfx sfx. (l = pfx ++ [e] ++ sfx) /\ ~MEM e sfx”,
  Q.ID_SPEC_TAC ‘l’ THEN SNOC_INDUCT_TAC THEN SRW_TAC [] [] THEN
  Cases_on ‘e = x’ THEN SRW_TAC [] [] THENL [
    MAP_EVERY Q.EXISTS_TAC [‘l’, ‘[]’] THEN SRW_TAC [] [SNOC_APPEND],
    SRW_TAC [] [EQ_IMP_THM] THENL [
      MAP_EVERY Q.EXISTS_TAC [‘pfx’, ‘SNOC x sfx’] THEN
      SRW_TAC [] [APPEND_ASSOC, APPEND_SNOC],
      Q.SPEC_THEN ‘sfx’ STRIP_ASSUME_TAC SNOC_CASES THEN
      SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
        FULL_SIMP_TAC (srw_ss()) [GSYM SNOC_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [APPEND_SNOC] THEN SRW_TAC [] [] THEN
      METIS_TAC []
    ]
  ]);

val APPEND_EQ_APPEND = store_thm(
  "APPEND_EQ_APPEND",
  “(l1 ++ l2 = m1 ++ m2) <=>
      (?l. (l1 = m1 ++ l) /\ (m2 = l ++ l2)) \/
      (?l. (m1 = l1 ++ l) /\ (l2 = l ++ m2))”,
  MAP_EVERY Q.ID_SPEC_TAC [‘m2’, ‘m1’, ‘l2’, ‘l1’] THEN Induct_on ‘l1’ THEN
  SRW_TAC [] [] THEN
  Cases_on ‘m1’ THEN SRW_TAC [] [] THEN METIS_TAC []);

val APPEND_EQ_CONS = store_thm(
  "APPEND_EQ_CONS",
  “(l1 ++ l2 = h::t) <=>
       ((l1 = []) /\ (l2 = h::t)) \/
       ?lt. (l1 = h::lt) /\ (t = lt ++ l2)”,
  MAP_EVERY Q.ID_SPEC_TAC [‘t’, ‘h’, ‘l2’, ‘l1’] THEN Induct_on ‘l1’ THEN
  SRW_TAC [] [] THEN METIS_TAC []);

(* could just use APPEND_EQ_APPEND and APPEND_EQ_SING, but this gives you
   four possibilities
      |- (x ++ [e] ++ y = a ++ b) <=>
           (?l'. (x = a ++ l') /\ (b = l' ++ [e] ++ y)) \/
           (a = x ++ [e]) /\ (b = y) \/
           (a = x) /\ (b = e::y) \/
           ?l. (a = x ++ [e] ++ l) /\ (y = l ++ b)
   Note that the middle two are instances of the outer two with the
   existentially quantified l set to []
*)
val APPEND_EQ_APPEND_MID = store_thm(
  "APPEND_EQ_APPEND_MID",
  “(l1 ++ [e] ++ l2 = m1 ++ m2) <=>
       (?l. (m1 = l1 ++ [e] ++ l) /\ (l2 = l ++ m2)) \/
       (?l. (l1 = m1 ++ l) /\ (m2 = l ++ [e] ++ l2))”,
  MAP_EVERY Q.ID_SPEC_TAC [‘m2’, ‘m1’, ‘l2’, ‘e’, ‘l1’] THEN Induct THEN
  Cases_on ‘m1’ THEN SRW_TAC [] [] THEN METIS_TAC []);

(* --------------------------------------------------------------------- *)

Definition LUPDATE_DEF[notuserdef,nocompute]:
  LUPDATE e n [] = [] /\
  LUPDATE e n (x::l) = if n = 0 then e :: l else x :: LUPDATE e (PRE n) l
End

Theorem LUPDATE_def[userdef]:
  (!e n. LUPDATE e n [] = [] : 'a list) /\
  (!e x l. LUPDATE e 0 (x::l) = e::l) /\
  (!e n x l. LUPDATE e (SUC n) (x::l) = x :: LUPDATE e n l)
Proof
  simp[LUPDATE_DEF]
QED

val _ = DefnBase.register_indn $ Prim_rec.gen_indthm
           {lookup_ind = TypeBase.induction_of} LUPDATE_DEF

val LUPDATE_NIL = store_thm("LUPDATE_NIL[simp]",
  “!xs n x. (LUPDATE x n xs = []) <=> (xs = [])”,
  Cases \\ Cases_on ‘n’ \\ FULL_SIMP_TAC (srw_ss()) [LUPDATE_def]);

val LUPDATE_SEM = store_thm ("LUPDATE_SEM",
  “(!e:'a n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
    (!e:'a n l p.
       p < LENGTH l ==>
       (EL p (LUPDATE e n l) = if p = n then e else EL p l))”,
  CONJ_TAC
  THEN Induct_on ‘n’
  THEN Cases_on ‘l’
  THEN ASM_SIMP_TAC arith_ss [LUPDATE_def, LENGTH]
  THEN Cases_on ‘p’
  THEN ASM_SIMP_TAC arith_ss [EL, HD, TL]);

val EL_LUPDATE = store_thm("EL_LUPDATE",
  “!ys (x:'a) i k.
      EL i (LUPDATE x k ys) =
      if (i = k) /\ k < LENGTH ys then x else EL i ys”,
  Induct_on ‘ys’ THEN Cases_on ‘k’ THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC arith_ss [LUPDATE_def, LENGTH]
  THEN Cases_on ‘i’
  THEN FULL_SIMP_TAC arith_ss [LUPDATE_def, LENGTH, EL, HD, TL]);

val LENGTH_LUPDATE = store_thm("LENGTH_LUPDATE",
  “!(x:'a) n ys. LENGTH (LUPDATE x n ys) = LENGTH ys”,
  SIMP_TAC bool_ss [LUPDATE_SEM]);
val _ = export_rewrites ["LENGTH_LUPDATE"]

val LUPDATE_LENGTH = store_thm("LUPDATE_LENGTH",
  “!xs x (y:'a) ys. LUPDATE x (LENGTH xs) (xs ++ y::ys) = xs ++ x::ys”,
  Induct THEN FULL_SIMP_TAC bool_ss [LENGTH, APPEND, LUPDATE_def,
    NOT_SUC, PRE, INV_SUC_EQ]);

val LUPDATE_SNOC = store_thm("LUPDATE_SNOC",
  “!ys k x (y:'a).
      LUPDATE x k (SNOC y ys) =
      if k = LENGTH ys then SNOC x ys else SNOC y (LUPDATE x k ys)”,
  Induct THEN Cases_on ‘k’ THEN Cases_on ‘n = LENGTH ys’
  THEN FULL_SIMP_TAC bool_ss [SNOC, LUPDATE_def, LENGTH, NOT_SUC,
         PRE, INV_SUC_EQ]);

val MEM_LUPDATE_E = store_thm("MEM_LUPDATE_E",
  “!l x y i. MEM x (LUPDATE y i l) ==> (x = y) \/ MEM x l”,
  Induct THEN SRW_TAC [] [LUPDATE_def] THEN
  Cases_on‘i’THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def] THEN
  PROVE_TAC[])

val MEM_LUPDATE = store_thm(
  "MEM_LUPDATE",
  “!l x y i. MEM x (LUPDATE y i l) <=>
                i < LENGTH l /\ (x = y) \/
                ?j. j < LENGTH l /\ i <> j /\ (EL j l = x)”,
  Induct THEN SRW_TAC [] [LUPDATE_def] THEN
  Cases_on ‘i’ THEN SRW_TAC [] [LUPDATE_def] THENL [
    SRW_TAC [] [Once arithmeticTheory.EXISTS_NUM] THEN
    METIS_TAC [MEM_EL],
    EQ_TAC THEN SRW_TAC [] [] THENL [
      DISJ2_TAC THEN Q.EXISTS_TAC ‘0’ THEN SRW_TAC [] [],
      DISJ2_TAC THEN Q.EXISTS_TAC ‘SUC j’ THEN SRW_TAC [] [],
      Cases_on ‘j’ THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC[]
    ]
  ]);

Theorem LUPDATE_compute[compute] = numLib.SUC_RULE LUPDATE_def

val LUPDATE_MAP = store_thm("LUPDATE_MAP",
“!x n l f. MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)”,
 Induct_on ‘l’ THEN SRW_TAC [] [LUPDATE_def] THEN Cases_on ‘n’ THEN
 FULL_SIMP_TAC (srw_ss()) [LUPDATE_def]);

Theorem LUPDATE_GENLIST:
 !m n e f. LUPDATE e n (GENLIST f m) = GENLIST ((n =+ e) f) m
Proof
 BasicProvers.Induct \\ simp [GENLIST_CONS] \\ Cases \\
 simp [LUPDATE_def, combinTheory.APPLY_UPDATE_THM, GENLIST_FUN_EQ]
QED

Definition EVERYi_def:
  (EVERYi P [] <=> T) /\
  (EVERYi P (h::t) <=> P 0 h /\ EVERYi (P o SUC) t)
End

Definition splitAtPki_def:
  (splitAtPki P k [] = k [] []) /\
  (splitAtPki P k (h::t) =
     if P 0 h then k [] (h::t)
     else splitAtPki (P o SUC) (\p s. k (h::p) s) t)
End

val splitAtPki_APPEND = store_thm(
  "splitAtPki_APPEND",
  “!l1 l2 P k.
      EVERYi (\i. $~ o P i) l1 /\ (0 < LENGTH l2 ==> P (LENGTH l1) (HD l2)) ==>
      (splitAtPki P k (l1 ++ l2) = k l1 l2)”,
  Induct THEN SRW_TAC [] [EVERYi_def, splitAtPki_def] THEN1
    (Cases_on ‘l2’ THEN FULL_SIMP_TAC (srw_ss())[splitAtPki_def]) THEN
  FULL_SIMP_TAC (srw_ss()) [o_DEF]);

val splitAtPki_EQN = store_thm(
  "splitAtPki_EQN",
  “splitAtPki P k l =
      case OLEAST i. i < LENGTH l /\ P i (EL i l) of
          NONE => k l []
        | SOME i => k (TAKE i l) (DROP i l)”,
  MAP_EVERY Q.ID_SPEC_TAC [‘P’, ‘k’, ‘l’] THEN Induct THEN
  ASM_SIMP_TAC (srw_ss()) [splitAtPki_def] THEN POP_ASSUM (K ALL_TAC) THEN
  MAP_EVERY Q.X_GEN_TAC [‘h’, ‘k’, ‘P’] THEN Cases_on ‘P 0 h’ THEN1
    (ASM_SIMP_TAC (srw_ss()) [] THEN
     ‘(OLEAST i. i < SUC (LENGTH l) /\ P i (EL i (h::l))) = SOME 0’
        suffices_by SRW_TAC [] [] THEN
     ASM_SIMP_TAC (srw_ss()) [whileTheory.OLEAST_EQ_SOME]) THEN
  SRW_TAC [] [] THEN
  Cases_on ‘OLEAST i. i < LENGTH l /\ P (SUC i) (EL i l)’ >> fs[]
  >- (‘(OLEAST i. i < SUC (LENGTH l) /\ P i (EL i (h::l))) = NONE’
        suffices_by (DISCH_THEN SUBST1_TAC THEN SRW_TAC[][]) THEN
      SRW_TAC[][] >> Q.RENAME_TAC [‘EL i (h::t)’] >> Cases_on ‘i’ >>
      SRW_TAC[][]) THEN
  Q.RENAME_TAC [‘h::TAKE i t’] >>
  ‘(OLEAST i. i < SUC (LENGTH t) /\ P i (EL i (h::t))) = SOME (SUC i)’
      suffices_by SRW_TAC [] [] THEN
  fs[whileTheory.OLEAST_EQ_SOME] >> Cases >> SRW_TAC[][]);

val TAKE_splitAtPki = store_thm(
  "TAKE_splitAtPki",
  “TAKE n l = splitAtPki (K o (=) n) K l”,
  SRW_TAC [] [splitAtPki_EQN] THEN
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN
  SRW_TAC[numSimps.ARITH_ss] [TAKE_LENGTH_TOO_LONG])

val DROP_splitAtPki = store_thm(
  "DROP_splitAtPki",
  “DROP n l = splitAtPki (K o (=) n) (K I) l”,
  SRW_TAC [] [splitAtPki_EQN] THEN
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN
  SRW_TAC[numSimps.ARITH_ss] [DROP_LENGTH_TOO_LONG]);

Theorem splitAtPki_RAND:
  f (splitAtPki P k l) = splitAtPki P ($o ($o f) k) l
Proof
  rw[splitAtPki_EQN] >> BasicProvers.CASE_TAC >> simp[]
QED

Theorem splitAtPki_MAP:
  splitAtPki P k (MAP f l) =
  splitAtPki (combin$C ($o $o P) f) (combin$C ($o o k o MAP f) (MAP f)) l
Proof
  rw[splitAtPki_EQN,MAP_TAKE,MAP_DROP]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ rw[EQ_IMP_THM] \\ REV_FULL_SIMP_TAC (srw_ss())[EL_MAP]
QED

Theorem splitAtPki_change_predicate:
  (!i. i < LENGTH l ==> (P1 i (EL i l) <=> P2 i (EL i l))) ==>
  (splitAtPki P1 k l = splitAtPki P2 k l)
Proof
  rw[splitAtPki_EQN] >> rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
  simp[FUN_EQ_THM] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    List monad related stuff
   ---------------------------------------------------------------------- *)

(* the bind function is flatMap with arguments in a different order *)
val LIST_BIND_def = Define‘
  LIST_BIND l f = FLAT (MAP f l)
’

val LIST_BIND_THM = store_thm(
  "LIST_BIND_THM",
  “(LIST_BIND [] f = []) /\
    (LIST_BIND (h::t) f = f h ++ LIST_BIND t f)”,
  SIMP_TAC (srw_ss()) [LIST_BIND_def]);
val _ = export_rewrites ["LIST_BIND_THM"]

val LIST_IGNORE_BIND_def = Define‘
  LIST_IGNORE_BIND m1 m2 = LIST_BIND m1 (K m2)
’;

val LIST_BIND_ID = store_thm(
  "LIST_BIND_ID",
  “(LIST_BIND l (\x.x) = FLAT l) /\
    (LIST_BIND l I = FLAT l)”,
  SIMP_TAC (srw_ss()) [LIST_BIND_def]);

val LIST_BIND_APPEND = store_thm(
  "LIST_BIND_APPEND",
  “LIST_BIND (l1 ++ l2) f = LIST_BIND l1 f ++ LIST_BIND l2 f”,
  Induct_on ‘l1’ THEN ASM_SIMP_TAC (srw_ss()) [APPEND_ASSOC]);

val LIST_BIND_MAP = store_thm(
  "LIST_BIND_MAP",
  “LIST_BIND (MAP f l) g = LIST_BIND l (g o f)”,
  Induct_on ‘l’ THEN ASM_SIMP_TAC (srw_ss()) []);

val MAP_LIST_BIND = store_thm(
  "MAP_LIST_BIND",
  “MAP f (LIST_BIND l g) = LIST_BIND l (MAP f o g)”,
  Induct_on ‘l’ THEN ASM_SIMP_TAC (srw_ss()) [MAP_APPEND]);

(* monad associativity *)
val LIST_BIND_LIST_BIND = store_thm(
  "LIST_BIND_LIST_BIND",
  “LIST_BIND (LIST_BIND l g) f = LIST_BIND l (combin$C LIST_BIND f o g)”,
  Induct_on ‘l’ THEN ASM_SIMP_TAC (srw_ss()) [LIST_BIND_APPEND]);

val LIST_GUARD_def = Define‘LIST_GUARD b = if b then [()] else []’;

(* the "return" or "pure" constant for lists isn't an existing one, unlike
   the situation with 'a option, where SOME fits the bill. *)
val _ = overload_on("SINGL", “\x:'a. [x]”)
val _ = overload_on("", “\x:'a. [x]”)

val SINGL_LIST_APPLY_L = store_thm(
  "SINGL_LIST_APPLY_L",
  “LIST_BIND (SINGL x) f = f x”,
  SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["SINGL_LIST_APPLY_L"]

val SINGL_LIST_APPLY_R = store_thm(
  "SINGL_LIST_APPLY_R",
  “LIST_BIND l SINGL = l”,
  Induct_on ‘l’ THEN ASM_SIMP_TAC (srw_ss()) [LIST_BIND_def]);

(* shows that lists are what Haskell would call Applicative *)
(* in 'a option, the apply applies a function to an argument if both are
   SOME, and otherwise returns NONE.  In lists, there is a cross-product
   created - this makes sense when you think of the list monad as being
   the non-determinism thing: you'd want every possible combination of
   the possibilities in fs and xs *)
val LIST_APPLY_def = Define‘
  LIST_APPLY fs xs = LIST_BIND fs (combin$C MAP xs)
’

(* pick up the <*> syntax *)
val _ = overload_on("APPLICATIVE_FAPPLY", “LIST_APPLY”)

(* derives the lift2 function to boot *)
val LIST_LIFT2_def = Define‘
  LIST_LIFT2 f xs ys = LIST_APPLY (MAP f xs) ys
’
(* e.g.,
    > EVAL ``LIST_LIFT2 (+) [1;3;4] [10;5]``
        |- ...  = [11;6;13;8;14;9]
    i.e., the sums of all possible pairs
*)


(* proofs of the relevant "laws" *)
val SINGL_APPLY_MAP = store_thm(
  "SINGL_APPLY_MAP",
  “LIST_APPLY (SINGL f) l = MAP f l”,
  SIMP_TAC (srw_ss()) [LIST_APPLY_def, LIST_BIND_def]);

val SINGL_SINGL_APPLY = store_thm(
  "SINGL_SINGL_APPLY",
  “LIST_APPLY (SINGL f) (SINGL x) = SINGL (f x)”,
  SIMP_TAC (srw_ss()) [LIST_APPLY_def, LIST_BIND_def]);
val _ = export_rewrites ["SINGL_SINGL_APPLY"]

val SINGL_APPLY_PERMUTE = store_thm(
  "SINGL_APPLY_PERMUTE",
  “LIST_APPLY fs (SINGL x) = LIST_APPLY (SINGL (\f. f x)) fs”,
  SIMP_TAC (srw_ss()) [LIST_APPLY_def, LIST_BIND_def] THEN
  Induct_on ‘fs’ THEN ASM_SIMP_TAC (srw_ss()) []);

val MAP_FLAT = store_thm(
  "MAP_FLAT",
  “MAP f (FLAT l) = FLAT (MAP (MAP f) l)”,
  Induct_on ‘l’ THEN ASM_SIMP_TAC (srw_ss()) [MAP_APPEND])

Theorem FLAT_MAP_K_NIL:
  !ls. FLAT (MAP (K []) ls) = []
Proof
  Induct \\ rw[]
QED

val LIST_APPLY_o = store_thm(
  "LIST_APPLY_o",
  “LIST_APPLY (LIST_APPLY (LIST_APPLY (SINGL (o)) fs) gs) xs =
    LIST_APPLY fs (LIST_APPLY gs xs)”,
  ASM_SIMP_TAC (srw_ss()) [LIST_APPLY_def] THEN
  Induct_on ‘fs’ THEN
  ASM_SIMP_TAC (srw_ss()) [LIST_BIND_APPEND, MAP_LIST_BIND,
                           APPEND_11] THEN
  SIMP_TAC (srw_ss()) [o_DEF, MAP_MAP_o, LIST_BIND_MAP]);

(* ----------------------------------------------------------------------
    Various lexicographic orderings on lists
   ---------------------------------------------------------------------- *)

val SHORTLEX_def = Define‘
  (SHORTLEX R [] l2 <=> l2 <> []) /\
  (SHORTLEX R (h1::t1) l2 <=>
        case l2 of
            [] => F
          | h2::t2 => if LENGTH t1 < LENGTH t2 then T
                      else if LENGTH t1 = LENGTH t2 then
                        if R h1 h2 then T
                        else if h1 = h2 then SHORTLEX R t1 t2
                        else F
                      else F)
’;

val def' = uncurry CONJ (Lib.pair_map SPEC_ALL (CONJ_PAIR SHORTLEX_def))
val SHORTLEX_THM = save_thm(
  "SHORTLEX_THM[simp]",
  CONJ (def' |> Q.INST [‘l2’ |-> ‘[]’]
             |> SIMP_RULE (srw_ss()) [])
       (def' |> Q.INST [‘l2’ |-> ‘h2::t2’]
             |> SIMP_RULE (srw_ss()) []))

val SHORTLEX_MONO = store_thm(
  "SHORTLEX_MONO[mono]",
  “(!x y. R1 x y ==> R2 x y) ==> SHORTLEX R1 x y ==> SHORTLEX R2 x y”,
  STRIP_TAC THEN Q.ID_SPEC_TAC‘y’ THEN Induct_on‘x’ THEN Cases_on‘y’ THEN
  SRW_TAC[][SHORTLEX_THM] THEN PROVE_TAC[]);

val SHORTLEX_NIL2 = store_thm(
  "SHORTLEX_NIL2[simp]",
  “~SHORTLEX R l []”,
  Cases_on ‘l’ THEN SIMP_TAC (srw_ss()) [SHORTLEX_def]);

val SHORTLEX_transitive = store_thm(
  "SHORTLEX_transitive",
  “transitive R ==> transitive (SHORTLEX R)”,
  SIMP_TAC(srw_ss()) [transitive_def] THEN STRIP_TAC THEN Induct THEN
  SIMP_TAC (srw_ss()) [SHORTLEX_def] THEN
  MAP_EVERY Q.X_GEN_TAC [‘h’, ‘y’, ‘z’] THEN Cases_on ‘y’ THEN
  SIMP_TAC (srw_ss()) [] THEN Cases_on ‘z’ THEN
  SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC[arithmeticTheory.LESS_TRANS]);

val LENGTH_LT_SHORTLEX = Q.store_thm(
  "LENGTH_LT_SHORTLEX",
  ‘!l1 l2. LENGTH l1 < LENGTH l2 ==> SHORTLEX R l1 l2’,
  Induct >> simp[SHORTLEX_def] >> rpt gen_tac >> Cases_on ‘l2’ >> simp[]);

val SHORTLEX_LENGTH_LE = Q.store_thm(
  "SHORTLEX_LENGTH_LE",
  ‘!l1 l2. SHORTLEX R l1 l2 ==> LENGTH l1 <= LENGTH l2’,
  Induct >> simp[SHORTLEX_def] >> rpt gen_tac >> Cases_on ‘l2’ >> simp[] >>
  rw[] >> simp[]);

val SHORTLEX_total = store_thm(
  "SHORTLEX_total",
  “total (RC R) ==> total (RC (SHORTLEX R))”,
  SIMP_TAC (srw_ss()) [total_def, RC_DEF] THEN STRIP_TAC THEN Induct THEN
  SIMP_TAC (srw_ss()) [SHORTLEX_def] THEN MAP_EVERY Q.X_GEN_TAC [‘h’, ‘y’] THEN
  Cases_on ‘y’ THEN SIMP_TAC (srw_ss()) [] THEN
  Q.RENAME_TAC [‘LENGTH l1 < LENGTH l2’, ‘SHORTLEX R l1 l2’, ‘R h1 h2’] >>
  MAP_EVERY Cases_on [‘LENGTH l1 < LENGTH l2’, ‘h1 = h2’, ‘l1 = l2’] >>
  simp[] >> metis_tac[arithmeticTheory.LESS_LESS_CASES]);

val WF_SHORTLEX_same_lengths = Q.store_thm(
  "WF_SHORTLEX_same_lengths",
  ‘WF R ==>
   !l s. (!d. d IN s ==> (LENGTH d = l)) /\ (?a. a IN s) ==>
         ?b. b IN s /\ !c. SHORTLEX R c b ==> c NOTIN s’,
  strip_tac >> ho_match_mp_tac (TypeBase.induction_of “:num”) >>
  simp[] >> rw[] >- (Q.EXISTS_TAC ‘[]’ >> simp[] >> metis_tac[]) >>
  Q.RENAME_TAC [‘LENGTH _ = SUC N’] >>
  ‘[] NOTIN s’ by (strip_tac >> ‘LENGTH [] = SUC N’ by metis_tac[] >> fs[]) >>
  Q.ABBREV_TAC ‘hds = IMAGE HD s’ >>
  ‘?ah. hds ah’ by
     (‘?ah. ah IN hds’ suffices_by simp[IN_DEF] >>
      simp[Abbr‘hds’] >> metis_tac[]) >>
  ‘?m. hds m /\ !n. R n m ==> n NOTIN hds’
    by (simp[IN_DEF] >> metis_tac[relationTheory.WF_DEF]) >>
  Q.ABBREV_TAC ‘ms = { a | a IN s /\ (HD a = m) }’ >>
  ‘?b. b IN ms /\ !c. SHORTLEX R c b ==> c NOTIN ms’ suffices_by
    (strip_tac >> Q.EXISTS_TAC ‘b’ >>
     ‘b IN s’ by fs[Abbr‘ms’] >> simp[] >> rpt strip_tac >>
     ‘c NOTIN ms’ by metis_tac[] >>
     ‘HD c <> m’
        by (pop_assum mp_tac >> simp_tac (srw_ss()) [Abbr‘ms’] >> simp[]) >>
     ‘(LENGTH c = SUC N) /\ (LENGTH b = SUC N)’ by simp[] >>
     ‘?ch ct. c = ch :: ct’ by (Cases_on ‘c’ >> fs[]) >>
     ‘?bh bt. b = bh :: bt’ by (Cases_on ‘b’ >> fs[]) >>
     fs[Abbr‘ms’]
     >- (‘ch IN hds’ by (simp[Abbr‘hds’] >> metis_tac[HD]) >>
         metis_tac[]) >>
     metis_tac[]) >>
  CONV_TAC (HO_REWR_CONV EXISTS_LIST) >> DISJ2_TAC >>
  Q.EXISTS_TAC ‘m’ >>
  ONCE_REWRITE_TAC [tautLib.TAUT ‘(p ==> q) <=> (~q ==> ~p)’] >>
  simp[] >> simp[Once FORALL_LIST] >>
  Q.ABBREV_TAC ‘mts = { t | m::t IN s }’ >>
  ‘!d. d IN mts ==> (LENGTH d = N)’
    by (simp[Abbr‘mts’] >> rw[] >> first_x_assum drule >> simp[]) >>
  ‘?a0. a0 IN mts’
    by (simp[Abbr‘mts’] >>
        ‘m IN hds’ by simp[IN_DEF] >> pop_assum mp_tac >>
        simp[Abbr‘hds’] >> fs[] >>
        Q.RENAME_TAC [‘R _ m’, ‘m = HD e’, ‘e IN s’] >> Cases_on ‘e’ >>
        fs[] >> metis_tac[]) >>
  ‘?t. t IN mts /\ !u. SHORTLEX R u t ==> u NOTIN mts’ by metis_tac[] >>
  Q.EXISTS_TAC ‘t’ >> rw[]
  >- fs[Abbr‘mts’, Abbr‘ms’]
  >- fs[Abbr‘mts’, Abbr‘ms’]
  >- (fs[Abbr‘mts’, Abbr‘ms’] >> rw[]) >>
  fs[Abbr‘mts’, Abbr‘ms’] >> rw[] >> metis_tac[IN_DEF]);

val WF_SHORTLEX = Q.store_thm(
  "WF_SHORTLEX[simp]",
  ‘WF R ==> WF (SHORTLEX R)’,
  simp[relationTheory.WF_DEF] >> rpt strip_tac >>
  Q.ABBREV_TAC ‘minlen = (LEAST) (IMAGE LENGTH B)’ >>
  ‘?a. B a /\ (LENGTH a = minlen) /\ !b. B b ==> LENGTH a <= LENGTH b’
    by (simp[Abbr‘minlen’] >> numLib.LEAST_ELIM_TAC >>
        simp[IMAGE_applied] >> simp[IN_DEF] >>
        metis_tac[arithmeticTheory.NOT_LESS]) >>
  markerLib.RM_ABBREV_TAC "minlen" >> rw[] >>
  Q.ABBREV_TAC ‘as = { l | B l /\ (LENGTH l = LENGTH a)}’ >>
  ‘!d. d IN as ==> (LENGTH d = LENGTH a)’ by simp[Abbr‘as’] >>
  ‘a IN as’ by simp[Abbr‘as’] >>
  ‘?a0. a0 IN as /\ !c. SHORTLEX R c a0 ==> c NOTIN as’
    by metis_tac[WF_SHORTLEX_same_lengths, relationTheory.WF_DEF] >>
  Q.EXISTS_TAC ‘a0’ >> conj_tac
  >- fs[Abbr‘as’] >>
  Q.X_GEN_TAC ‘bb’ >> rpt strip_tac >>
  ‘bb NOTIN as’ by simp[] >>
  ‘LENGTH bb <> LENGTH a’ by (fs[Abbr‘as’] >> metis_tac[]) >>
  ‘LENGTH a < LENGTH bb’ by metis_tac[arithmeticTheory.LESS_OR_EQ] >>
  ‘LENGTH bb <= LENGTH a0’ by metis_tac[SHORTLEX_LENGTH_LE] >>
  ‘LENGTH a0 = LENGTH a’ by metis_tac[] >>
  full_simp_tac (srw_ss() ++ numSimps.ARITH_ss) []);

val LLEX_def = Define‘
  (LLEX R [] l2 <=> l2 <> []) /\
  (LLEX R (h1::t1) l2 <=>
     case l2 of
         [] => F
       | h2::t2 => if R h1 h2 then T
                   else if h1 = h2 then LLEX R t1 t2
                   else F)
’;

val def' = uncurry CONJ (Lib.pair_map SPEC_ALL (CONJ_PAIR LLEX_def))
val LLEX_THM = save_thm(
  "LLEX_THM[simp]",
  CONJ (def' |> Q.INST [‘l2’ |-> ‘[]’]
             |> SIMP_RULE (srw_ss()) [])
       (def' |> Q.INST [‘l2’ |-> ‘h2::t2’]
             |> SIMP_RULE (srw_ss()) []))

val LLEX_MONO = store_thm("LLEX_MONO[mono]",
  “(!x y. R1 x y ==> R2 x y) ==> LLEX R1 x y ==> LLEX R2 x y”,
  STRIP_TAC THEN
  Q.ID_SPEC_TAC‘y’ THEN
  Induct_on‘x’ THEN
  Cases_on‘y’ THEN
  SRW_TAC[][LLEX_THM] THEN
  PROVE_TAC[])

val LLEX_CONG = store_thm
("LLEX_CONG[defncong]",
 “!R l1 l2 R' l1' l2'.
    (l1 = l1') /\ (l2 = l2') /\
    (!a b. MEM a l1' /\ MEM b l2' ==> (R a b = R' a b))
    ==>
    (LLEX R l1 l2 = LLEX R' l1' l2')”,
 GEN_TAC THEN Induct
  THENL [ALL_TAC, GEN_TAC]
   THEN Induct
   THEN SRW_TAC [] []
   THEN SRW_TAC [] [LLEX_THM]
   THEN METIS_TAC[MEM]);

val LLEX_NIL2 = store_thm(
  "LLEX_NIL2[simp]",
  “~LLEX R l []”,
  Cases_on ‘l’ THEN SIMP_TAC (srw_ss()) [LLEX_def]);

val LLEX_transitive = store_thm(
  "LLEX_transitive",
  “transitive R ==> transitive (LLEX R)”,
  SIMP_TAC(srw_ss()) [transitive_def] THEN STRIP_TAC THEN Induct THEN
  SIMP_TAC (srw_ss()) [LLEX_def] THEN
  MAP_EVERY Q.X_GEN_TAC [‘h’, ‘y’, ‘z’] THEN Cases_on ‘y’ THEN
  SIMP_TAC (srw_ss()) [] THEN Cases_on ‘z’ THEN
  SIMP_TAC (srw_ss()) [] THEN METIS_TAC[]);

val LLEX_total = store_thm(
  "LLEX_total",
  “total (RC R) ==> total (RC (LLEX R))”,
  SIMP_TAC (srw_ss()) [total_def, RC_DEF] THEN STRIP_TAC THEN Induct THEN
  SIMP_TAC (srw_ss()) [LLEX_def] THEN MAP_EVERY Q.X_GEN_TAC [‘h’, ‘y’] THEN
  Cases_on ‘y’ THEN SIMP_TAC (srw_ss()) [] THEN METIS_TAC[]);

val LLEX_not_WF = store_thm(
  "LLEX_not_WF",
  “(?a b. R a b) ==> ~WF (LLEX R)”,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [WF_DEF] THEN
  Q.EXISTS_TAC ‘\s. ?n. s = GENLIST (K a) n ++ [b]’ THEN CONJ_TAC
  THEN1 (Q.EXISTS_TAC ‘[b]’ THEN SIMP_TAC (srw_ss()) [] THEN
         Q.EXISTS_TAC ‘0’ THEN SIMP_TAC (srw_ss()) []) THEN
  REWRITE_TAC [GSYM IMP_DISJ_THM] THEN
  SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [SKOLEM_THM] THEN
  Q.EXISTS_TAC ‘SUC’ THEN Induct_on ‘n’ THEN
  ONCE_REWRITE_TAC [GENLIST_CONS] THEN
  ASM_SIMP_TAC (srw_ss()) [LLEX_def]);

val LLEX_EL_THM = store_thm("LLEX_EL_THM",
  “!R l1 l2. LLEX R l1 l2 <=>
              ?n. n <= LENGTH l1 /\ n < LENGTH l2 /\
                  (TAKE n l1 = TAKE n l2) /\
                  (n < LENGTH l1 ==> R (EL n l1) (EL n l2))”,
  GEN_TAC THEN Induct THEN Cases_on‘l2’ THEN SRW_TAC[][] THEN
  SRW_TAC[][EQ_IMP_THM] THEN1 (
    Q.EXISTS_TAC‘0’ THEN SRW_TAC[][] )
  THEN1 (
    Q.EXISTS_TAC‘SUC n’ THEN SRW_TAC[][] ) THEN
  Cases_on‘n’ THEN FULL_SIMP_TAC(srw_ss())[] THEN
  METIS_TAC[])

(*---------------------------------------------------------------------------*)
(* Various lemmas from the CakeML project https://cakeml.org                 *)
(*---------------------------------------------------------------------------*)

(* nub *)

Definition nub_def:
   (nub [] = []) /\
   (nub (x::l) = if MEM x l then nub l else x :: nub l)
End

Theorem nub_NIL[simp] = cj 1 nub_def

Theorem nub_EQ0[simp]:
  nub l = [] <=> l = []
Proof
  Induct_on ‘l’ >> rw[nub_def] >> strip_tac >> fs[]
QED

Theorem nub_set[simp]:
  !l. set (nub l) = set l
Proof Induct >> rw [nub_def, EXTENSION] >> metis_tac []
QED

Theorem all_distinct_nub[simp]: !l. ALL_DISTINCT (nub l)
Proof
  Induct >> rw [nub_def] >> metis_tac [nub_set]
QED

Theorem all_distinct_nub_id:
  !l. ALL_DISTINCT l ==> nub l = l
Proof
  Induct >> simp[nub_def]
QED

Theorem CARD_LIST_TO_SET_EQN:
  CARD (LIST_TO_SET l) = LENGTH (nub l)
Proof
  metis_tac[nub_set, CARD_LIST_TO_SET_ALL_DISTINCT,
            ALL_DISTINCT_CARD_LIST_TO_SET, all_distinct_nub]
QED

(* doesn't need to be simp, as nub_set is *)
Theorem MEM_nub: MEM x (nub l) = MEM x l
Proof simp[]
QED

val filter_helper = Q.prove (
   ‘!x l1 l2.
      ~MEM x l2 ==> (MEM x (FILTER (\x. x NOTIN set l2) l1) = MEM x l1)’,
   Induct_on ‘l1’
   >> rw []
   >> metis_tac []);

val nub_append = Q.store_thm ("nub_append",
   ‘!l1 l2. nub (l1++l2) = nub (FILTER (\x. ~MEM x l2) l1) ++ nub l2’,
   Induct_on ‘l1’
   >> rw [nub_def]
   >> fs []
   >> BasicProvers.FULL_CASE_TAC
   >> rw []
   >> metis_tac [filter_helper]);

Theorem nub_MAP_INJ:
  INJ f (set ls) UNIV ==>
  nub (MAP f ls) = MAP f (nub ls)
Proof
  Induct_on`ls`
  \\ rw[]
  \\ simp[nub_def]
  \\ simp[Once COND_RAND, SimpRHS]
  \\ `INJ f (set ls) UNIV`
  by (
    irule INJ_SUBSET
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[SUBSET_DEF] )
  \\ fs[]
  \\ simp[MEM_MAP]
  \\ fs[INJ_DEF]
  \\ metis_tac[]
QED

val list_to_set_diff = Q.store_thm ("list_to_set_diff",
   ‘!l1 l2. set l2 DIFF set l1 = set (FILTER (\x. x NOTIN set l1) l2)’,
   Induct_on ‘l2’ >> rw []);

val card_eqn_help = Q.prove (
   ‘!l1 l2. CARD (set l2) - CARD (set l1 INTER set l2) =
            CARD (set (FILTER (\x. x NOTIN set l1) l2))’,
   rw [Once INTER_COMM]
   >> SIMP_TAC bool_ss [GSYM CARD_DIFF, FINITE_LIST_TO_SET]
   >> metis_tac [list_to_set_diff]);

val length_nub_append = Q.store_thm ("length_nub_append",
   ‘!l1 l2. LENGTH (nub (l1 ++ l2)) =
            LENGTH (nub l1) + LENGTH (nub (FILTER (\x. ~MEM x l1) l2))’,
   rw [GSYM ALL_DISTINCT_CARD_LIST_TO_SET, all_distinct_nub]
   >> fs [FINITE_LIST_TO_SET, CARD_UNION_EQN]
   >> simp[GSYM card_eqn_help]
   >> ‘CARD (set l1 INTER set l2) <= CARD (set l2)’ suffices_by simp[]
   >> metis_tac [CARD_INTER_LESS_EQ, FINITE_LIST_TO_SET, INTER_COMM]);

val ALL_DISTINCT_DROP = Q.store_thm("ALL_DISTINCT_DROP",
   ‘!ls n. ALL_DISTINCT ls ==> ALL_DISTINCT (DROP n ls)’,
   Induct >> SIMP_TAC (srw_ss()) [] >> rw [DROP_def])

Theorem ALL_DISTINCT_TAKE:
  !ls n. ALL_DISTINCT ls ==> ALL_DISTINCT (TAKE n ls)
Proof
  Induct >> simp[TAKE_def] >> Cases_on ‘n’ >> simp[] >>
  metis_tac[SUBSET_DEF, LIST_TO_SET_TAKE]
QED

fun gvs ths =
  global_simp_tac{elimvars = true, droptrues = true, strip = true,
                  oldestfirst = false} (srw_ss()) ths

Theorem FINITE_BOUNDED_LISTS:
  !s n. FINITE s ==> FINITE { l | set l SUBSET s /\ LENGTH l <= n}
Proof
  Induct_on ‘n’ >> simp[] >> simp[SF CONJ_ss] >> rpt strip_tac >>
  Q.MATCH_ABBREV_TAC ‘FINITE As’ >>
  ‘As = IMAGE (λ(h,t). CONS h t)
              (s CROSS { l | set l SUBSET s /\ LENGTH l <= n}) UNION
        { l | set l SUBSET s /\ LENGTH l <= n}’
    suffices_by simp[] >>
  simp[Abbr‘As’, EXTENSION, pairTheory.EXISTS_PROD] >>
  Q.X_GEN_TAC ‘l’ >> iff_tac >~
  [‘LENGTH l <= SUC n’]
  >- (simp[arithmeticTheory.LE] >> strip_tac >> simp[] >>
      gvs[LENGTH_CONS]) >>
  strip_tac >> simp[]
QED

Theorem FINITE_ALL_DISTINCT_LISTS:
  !s. FINITE s ==> FINITE { l | set l SUBSET s /\ ALL_DISTINCT l}
Proof
  rpt strip_tac >> irule SUBSET_FINITE_I >>
  Q.EXISTS_TAC ‘{l | set l SUBSET s /\ LENGTH l <= CARD s}’ >>
  simp[FINITE_BOUNDED_LISTS] >>
  simp[Once SUBSET_DEF] >> rpt strip_tac >>
  drule_then (assume_tac o SYM) ALL_DISTINCT_CARD_LIST_TO_SET >> simp[] >>
  simp[CARD_SUBSET]
QED

val EXISTS_LIST_EQ_MAP = Q.store_thm("EXISTS_LIST_EQ_MAP",
   ‘!ls f. EVERY (\x. ?y. x = f y) ls ==> ?l. ls = MAP f l’,
   Induct
   >> ASM_SIMP_TAC (srw_ss()) []
   >> rw []
   >> RES_TAC
   >> Q.EXISTS_TAC‘y::l’
   >> ASM_SIMP_TAC (srw_ss()) [])

val LIST_TO_SET_FLAT = Q.store_thm("LIST_TO_SET_FLAT",
   ‘!ls. set (FLAT ls) = BIGUNION (set (MAP set ls))’,
   Induct >> ASM_SIMP_TAC (srw_ss()) [])

val MEM_APPEND_lemma = Q.store_thm("MEM_APPEND_lemma",
   ‘!a b c d x.
      (a ++ [x] ++ b = c ++ [x] ++ d) /\ x NOTIN set b /\ x NOTIN set a ==>
      (a = c) /\ (b = d)’,
   rw [APPEND_EQ_APPEND_MID]
   >> fs []
   >> fs [APPEND_EQ_SING])

val EVERY2_REVERSE = Q.store_thm("EVERY2_REVERSE",
   ‘!R l1 l2. EVERY2 R l1 l2 ==> EVERY2 R (REVERSE l1) (REVERSE l2)’,
   rw [EVERY2_EVERY, EVERY_MEM, FORALL_PROD]
   >> REV_FULL_SIMP_TAC (srw_ss())
         [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_REVERSE]
   >> FIRST_X_ASSUM MATCH_MP_TAC
   >> ASM_SIMP_TAC (arith_ss) []);

val SUM_MAP_PLUS = Q.store_thm("SUM_MAP_PLUS",
   ‘!f g ls. SUM (MAP (\x. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)’,
   NTAC 2 GEN_TAC >> Induct >> simp [SUM])

Theorem TAKE_LENGTH_ID_rwt: !l m. (m = LENGTH l) ==> (TAKE m l = l)
Proof rw [TAKE_LENGTH_ID]
QED

Theorem TAKE_LENGTH_ID_rwt2[simp]:
   !l m. TAKE m l = l <=> LENGTH l <= m
Proof
  Induct >> simp[] >> Cases_on ‘m’ >> simp[]
QED

val ZIP_DROP = Q.store_thm("ZIP_DROP",
   ‘!a b n. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
            (ZIP (DROP n a,DROP n b) = DROP n (ZIP (a,b)))’,
   Induct
   THEN SRW_TAC [] [LENGTH_NIL_SYM, arithmeticTheory.ADD1]
   THEN Cases_on‘b’
   THEN FULL_SIMP_TAC (srw_ss()) [ZIP]
   THEN Cases_on‘0<n’ THEN FULL_SIMP_TAC (srw_ss()) [ZIP]
   THEN FIRST_X_ASSUM MATCH_MP_TAC
   THEN FULL_SIMP_TAC arith_ss [])

val GENLIST_EL = Q.store_thm("GENLIST_EL",
   ‘!ls f n. (n = LENGTH ls) /\ (!i. i < n ==> (f i = EL i ls)) ==>
             (GENLIST f n = ls)’,
   rw [LIST_EQ_REWRITE])

val EVERY2_trans = Q.store_thm("EVERY2_trans",
   ‘(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. EVERY2 R x y /\ EVERY2 R y z ==> EVERY2 R x z’,
   SRW_TAC [] [EVERY2_EVERY, EVERY_MEM, FORALL_PROD]
   THEN REPEAT (Q.PAT_X_ASSUM ‘LENGTH X = Y’ MP_TAC)
   THEN REPEAT STRIP_TAC
   THEN FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP]
   THEN METIS_TAC [])

val EVERY2_sym = Q.store_thm("EVERY2_sym",
   ‘(!x y. R1 x y ==> R2 y x) ==> !x y. EVERY2 R1 x y ==> EVERY2 R2 y x’,
   SRW_TAC [] [EVERY2_EVERY, EVERY_MEM, FORALL_PROD]
   THEN Q.PAT_X_ASSUM ‘LENGTH X = Y’ MP_TAC
   THEN STRIP_TAC
   THEN FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP])

val EVERY2_LUPDATE_same = Q.store_thm("EVERY2_LUPDATE_same",
   ‘!P l1 l2 v1 v2 n.
       P v1 v2 /\ EVERY2 P l1 l2 ==>
       EVERY2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)’,
   GEN_TAC
   THEN Induct
   THEN SRW_TAC [] [LUPDATE_def]
   THEN Cases_on‘n’
   THEN SRW_TAC [] [LUPDATE_def]
   THEN Cases_on‘l2’
   THEN FULL_SIMP_TAC (srw_ss()) [LUPDATE_def])

val EVERY2_refl = Q.store_thm("EVERY2_refl",
   ‘(!x. MEM x ls ==> R x x) ==> (EVERY2 R ls ls)’,
   Induct_on‘ls’ >> rw [])

val EVERY2_THM = Q.store_thm("EVERY2_THM[simp]",
   ‘(!P ys. EVERY2 P [] ys = (ys = [])) /\
    (!P yys x xs. EVERY2 P (x::xs) yys =
       ?y ys. (yys = y::ys) /\ (P x y) /\ (EVERY2 P xs ys)) /\
    (!P xs. EVERY2 P xs [] = (xs = [])) /\
    (!P xxs y ys. EVERY2 P xxs (y::ys) =
       ?x xs. (xxs = x::xs) /\ (P x y) /\ (EVERY2 P xs ys))’,
   REPEAT CONJ_TAC
   THEN GEN_TAC
   THEN TRY (SRW_TAC [] [EVERY2_EVERY, LENGTH_NIL]
             THEN SRW_TAC [] [EQ_IMP_THM]
             THEN NO_TAC)
   THEN Cases
   THEN SRW_TAC [] [EVERY2_EVERY])

val LIST_REL_trans = Q.store_thm("LIST_REL_trans",
   ‘!l1 l2 l3.
      (!n. n < LENGTH l1 /\ R (EL n l1) (EL n l2) /\
       R (EL n l2) (EL n l3) ==> R (EL n l1) (EL n l3)) /\
      LIST_REL R l1 l2 /\ LIST_REL R l2 l3 ==> LIST_REL R l1 l3’,
   Induct
   >> simp []
   >> rw [LIST_REL_CONS1]
   >> fs [LIST_REL_CONS1]
   >> rw []
   THEN1 (FIRST_X_ASSUM (Q.SPEC_THEN ‘0’ MP_TAC) >> rw [])
   >> FIRST_X_ASSUM MATCH_MP_TAC
   >> Q.RENAME_TAC [‘LIST_REL _ l1 l2’, ‘LIST_REL _ l2 l3’]
   >> Q.EXISTS_TAC‘l2’
   >> rw []
   >> FIRST_X_ASSUM (Q.SPEC_THEN ‘SUC n’ MP_TAC)
   >> simp []);

Theorem LIST_REL_eq[simp,quotient_simp]:
  LIST_REL (=) = (=)
Proof
  simp[FUN_EQ_THM] >> Induct >> rpt gen_tac >>
  Q.RENAME_TAC [‘LIST_REL _ _ ys’] >> Cases_on ‘ys’ >> fs []
QED

Theorem LIST_REL_MEM_IMP:
  !xs ys P x. LIST_REL P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y
Proof  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]
QED

Theorem LIST_REL_MEM_IMP_R:
  !xs ys P y. LIST_REL P xs ys /\ MEM y ys ==> ?x. MEM x xs /\ P x y
Proof  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]
QED

Theorem LIST_REL_SNOC:
  (LIST_REL R (SNOC x xs) yys <=>
      ?y ys. (yys = SNOC y ys) /\ LIST_REL R xs ys /\ R x y) /\
  (LIST_REL R xxs (SNOC y ys) <=>
      ?x xs. (xxs = SNOC x xs) /\ LIST_REL R xs ys /\ R x y)
Proof
   simp[EQ_IMP_THM, PULL_EXISTS, SNOC_APPEND] >> rpt strip_tac >>
   fs[LIST_REL_SPLIT1, LIST_REL_SPLIT2] >> metis_tac[]
QED

Theorem LIST_REL_APPEND_IMP:
  !xs ys xs1 ys1.
      LIST_REL P (xs ++ xs1) (ys ++ ys1) /\ (LENGTH xs = LENGTH ys) ==>
      LIST_REL P xs ys /\ LIST_REL P xs1 ys1
Proof  Induct >> Cases_on ‘ys’ >> FULL_SIMP_TAC (srw_ss()) [] >> METIS_TAC []
QED

Theorem LIST_REL_APPEND:
   EVERY2 R l1 l2 /\ EVERY2 R l3 l4 <=>
     EVERY2 R (l1 ++ l3) (l2 ++ l4) /\
     (LENGTH l1 = LENGTH l2) /\ (LENGTH l3 = LENGTH l4)
Proof
  rw[LIST_REL_EL_EQN, EL_APPEND_EQN, EQ_IMP_THM] >> rw[]
  >- (first_x_assum irule >> simp[])
  >- (first_x_assum (Q.SPEC_THEN ‘n’ mp_tac) >> simp[])
  >- (first_x_assum (Q.SPEC_THEN ‘LENGTH l2 + n’ mp_tac) >> simp[])
QED

Theorem LIST_REL_APPEND_suff:
  EVERY2 R l1 l2 /\ EVERY2 R l3 l4 ==> EVERY2 R (l1 ++ l3) (l2 ++ l4)
Proof metis_tac[LIST_REL_APPEND]
QED

Theorem LIST_REL_APPEND_EQ:
  (LENGTH x1 = LENGTH x2) ==>
  (LIST_REL R (x1 ++ y1) (x2 ++ y2) <=> LIST_REL R x1 x2 /\ LIST_REL R y1 y2)
Proof
  metis_tac[LIST_REL_APPEND_IMP, EVERY2_LENGTH, LIST_REL_APPEND_suff]
QED

Theorem LIST_REL_MAP_inv_image:
  LIST_REL R (MAP f l1) (MAP f l2) = LIST_REL (inv_image R f) l1 l2
Proof
  rw[LIST_REL_EL_EQN, EQ_IMP_THM, EL_MAP, LENGTH_MAP] >> metis_tac[EL_MAP]
QED

val SWAP_REVERSE = Q.store_thm("SWAP_REVERSE",
   ‘!l1 l2. (l1 = REVERSE l2) = (l2 = REVERSE l1)’,
   SRW_TAC [] [EQ_IMP_THM])

val SWAP_REVERSE_SYM = Q.store_thm("SWAP_REVERSE_SYM",
   ‘!l1 l2. (REVERSE l1 = l2) = (l1 = REVERSE l2)’,
   metis_tac [SWAP_REVERSE])

val BIGUNION_IMAGE_set_SUBSET = Q.store_thm("BIGUNION_IMAGE_set_SUBSET",
   ‘(BIGUNION (IMAGE f (set ls)) SUBSET s) = (!x. MEM x ls ==> f x SUBSET s)’,
   SRW_TAC [DNF_ss] [SUBSET_DEF] THEN METIS_TAC [])

val IMAGE_EL_count_LENGTH = Q.store_thm("IMAGE_EL_count_LENGTH",
   ‘!f ls. IMAGE (\n. f (EL n ls)) (count (LENGTH ls)) = IMAGE f (set ls)’,
   rw [EXTENSION, MEM_EL] >> PROVE_TAC [])

val GENLIST_EL_MAP = Q.store_thm("GENLIST_EL_MAP",
   ‘!f ls. GENLIST (\n. f (EL n ls)) (LENGTH ls) = MAP f ls’,
   GEN_TAC >> Induct >> rw [GENLIST_CONS, o_DEF])

val LENGTH_FILTER_LEQ_MONO = Q.store_thm("LENGTH_FILTER_LEQ_MONO",
   ‘!P Q. (!x. P x ==> Q x) ==>
          !ls. (LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls))’,
   REPEAT GEN_TAC
   >> STRIP_TAC
   >> Induct
   >> rw []
   >> FULL_SIMP_TAC arith_ss []
   >> PROVE_TAC [])

val LIST_EQ_MAP_PAIR = Q.store_thm("LIST_EQ_MAP_PAIR",
   ‘!l1 l2.
     (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)’,
   SRW_TAC []
     [MAP_EQ_EVERY2, EVERY2_EVERY, EVERY_MEM, LIST_EQ_REWRITE, FORALL_PROD]
   THEN REV_FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP]
   THEN METIS_TAC [pair_CASES, PAIR_EQ])

val TAKE_SUM = Q.store_thm("TAKE_SUM",
   ‘!n m l. TAKE (n + m) l = TAKE n l ++ TAKE m (DROP n l)’,
   Induct_on ‘l’ >> simp[TAKE_def] >> rw[] >> simp[] >>
   ‘m + n - 1 = (n - 1) + m’ by simp[] >>
   ASM_REWRITE_TAC[]);

val ALL_DISTINCT_FILTER_EL_IMP = Q.store_thm("ALL_DISTINCT_FILTER_EL_IMP",
   ‘!P l n1 n2.
      ALL_DISTINCT (FILTER P l) /\ n1 < LENGTH l /\ n2 < LENGTH l /\
      (P (EL n1 l)) /\ (EL n1 l = EL n2 l) ==> (n1 = n2)’,
   GEN_TAC
   THEN Induct
   THEN1 SRW_TAC [] []
   THEN SRW_TAC [] []
   THEN FULL_SIMP_TAC (srw_ss()) [MEM_FILTER]
   THEN1 PROVE_TAC []
   THEN Cases_on ‘n1’
   THEN Cases_on ‘n2’
   THEN FULL_SIMP_TAC (srw_ss()) [MEM_EL]
   THEN PROVE_TAC [])

val FLAT_EQ_NIL = Q.store_thm("FLAT_EQ_NIL",
   ‘!ls. (FLAT ls = []) = (EVERY ($= []) ls)’,
   Induct >> SRW_TAC [] [EQ_IMP_THM] >> rw [APPEND]);

Theorem FLAT_EQ_NIL' :
    FLAT l = [] <=> !e. MEM e l ==> e = []
Proof simp[FLAT_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem FLAT_EQ_SING:
  FLAT l = [x] <=>
    ?p s. l = p ++ [[x]] ++ s /\ FLAT p = [] /\ FLAT s = []
Proof
  Induct_on `l` >> simp[] >> simp[APPEND_EQ_CONS] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> metis_tac[]
QED

Theorem FLAT_EQ_APPEND:
  FLAT l = x ++ y <=>
    (?p s. l = p ++ s /\ x = FLAT p /\ y = FLAT s) \/
    (?p s ip is.
       l = p ++ [ip ++ is] ++ s /\ ip <> [] /\ is <> [] /\
       x = FLAT p ++ ip /\
       y = is ++ FLAT s)
Proof
  reverse eq_tac >- (rw[] >> rw[APPEND_ASSOC, FLAT_APPEND]) >>
  map_every qid_spec_tac [`y`,`x`,`l`] >> Induct_on `l` >- simp[] >>
  simp[] >> map_every qx_gen_tac [`h`, `x`, `y`] >>
  simp[APPEND_EQ_APPEND] >>
  disch_then (DISJ_CASES_THEN (qxch `m` strip_assume_tac))
  >- (Cases_on `x = []`
      >- (fs[] >> map_every qexists_tac [`[]`, `m::l`] >> simp[]) >>
      Cases_on `m = []`
      >- (fs[] >> disj1_tac >> map_every qexists_tac [`[x]`, `l`] >>
          simp[]) >>
      disj2_tac >>
      map_every qexists_tac [`[]`, `l`, `x`, `m`] >> simp[]) >>
  `(?p s. l = p ++ s /\ FLAT p = m /\ FLAT s = y) \/
   (?p s ip is.
       l = p ++ [ip ++ is] ++ s /\ m = FLAT p ++ ip /\ ip <> [] /\ is <> [] /\
       y = is ++ FLAT s)` by metis_tac[]
  >- (disj1_tac >> map_every qexists_tac [`h::p`, `s`] >> simp[]) >>
  disj2_tac >> map_every qexists_tac [`h::p`, `s`] >> simp[APPEND_ASSOC] >>
  map_every qexists_tac [`ip`, `is`] >> rw []
QED

val ALL_DISTINCT_MAP_INJ = Q.store_thm("ALL_DISTINCT_MAP_INJ",
   ‘!ls f. (!x y. MEM x ls /\ MEM y ls /\ (f x = f y) ==> (x = y)) /\
           ALL_DISTINCT ls ==> ALL_DISTINCT (MAP f ls)’,
   Induct THEN SRW_TAC [] [MEM_MAP] THEN PROVE_TAC [])

val LENGTH_o_REVERSE = Q.store_thm("LENGTH_o_REVERSE",
   ‘(LENGTH o REVERSE = LENGTH) /\
    (LENGTH o REVERSE o f = LENGTH o f)’,
   SRW_TAC [] [FUN_EQ_THM])

val REVERSE_o_REVERSE = Q.store_thm("REVERSE_o_REVERSE",
   ‘(REVERSE o REVERSE o f = f)’,
   SRW_TAC [] [FUN_EQ_THM])

val GENLIST_PLUS_APPEND = Q.store_thm("GENLIST_PLUS_APPEND",
   ‘GENLIST ($+ a) n1 ++ GENLIST ($+ (n1 + a)) n2 = GENLIST ($+ a) (n1 + n2)’,
   rw [Once arithmeticTheory.ADD_SYM, SimpRHS]
   >> RW_TAC arith_ss [GENLIST_APPEND]
   >> SRW_TAC [ETA_ss] [arithmeticTheory.ADD_ASSOC])

val LIST_TO_SET_GENLIST = Q.store_thm("LIST_TO_SET_GENLIST",
   ‘!f n. LIST_TO_SET (GENLIST f n) = IMAGE f (count n)’,
   SRW_TAC [] [EXTENSION, MEM_GENLIST] THEN PROVE_TAC [])

val MEM_ZIP_MEM_MAP = Q.store_thm("MEM_ZIP_MEM_MAP",
   ‘(LENGTH (FST ps) = LENGTH (SND ps)) /\
    MEM p (ZIP ps) ==> MEM (FST p) (FST ps) /\ MEM (SND p) (SND ps)’,
   Cases_on ‘p’
   >> Cases_on ‘ps’
   >> SRW_TAC [] []
   >> REV_FULL_SIMP_TAC (srw_ss()) [MEM_ZIP, MEM_EL]
   >> PROVE_TAC [])

val DISJOINT_GENLIST_PLUS = Q.store_thm("DISJOINT_GENLIST_PLUS",
   ‘DISJOINT x (set (GENLIST ($+ n) (a + b))) ==>
    DISJOINT x (set (GENLIST ($+ n) a)) /\
    DISJOINT x (set (GENLIST ($+ (n + a)) b))’,
   rw [GSYM GENLIST_PLUS_APPEND]
   >> metis_tac [DISJOINT_SYM, arithmeticTheory.ADD_SYM])

val EVERY2_MAP = Q.store_thm("EVERY2_MAP",
   `(EVERY2 P (MAP f l1) l2 = EVERY2 (\x y. P (f x) y) l1 l2) /\
    (EVERY2 Q l1 (MAP g l2) = EVERY2 (\x y. Q x (g y)) l1 l2)`,
   rw [EVERY2_EVERY, LENGTH_MAP]
   >> Cases_on `LENGTH l1 = LENGTH l2`
   >> fs []
   >> rw [ZIP_MAP, EVERY_MEM, MEM_MAP]
   >> SRW_TAC [DNF_ss] [pairTheory.FORALL_PROD, LENGTH_MAP, MEM_ZIP]);

val exists_list_GENLIST = Q.store_thm("exists_list_GENLIST",
   ‘(?ls. P ls) = (?n f. P (GENLIST f n))’,
   rw [EQ_IMP_THM]
   THEN1 (MAP_EVERY Q.EXISTS_TAC [‘LENGTH ls’,‘combin$C EL ls’]
          >> Q.MATCH_ABBREV_TAC ‘P ls2’
          >> Q_TAC SUFF_TAC ‘ls2 = ls’
          THEN1 rw []
          >> rw [LIST_EQ_REWRITE, Abbr‘ls2’])
   >> PROVE_TAC [])

val EVERY_MEM_MONO = Q.store_thm("EVERY_MEM_MONO",
   ‘!P Q l. (!x. MEM x l /\ P x ==> Q x) /\ EVERY P l ==> EVERY Q l’,
   NTAC 2 GEN_TAC >> Induct >> rw [])

val EVERY2_MEM_MONO = Q.store_thm("EVERY2_MEM_MONO",
   ‘!P Q l1 l2. (!x. MEM x (ZIP (l1,l2)) /\ UNCURRY P x ==> UNCURRY Q x) /\
                EVERY2 P l1 l2 ==> EVERY2 Q l1 l2’,
   rw [EVERY2_EVERY] >> MATCH_MP_TAC EVERY_MEM_MONO >> PROVE_TAC [])

val mem_exists_set = Q.store_thm ("mem_exists_set",
   ‘!x y l. MEM (x,y) l ==> ?z. (x = FST z) /\ z IN set l’,
   Induct_on ‘l’
   >> rw []
   >> metis_tac [FST]);

val every_zip_snd = Q.store_thm ("every_zip_snd",
   ‘!l1 l2 P.
     (LENGTH l1 = LENGTH l2) ==>
     (EVERY (\x. P (SND x)) (ZIP (l1,l2)) = EVERY P l2)’,
   Induct_on ‘l1’
   >> rw []
   >> TRY(Cases_on ‘l2’)
   >> fs [ZIP]);

val every_zip_fst = Q.store_thm ("every_zip_fst",
   ‘!l1 l2 P. (LENGTH l1 = LENGTH l2) ==>
              (EVERY (\x. P (FST x)) (ZIP (l1,l2)) = EVERY P l1)’,
   Induct_on ‘l1’
   >> rw []
   >> TRY(Cases_on ‘l2’)
   >> fs [ZIP]);

val el_append3 = Q.store_thm ("el_append3",
   ‘!l1 x l2. EL (LENGTH l1) (l1++ [x] ++ l2) = x’,
   Induct_on ‘l1’
   >> rw []
   >> rw []);

val lupdate_append = Q.store_thm ("lupdate_append",
   ‘!x n l1 l2.
       n < LENGTH l1 ==> (LUPDATE x n (l1++l2) = LUPDATE x n l1 ++ l2)’,
   Induct_on ‘l1’
   >> rw []
   >> Cases_on ‘n’
   >> rw [LUPDATE_def]
   >> fs []);

val lupdate_append2 = Q.store_thm ("lupdate_append2",
   ‘!v l1 x l2 l3. LUPDATE v (LENGTH l1) (l1++[x]++l2) = l1++[v]++l2’,
   Induct_on ‘l1’ >> rw [LUPDATE_def])

val HD_REVERSE = store_thm ("HD_REVERSE",
  “!x. x <> [] ==> (HD (REVERSE x) = LAST x)”,
  REPEAT strip_tac >>
  Induct_on ‘x’ THEN1 fs[] >>
  rw[LAST_DEF] >>
  Cases_on ‘REVERSE x’ THEN1 fs[] >>
  fs[]);

val LAST_REVERSE = Q.store_thm("LAST_REVERSE",
   ‘!ls. ls <> [] ==> (LAST (REVERSE ls) = HD ls)’,
   Induct >> simp [])

val NOT_NIL_EQ_LENGTH_NOT_0 = store_thm ( "NOT_NIL_EQ_LENGTH_NOT_0",
  “x <> [] <=> (0 < LENGTH x)”,
  Cases_on ‘x’ >> rw[]);

val last_drop = Q.store_thm ("last_drop",
  ‘!l n. n < LENGTH l ==> (LAST (DROP n l) = LAST l)’,
  Induct >> rw [DROP_def] >>
  Q.SPEC_THEN‘l’FULL_STRUCT_CASES_TAC list_CASES >> fs [] >>
  FULL_SIMP_TAC (srw_ss()++numSimps.ARITH_ss) [] >> SRW_TAC[] [] >>
  FIRST_X_ASSUM (Q.SPEC_THEN ‘n - 1’ MP_TAC) >>
  simp[]);

val dropWhile_def = Define‘
   (dropWhile P [] = []) /\
   (dropWhile P (h::t) = if P h then dropWhile P t else (h::t))’
val _ = export_rewrites ["dropWhile_def"]

val dropWhile_splitAtPki = Q.store_thm("dropWhile_splitAtPki",
  ‘!P. dropWhile P = splitAtPki (combin$C (K o $~ o P)) (K I)’,
   GEN_TAC
   >> simp [FUN_EQ_THM]
   >> Induct
   >> simp [splitAtPki_def]
   >> rw []
   >> AP_THM_TAC
   >> Q.MATCH_ABBREV_TAC ‘f a b = f a' b'’
   >> ‘b = b'’ by (markerLib.UNABBREV_ALL_TAC >> simp [FUN_EQ_THM])
   >> ‘a = a'’ by (markerLib.UNABBREV_ALL_TAC >> simp [FUN_EQ_THM])
   >> REV_FULL_SIMP_TAC (srw_ss()) [])

val dropWhile_eq_nil = Q.store_thm("dropWhile_eq_nil",
   ‘!P ls. (dropWhile P ls = []) <=> EVERY P ls’,
   GEN_TAC >> Induct >> simp [] >> rw [])

val MEM_dropWhile_IMP = Q.store_thm("MEM_dropWhile_IMP",
   ‘!P ls x. MEM x (dropWhile P ls) ==> MEM x ls’,
   GEN_TAC >> Induct >> simp [] >> rw [])

val HD_dropWhile = Q.store_thm("HD_dropWhile",
   ‘!P ls. EXISTS ($~ o P) ls ==> ~ P (HD (dropWhile P ls))’,
   GEN_TAC >> Induct >> simp [] >> rw [])

val LENGTH_dropWhile_LESS_EQ = Q.store_thm("LENGTH_dropWhile_LESS_EQ",
   ‘!P ls. LENGTH (dropWhile P ls) <= LENGTH ls’,
   GEN_TAC >> Induct >> simp [] >> rw [] >> simp [])

val dropWhile_APPEND_EVERY = Q.store_thm("dropWhile_APPEND_EVERY",
   ‘!P l1 l2. EVERY P l1 ==> (dropWhile P (l1 ++ l2) = dropWhile P l2)’,
   GEN_TAC >> Induct >> simp [dropWhile_def])

val dropWhile_APPEND_EXISTS = Q.store_thm("dropWhile_APPEND_EXISTS",
   ‘!P l1 l2. EXISTS ($~ o P) l1 ==>
              (dropWhile P (l1 ++ l2) = dropWhile P l1 ++ l2)’,
   GEN_TAC >> Induct >> simp [dropWhile_def] >> rw [])

local
  val fs = FULL_SIMP_TAC (srw_ss()++numSimps.ARITH_ss)
  val rw = SRW_TAC [numSimps.ARITH_ss]
in
val EL_LENGTH_dropWhile_REVERSE = Q.store_thm("EL_LENGTH_dropWhile_REVERSE",
   ‘!P ls k. LENGTH (dropWhile P (REVERSE ls)) <= k /\ k < LENGTH ls ==>
             P (EL k ls)’,
   GEN_TAC
   >> Induct
   >> simp [LENGTH]
   >> rw []
   >> Cases_on ‘k’
   >> fs [LENGTH_NIL, dropWhile_eq_nil, EVERY_APPEND]
   >> FIRST_X_ASSUM MATCH_MP_TAC
   >> simp []
   >> Cases_on ‘EVERY P (REVERSE ls)’
   THEN1 (fs [dropWhile_APPEND_EVERY, GSYM dropWhile_eq_nil])
   >> fs [NOT_EVERY, dropWhile_APPEND_EXISTS, arithmeticTheory.ADD1])
end

val IMP_EVERY_LUPDATE = store_thm("IMP_EVERY_LUPDATE",
  “!xs h i. P h /\ EVERY P xs ==> EVERY P (LUPDATE h i xs)”,
  Induct THEN fs [LUPDATE_def] THEN REPEAT STRIP_TAC
  THEN Cases_on ‘i’ THEN fs [LUPDATE_def]);

val MAP_APPEND_MAP_EQ = store_thm("MAP_APPEND_MAP_EQ",
  “!xs ys.
      ((MAP f1 xs ++ MAP g1 ys) = (MAP f2 xs ++ MAP g2 ys)) <=>
      (MAP f1 xs = MAP f2 xs) /\ (MAP g1 ys = MAP g2 ys)”,
  Induct THEN fs [] THEN METIS_TAC []);

val LUPDATE_SOME_MAP = store_thm("LUPDATE_SOME_MAP",
  “!xs n f h.
      LUPDATE (SOME (f h)) n (MAP (OPTION_MAP f) xs) =
      MAP (OPTION_MAP f) (LUPDATE (SOME h) n xs)”,
  Induct THEN1 (fs [LUPDATE_def]) THEN
  Cases_on ‘n’ THEN fs [LUPDATE_def]);

val ZIP_EQ_NIL = store_thm("ZIP_EQ_NIL",
  “!l1 l2. (LENGTH l1 = LENGTH l2) ==>
            ((ZIP (l1,l2) = []) <=> ((l1 = []) /\ (l2 = [])))”,
  REPEAT GEN_TAC >> Cases_on‘l1’ >> rw[LENGTH_NIL_SYM,ZIP] >> Cases_on‘l2’ >>
  fs[ZIP])

val LUPDATE_SAME = store_thm("LUPDATE_SAME",
  “!n ls. n < LENGTH ls ==> (LUPDATE (EL n ls) n ls = ls)”,
  rw[LIST_EQ_REWRITE,EL_LUPDATE]>>rw[])

(* end CakeML lemmas *)

(* u is unique in L, learnt from Robert Beers <robert@beers.org> *)
val UNIQUE_DEF = new_definition ("UNIQUE_DEF",
  “UNIQUE e L = ?L1 L2. (L1 ++ [e] ++ L2 = L) /\ ~MEM e L1 /\ ~MEM e L2”);

local
    fun take ts = MAP_EVERY Q.EXISTS_TAC ts;    (* from HOL mizar mode *)
    val Know = Q_TAC KNOW_TAC;                  (* from util_prob *)
    val Suff = Q_TAC SUFF_TAC;                  (* from util_prob *)
    fun K_TAC _ = ALL_TAC;                      (* from util_prob *)
    val KILL_TAC = POP_ASSUM_LIST K_TAC;        (* from util_prob *)
    fun wrap a = [a];                           (* from util_prob *)
    val Rewr = DISCH_THEN (REWRITE_TAC o wrap); (* from util_prob *)
in
(* alternative definition of UNIQUE, by Chun Tian (binghe) *)
val UNIQUE_FILTER = store_thm (
   "UNIQUE_FILTER", “!e L. UNIQUE e L = (FILTER ($= e) L = [e])”,
    rpt GEN_TAC
 >> REWRITE_TAC [UNIQUE_DEF]
 >> EQ_TAC >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘P = L’ (REWRITE_TAC o wrap o SYM) \\
      REWRITE_TAC [FILTER_APPEND_DISTRIB] \\
      Know ‘((FILTER ($= e) L1) = []) /\ ((FILTER ($= e) L2) = [])’
      >- ( REWRITE_TAC [GSYM NULL_EQ] \\
           REWRITE_TAC [NULL_FILTER] \\
           rpt STRIP_TAC >> FULL_SIMP_TAC arith_ss [] ) \\
      Rewr \\
      REWRITE_TAC [APPEND, APPEND_NIL, FILTER],
      (* goal 2 (of 2) *)
      Know ‘MEM e L’
      >- ( ‘FILTER ($= e) L <> []’ by PROVE_TAC [NOT_CONS_NIL] \\
           FULL_SIMP_TAC arith_ss [FILTER_NEQ_NIL] ) \\
      REWRITE_TAC [MEM_SPLIT] >> rpt STRIP_TAC \\
      take [‘l1’, ‘l2’] >> FULL_SIMP_TAC arith_ss [] \\
      CONJ_TAC >- ( KILL_TAC >> REWRITE_TAC [GSYM APPEND_ASSOC] \\
                    SIMP_TAC arith_ss [APPEND, APPEND_11] ) \\
      POP_ASSUM K_TAC \\
      POP_ASSUM MP_TAC \\
      SIMP_TAC arith_ss [FILTER_APPEND_DISTRIB, FILTER] \\
      REWRITE_TAC [APPEND_EQ_SING] \\
      rpt STRIP_TAC \\
      FULL_SIMP_TAC arith_ss [NOT_CONS_NIL, FILTER_APPEND_DISTRIB, FILTER,
                              APPEND_eq_NIL, CONS_11] ]);

(* alternative definition of UNIQUE, learnt from Scott Owens and Anthony Fox *)
val UNIQUE_LENGTH_FILTER = store_thm (
   "UNIQUE_LENGTH_FILTER", “!e L. UNIQUE e L = (LENGTH (FILTER ($= e) L) = 1)”,
    rpt GEN_TAC
 >> REWRITE_TAC [UNIQUE_FILTER]
 >> EQ_TAC >> DISCH_TAC
 >- ( ASM_REWRITE_TAC [] >> REWRITE_TAC [LENGTH] >> ACCEPT_TAC (SYM ONE) )
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [ONE, LENGTH_EQ_NUM]
 >> SIMP_TAC arith_ss []
 >> rpt STRIP_TAC
 >> Cases_on ‘e = h’ >- ASM_REWRITE_TAC []
 >> ASM_REWRITE_TAC []
 >> FULL_SIMP_TAC arith_ss [CONS_11]
 >> Suff ‘MEM e (FILTER ($= e) L)’
 >- ( DISCH_TAC \\
      REV_FULL_SIMP_TAC (arith_ss ++ pred_setSimps.PRED_SET_ss) [LIST_TO_SET] )
 >> REWRITE_TAC [MEM_FILTER]
 >> Know ‘FILTER ($= e) L <> []’ >- FULL_SIMP_TAC arith_ss [NOT_CONS_NIL]
 >> KILL_TAC
 >> REWRITE_TAC [FILTER_NEQ_NIL]
 >> rpt STRIP_TAC
 >> ASM_REWRITE_TAC []);
end; (* local *)

(* OPT_MMAP : ('a -> 'b option) -> 'a list -> 'b list option *)
Definition OPT_MMAP_def[simp]:
  (OPT_MMAP f [] = SOME []) /\
  (OPT_MMAP f (h0::t0) =
     OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t))))
End

Theorem OPT_MMAP_cong[defncong]:
  !f1 f2 x1 x2.
    x1 = x2 /\ (!a. MEM a x2 ==> f1 a = f2 a) ==>
    OPT_MMAP f1 x1 = OPT_MMAP f2 x2
Proof
  ntac 2 gen_tac \\ Induct \\ rw[] \\ computeLib.EVAL_TAC
  \\ FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) []
QED

val LAST_compute = Q.store_thm("LAST_compute",
   ‘(!x. LAST [x] = x) /\
    (!h1 h2 t. LAST (h1::h2::t) = LAST (h2::t))’,
   SRW_TAC [] [LAST_DEF]);

val TAKE_compute = Q.prove(
   ‘(!l. TAKE 0 l = []) /\
    (!n. TAKE (SUC n) [] = []) /\
    (!n h t. TAKE (SUC n) (h::t) = h :: TAKE n t)’,
   SRW_TAC [] []);

val DROP_compute = Q.prove(
   ‘(!l. DROP 0 l = l) /\
    (!n. DROP (SUC n) [] = []) /\
    (!n h t. DROP (SUC n) (h::t) = DROP n t)’,
   SRW_TAC [] []);

val TAKE_compute =
   Theory.save_thm("TAKE_compute", numLib.SUC_RULE TAKE_compute);

val DROP_compute =
   Theory.save_thm("DROP_compute", numLib.SUC_RULE DROP_compute);

Theorem DROP_TAKE:
  !xs n k. DROP n (TAKE k xs) = TAKE (k - n) (DROP n xs)
Proof
  Induct \\ simp_tac bool_ss [TAKE_def,DROP_def]
  \\ rpt strip_tac \\ rpt IF_CASES_TAC
  \\ asm_simp_tac bool_ss [TAKE_def,DROP_def,TAKE_0,arithmeticTheory.SUB_0]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ numLib.DECIDE_TAC
QED

Theorem TAKE_DROP_SWAP:
  !xs k n. TAKE k (DROP n xs) = DROP n (TAKE (k + n) xs)
Proof
  rewrite_tac [DROP_TAKE,arithmeticTheory.ADD_SUB]
QED

(* ----------------------------------------------------------------------
    versions of constants with option outputs rather than unspecified

      oHD : 'a list -> 'a option
      oEL : num -> 'a list -> 'a option

   ---------------------------------------------------------------------- *)

val oHD_def = Define‘oHD l = case l of [] => NONE | h::_ => SOME h’
val oHD_thm = Q.store_thm("oHD_thm[simp]",
  ‘(oHD [] = NONE) /\ (oHD (h::t) = SOME h)’,
  rw[oHD_def]);

val oEL_def = Define‘
  (oEL n [] = NONE) /\
  (oEL n (x::xs) = if n = 0 then SOME x else oEL (n - 1) xs)
’;

val oEL_THM = Q.store_thm(
  "oEL_THM",
  ‘!xs n. oEL n xs = if n < LENGTH xs then SOME (EL n xs) else NONE’,
  Induct >> fs[oEL_def] >> rw[] >> fs[]
  >- (Q.RENAME_TAC [‘n < SUC (LENGTH xs)’] >> Cases_on ‘n’ >> fs[]) >>
  rw[] >> ASSUME_TAC (numLib.DECIDE “!x. 1 + x = SUC x”) >>
  fs[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  METIS_TAC[ONE, arithmeticTheory.LESS_LESS_SUC]);

val oEL_EQ_EL = Q.store_thm(
  "oEL_EQ_EL",
  ‘!xs n y. (oEL n xs = SOME y) <=> n < LENGTH xs /\ (y = EL n xs)’,
  simp[oEL_THM] >> METIS_TAC[]);

val oEL_DROP = Q.store_thm(
  "oEL_DROP",
  ‘oEL n (DROP m xs) = oEL (m + n) xs’,
  MAP_EVERY Q.ID_SPEC_TAC [‘n’, ‘m’, ‘xs’] >> Induct_on ‘xs’ >>
  simp[DROP_def, oEL_def] >> rw[oEL_def] >> fs[] >>
  Q.RENAME_TAC [‘m - 1 + n’] >>
  ‘m - 1 + n = m + n - 1’ suffices_by simp[] >>
  Q.UNDISCH_THEN ‘m <> 0’ MP_TAC >> numLib.ARITH_TAC);

val oEL_TAKE_E = Q.store_thm(
  "oEL_TAKE_E",
  ‘(oEL n (TAKE m xs) = SOME x) ==> (oEL n xs = SOME x)’,
  MAP_EVERY Q.ID_SPEC_TAC [‘n’, ‘m’, ‘xs’] >> Induct_on ‘xs’ >>
  simp[TAKE_def, oEL_def] >> rw[oEL_def] >> RES_TAC);

val oEL_LUPDATE = Q.store_thm(
  "oEL_LUPDATE",
  ‘!xs i n x. oEL n (LUPDATE x i xs) =
               if i <> n then oEL n xs else
               if i < LENGTH xs then SOME x else NONE’,
  Induct >> fs[oEL_def,LUPDATE_def] >>
  Cases_on ‘i’ >> rw[oEL_def,LUPDATE_def] >> fs[] >> rw[] >>
  fs[numLib.DECIDE “!x. SUC (x - 1) <> x <=> (x = 0)”,
     numLib.DECIDE “!x. 1 + x = SUC x”]);

(* ----------------------------------------------------------------------
    adjacent : 'a list -> 'a -> 'a -> bool

    adjacent L a b is true if b immediately follows a somewhere in list L
   ---------------------------------------------------------------------- *)

Inductive adjacent:
  (!a b t. adjacent (a::b::t) a b) /\
  (!a b h t. adjacent t a b ==> adjacent (h::t) a b)
End

Theorem adjacent_thm[simp]:
  adjacent [] a b = F /\
  adjacent [e] a b = F /\
  adjacent (a::b::t) a b = T
Proof
  rpt conj_tac >> simp[Once adjacent_cases] >> Induct_on ‘adjacent’ >>
  simp[]
QED

Theorem adjacent_iff:
  adjacent (h1::h2::t) a b <=> h1 = a /\ h2 = b \/ adjacent (h2::t) a b
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM, adjacent_rules] >>
  map_every Q.ID_SPEC_TAC [‘a’, ‘b’, ‘h1’, ‘h2’, ‘t’] >>
  Induct_on ‘adjacent’ >> simp[]
QED

Theorem adjacent_EL:
  adjacent L a b <=> ?i. i + 1 < LENGTH L /\ a = EL i L /\ b = EL (i + 1) L
Proof
  eq_tac
  >- (Induct_on ‘adjacent’ >> simp[PULL_EXISTS] >> rw[]
      >- (Q.EXISTS_TAC ‘0’ >> simp[]) >>
      Q.RENAME_TAC [‘i + 1 < LENGTH L’] >> Q.EXISTS_TAC ‘SUC i’ >>
      simp[ADD_CLAUSES]) >>
  simp[PULL_EXISTS] >> Q.ID_SPEC_TAC ‘L’ >> Induct_on ‘i’ >>
  Cases >> simp[]
  >- (Q.RENAME_TAC [‘1 < SUC (LENGTH L)’] >> Cases_on ‘L’ >> simp[]) >>
  simp[ADD_CLAUSES, adjacent_rules]
QED

Theorem adjacent_MAP:
  !xs a b f.
    adjacent (MAP f xs) a b <=> ?x y. adjacent xs x y /\ a = f x /\ b = f y
Proof
  Induct_on ‘xs’ >> simp[] >> Cases_on ‘xs’ >> gvs[] >>
  simp[adjacent_iff, SF DNF_ss] >> metis_tac[]
QED

Theorem adjacent_MEM:
  !xs a b. adjacent xs a b ==> MEM a xs /\ MEM b xs
Proof
  simp[MEM_EL, adjacent_EL, PULL_EXISTS] >> rpt strip_tac >>
  rpt (irule_at Any EQ_REFL) >> simp[]
QED

Theorem adjacent_ps_append:
  !xs a b. adjacent xs a b <=> ?p s. xs = p ++ [a;b] ++ s
Proof
  simp[adjacent_EL, PULL_EXISTS, EQ_IMP_THM] >> rw[]
  >- (Q.RENAME_TAC [‘i + 1 < LENGTH xs’] >>
      MAP_EVERY Q.EXISTS_TAC [‘TAKE i xs’, ‘DROP (i + 2) xs’] >>
      simp[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, EL_DROP] >> rw[] >>
      Q.RENAME_TAC [‘~(j < i)’, ‘j < i + 2’] >>
      ‘j = i \/ j = i + 1’ by simp[] >> simp[]) >>
  Q.EXISTS_TAC ‘LENGTH p’ >> simp[EL_APPEND_EQN]
QED

Theorem adjacent_append1:
  !xs ys a b. adjacent xs a b ==> adjacent (xs ++ ys) a b
Proof
  Induct_on ‘adjacent’ >> simp[] >> metis_tac[adjacent_rules]
QED

Theorem adjacent_append2:
  !xs ys a b. adjacent ys a b ==> adjacent (xs ++ ys) a b
Proof
  simp[adjacent_ps_append, PULL_EXISTS, APPEND_ASSOC] >> rpt strip_tac >>
  irule_at Any EQ_REFL
QED

Theorem adjacent_REVERSE[simp]:
  !xs a b. adjacent (REVERSE xs) a b <=> adjacent xs b a
Proof
  simp[adjacent_ps_append, EQ_IMP_THM, PULL_EXISTS] >> rw[]
  >- (pop_assum (mp_tac o Q.AP_TERM ‘REVERSE’) >>
      REWRITE_TAC[REVERSE_REVERSE] >> simp[REVERSE_APPEND] >>
      strip_tac >> Q.EXISTS_TAC ‘REVERSE s’ >>
      simp[GSYM APPEND_ASSOC, APPEND_11]) >>
  simp[REVERSE_APPEND, APPEND_ASSOC] >>
  Q.EXISTS_TAC ‘REVERSE s’ >> simp[GSYM APPEND_ASSOC, APPEND_11]
QED

(* ---------------------------------------------------------------------- *)

val lazy_list_case_compute = save_thm(
  "lazy_list_case_compute[compute]",
  computeLib.lazyfy_thm list_case_compute);

val _ = computeLib.add_persistent_funs [
      "APPEND", "APPEND_NIL", "FLAT", "HD", "TL", "LENGTH", "MAP", "MAP2",
      "NULL_DEF", "MEM", "EXISTS_DEF", "DROP_compute", "EVERY_DEF", "ZIP",
      "UNZIP", "FILTER", "FOLDL", "FOLDR",
      "TAKE_compute", "FOLDL", "REVERSE_REV", "SUM_SUM_ACC", "ALL_DISTINCT",
      "GENLIST_AUX", "EL_restricted", "EL_simp_restricted", "SNOC",
      "GENLIST_NUMERALS", "list_size_def", "FRONT_DEF",
      "LAST_compute", "isPREFIX"
    ]

val _ =
  let
    val list_info = Option.valOf (TypeBase.read {Thy = "list", Tyop="list"})
    val lift_list =
      mk_var ("listSyntax.lift_list",
              “:'type -> ('a -> 'term) -> 'a list -> 'term”)
    val list_info' =
        list_info |> TypeBasePure.put_lift lift_list
                  |> TypeBasePure.put_induction
                       (TypeBasePure.ORIG list_induction)
                  |> TypeBasePure.put_nchotomy list_nchotomy
  in
    (* this exports a tyinfo with simpls included, but that's OK given how
       small they are; seems easier than taking them out again only for the
       benefit of a tiny amount of file size in the .dat file *)
    TypeBase.export [list_info']
  end;

val _ = export_rewrites
          ["APPEND_11",
           "MAP2", "NULL_DEF",
           "SUM", "APPEND_ASSOC", "CONS", "CONS_11",
           "LENGTH_MAP",
           "NOT_CONS_NIL", "NOT_NIL_CONS",
           "CONS_ACYCLIC", "list_case_def",
           "ZIP", "UNZIP", "ZIP_UNZIP", "UNZIP_ZIP",
           "LENGTH_ZIP", "LENGTH_UNZIP",
           "EVERY_APPEND", "EXISTS_APPEND", "EVERY_SIMP",
           "NOT_EVERY", "NOT_EXISTS",
           "FOLDL", "FOLDR", "LENGTH_LUPDATE",
           "LUPDATE_LENGTH"];

val _ =
    monadsyntax.declare_monad (
      "list",
      { bind = “LIST_BIND”, ignorebind = SOME “LIST_IGNORE_BIND”,
        unit = “SINGL”, choice = SOME “APPEND”, fail = SOME “[]”,
        guard = SOME “LIST_GUARD” }
    )

(* ----------------------------------------------------------------------
    Supporting the quotient package
   ---------------------------------------------------------------------- *)

Theorem LIST_EQUIV[quotient_equiv]:
  !R:'a -> 'a -> bool. EQUIV R ==> EQUIV (LIST_REL R)
Proof
  simp[EQUIV_def] >> simp[GSYM ALT_equivalence] >>
  simp[equivalence_def, reflexive_def, symmetric_def, transitive_def] >>
  rpt strip_tac
  >- (irule EVERY2_refl >> simp[])
  >- (‘!l1 l2. LIST_REL R l1 l2 ==> LIST_REL R l2 l1’ suffices_by metis_tac[] >>
      Induct_on ‘LIST_REL’ >> simp[]) >>
  irule LIST_REL_trans >> first_assum $ irule_at Any >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem LIST_QUOTIENT[quotient]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    QUOTIENT (LIST_REL R) (MAP abs) (MAP rep)
Proof
  rw[] >> simp[QUOTIENT_def] >> rpt conj_tac
  >- (drule QUOTIENT_ABS_REP >> simp[MAP_MAP_o, o_DEF])
  >- (dxrule QUOTIENT_REP_REFL >> simp[LIST_REL_EL_EQN, EL_MAP]) >>
  dxrule_then assume_tac QUOTIENT_REL >>
  Induct >- simp[SF CONJ_ss] >>
  pop_assum (fn lrth => pop_assum (fn rth =>
    simp[] >> simp[Once rth, Once lrth, SimpLHS])) >>
  Cases_on ‘s’ >> simp[] >> metis_tac[]
QED

Theorem NIL_RSP[quotient_rsp]:
  !R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==> LIST_REL R [] []
Proof
  simp[]
QED

Theorem NIL_PRS[quotient_prs]:
  !R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==> [] = (MAP abs) []
Proof
  simp[]
QED

Theorem CONS_PRS[quotient_prs]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !t h. CONS h t = (MAP abs) (CONS (rep h) (MAP rep t))
Proof
  rpt strip_tac >> drule_then assume_tac QUOTIENT_ABS_REP >>
  simp[MAP_MAP_o, o_DEF]
QED

Theorem CONS_RSP[quotient_rsp]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !t1 t2 h1 h2.
      R h1 h2 /\ (LIST_REL R) t1 t2 ==> (LIST_REL R) (CONS h1 t1) (CONS h2 t2)
Proof
  simp[]
QED


Theorem EVERY_PRS[quotient_prs]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !l P. EVERY P l = EVERY ((abs --> I) P) (MAP rep l)
Proof
  rpt strip_tac >> drule_then assume_tac QUOTIENT_ABS_REP >>
  simp[EVERY_MAP, FUN_MAP_THM, SF ETA_ss]
QED

Theorem LIST_TO_SET_PRS[quotient_prs]:
  !R (abs : 'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !l. LIST_TO_SET l = IMAGE abs (LIST_TO_SET (MAP rep l))
Proof
  rpt strip_tac >> drule_then assume_tac QUOTIENT_ABS_REP >>
  simp[GSYM LIST_TO_SET_MAP, MAP_MAP_o, combinTheory.o_DEF]
QED

Definition SET_REL_def:
  SET_REL R s1 s2 <=>
  ?ps. IMAGE FST ps = s1 /\ IMAGE SND ps = s2 /\
       !p. p IN ps ==> R (FST p) (SND p)
End

Theorem SET_REL_EQ:
  SET_REL (=) = (=)
Proof
  simp[Once FUN_EQ_THM] >> simp[Once FUN_EQ_THM] >>
  simp[SET_REL_def, EQ_IMP_THM, FORALL_AND_THM, FORALL_PROD] >>
  conj_tac
  >- (simp[EXTENSION, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]) >>
  Q.X_GEN_TAC ‘s’ >> Q.EXISTS_TAC ‘{(a,a) | a IN s}’ >>
  simp[EXTENSION, EXISTS_PROD]
QED

Theorem SET_REL_THM:
  SET_REL R s1 s2 <=>
  (!x. x IN s1 ==> ?y. y IN s2 /\ R x y) /\
  (!y. y IN s2 ==> ?x. x IN s1 /\ R x y)
Proof
  simp[SET_REL_def, EQ_IMP_THM] >> rw[] >>
  FULL_SIMP_TAC (srw_ss()) [FORALL_PROD, PULL_EXISTS, EXISTS_PROD]
  >- metis_tac[]
  >- metis_tac[] >>
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  Q.RENAME_TAC [‘f _ IN s2 /\ R _ (f _)’, ‘g _ IN s1 /\ R (g _) _’] >>
  Q.EXISTS_TAC ‘{(x,f x) | x IN s1} UNION {(g y, y) | y IN s2}’ >>
  simp[EXTENSION, PULL_EXISTS, SF DNF_ss, EXISTS_PROD] >> metis_tac[]
QED

Theorem SET_QUOTIENT:
  !R abs rep.
    QUOTIENT R (abs : 'a -> 'b) rep ==>
    QUOTIENT (SET_REL R) (IMAGE abs) (IMAGE rep)
Proof
  simp[QUOTIENT_def] >> rpt strip_tac >>
  pop_assum (assume_tac o GSYM)
  >- simp[IMAGE_IMAGE, combinTheory.o_DEF]
  >- (simp[SET_REL_THM, PULL_EXISTS] >> metis_tac[]) >>
  eq_tac >> simp[SET_REL_THM] >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (simp[EXTENSION] >> metis_tac[]) >>
  Q.PAT_X_ASSUM ‘IMAGE _ _ = IMAGE _ _’ MP_TAC >>
  simp[EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem LIST_TO_SET_RSP[quotient_rsp]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !l1 l2. LIST_REL R l1 l2 ==>
            SET_REL R (LIST_TO_SET l1) (LIST_TO_SET l2)
Proof
  simp[SET_REL_THM, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem EVERY_RSP[quotient_rsp]:
  !R (abs:'a -> 'b) rep.
    QUOTIENT R abs rep ==>
    !l1 l2 P1 P2.
      (R ===> $=) P1 P2 /\ (LIST_REL R) l1 l2 ==>
      (EVERY P1 l1 <=> EVERY P2 l2)
Proof
  simp[EVERY_MEM, FUN_REL] >> rpt strip_tac >>
  Q.PAT_X_ASSUM ‘LIST_REL _ _ _’ MP_TAC >>
  Induct_on ‘LIST_REL’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[]
QED

Theorem MAP_RSP[quotient_rsp]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      !l1 l2 f1 f2.
        (R1 ===> R2) f1 f2 /\ (LIST_REL R1) l1 l2 ==>
        (LIST_REL R2) (MAP f1 l1) (MAP f2 l2)
Proof
  simp[FUN_REL] >> rpt strip_tac >>
  Q.PAT_X_ASSUM ‘LIST_REL _ _ _ ’ MP_TAC >>
  Induct_on ‘LIST_REL’ >> simp[]
QED

Theorem MAP_PRS[quotient_prs]:
  !R1 (abs1:'a -> 'c) rep1.
    QUOTIENT R1 abs1 rep1 ==>
    !R2 (abs2:'b -> 'd) rep2.
      QUOTIENT R2 abs2 rep2 ==>
      !l f. MAP f l = (MAP abs2) (MAP ((abs1 --> rep2) f) (MAP rep1 l))
Proof
  rpt strip_tac >> rpt (dxrule_then assume_tac QUOTIENT_ABS_REP) >>
  simp[MAP_MAP_o, FUN_MAP, combinTheory.o_DEF, SF ETA_ss]
QED

val _ = export_theory();
