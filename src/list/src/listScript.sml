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


(*---------------------------------------------------------------------------*
 * Require ancestor theory structures to be present. The parents of list     *
 * are "arithmetic" and "pair".                                              *
 *---------------------------------------------------------------------------*)

local open arithmeticTheory pairTheory pred_setTheory operatorTheory Datatype OpenTheoryMap in end;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib Num_conv Prim_rec BasicProvers mesonLib
     simpLib boolSimps pairTheory TotalDefn metisLib;;

val arith_ss = bool_ss ++ numSimps.ARITH_ss ++ numSimps.REDUCE_ss

val _ = new_theory "list";

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;
val zDefine = Lib.with_flag (computeLib.auto_import_definitions,false) Define

val NOT_SUC      = numTheory.NOT_SUC
and INV_SUC      = numTheory.INV_SUC
fun INDUCT_TAC g = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g;

val LESS_0       = prim_recTheory.LESS_0;
val NOT_LESS_0   = prim_recTheory.NOT_LESS_0;
val PRE          = prim_recTheory.PRE;
val LESS_MONO    = prim_recTheory.LESS_MONO;
val INV_SUC_EQ   = prim_recTheory.INV_SUC_EQ;
val num_Axiom    = prim_recTheory.num_Axiom;

val ADD_CLAUSES  = arithmeticTheory.ADD_CLAUSES;
val LESS_ADD_1   = arithmeticTheory.LESS_ADD_1;
val LESS_EQ      = arithmeticTheory.LESS_EQ;
val NOT_LESS     = arithmeticTheory.NOT_LESS;
val LESS_EQ_ADD  = arithmeticTheory.LESS_EQ_ADD;
val num_CASES    = arithmeticTheory.num_CASES;
val LESS_MONO_EQ = arithmeticTheory.LESS_MONO_EQ;
val LESS_MONO_EQ = arithmeticTheory.LESS_MONO_EQ;
val ADD_EQ_0     = arithmeticTheory.ADD_EQ_0;
val ONE          = arithmeticTheory.ONE;
val PAIR_EQ      = pairTheory.PAIR_EQ;

(*---------------------------------------------------------------------------*)
(* Declare the datatype of lists                                             *)
(*---------------------------------------------------------------------------*)

val _ = Datatype.Hol_datatype `list = NIL | CONS of 'a => list`;

local open OpenTheoryMap in
val ns = ["Data","List"]
val _ = OpenTheory_tyop_name{tyop={Thy="list",Tyop="list"},name=(ns,"list")}
val _ = OpenTheory_const_name{const={Thy="list",Name="NIL"},name=(ns,"[]")}
val _ = OpenTheory_const_name{const={Thy="list",Name="CONS"},name=(ns,"::")}
val _ = OpenTheory_const_name{const={Thy="list",Name="LENGTH"},name=(ns,"length")}
val _ = OpenTheory_const_name{const={Thy="list",Name="APPEND"},name=(ns,"@")}
val _ = OpenTheory_const_name{const={Thy="list",Name="EXISTS"},name=(ns,"any")}
val _ = OpenTheory_const_name{const={Thy="list",Name="EVERY"},name=(ns,"all")}
val _ = OpenTheory_const_name{const={Thy="list",Name="FILTER"},name=(ns,"filter")}
val _ = OpenTheory_const_name{const={Thy="list",Name="MAP"},name=(ns,"map")}
val _ = OpenTheory_const_name{const={Thy="list",Name="HD"},name=(ns,"head")}
val _ = OpenTheory_const_name{const={Thy="list",Name="TL"},name=(ns,"tail")}
val _ = OpenTheory_const_name{const={Thy="list",Name="FLAT"},name=(ns,"concat")}
end

(*---------------------------------------------------------------------------*)
(* Fiddle with concrete syntax                                               *)
(*---------------------------------------------------------------------------*)

val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "["], rightdelim = [TOK "]"],
                      cons = "CONS", nilstr = "NIL",
                      block_info = (PP.INCONSISTENT, 0)};

val _ = add_rule {term_name = "CONS", fixity = Infixr 490,
                  pp_elements = [TOK "::", BreakSpace(0,2)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 2))};

(*---------------------------------------------------------------------------*)
(* Prove the axiomatization of lists                                         *)
(*---------------------------------------------------------------------------*)

val list_Axiom = TypeBase.axiom_of ``:'a list``;

val list_Axiom_old = store_thm(
  "list_Axiom_old",
  Term`!x f. ?!fn1:'a list -> 'b.
          (fn1 [] = x) /\ (!h t. fn1 (h::t) = f (fn1 t) h t)`,
  REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL [
    ASSUME_TAC list_Axiom THEN
    POP_ASSUM (ACCEPT_TAC o BETA_RULE o Q.SPECL [`x`, `\x y z. f z x y`]),
    REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    HO_MATCH_MP_TAC (TypeBase.induction_of ``:'a list``) THEN
    simpLib.ASM_SIMP_TAC boolSimps.bool_ss []
  ]);

(*---------------------------------------------------------------------------
     Now some definitions.
 ---------------------------------------------------------------------------*)

val NULL_DEF = new_recursive_definition
      {name = "NULL_DEF",
       rec_axiom = list_Axiom,
       def = --`(NULL []     = T) /\
                (NULL (h::t) = F)`--};

val HD = new_recursive_definition
      {name = "HD",
       rec_axiom = list_Axiom,
       def = --`HD (h::t) = h`--};
val _ = export_rewrites ["HD"]

val TL = new_recursive_definition
      {name = "TL",
       rec_axiom = list_Axiom,
       def = --`TL (h::t) = t`--};
val _ = export_rewrites ["TL"]

val SUM = new_recursive_definition
      {name = "SUM",
       rec_axiom =  list_Axiom,
       def = --`(SUM [] = 0) /\
          (!h t. SUM (h::t) = h + SUM t)`--};

val APPEND = new_recursive_definition
      {name = "APPEND",
       rec_axiom = list_Axiom,
       def = --`(!l:'a list. APPEND [] l = l) /\
                  (!l1 l2 h. APPEND (h::l1) l2 = h::APPEND l1 l2)`--};
val _ = export_rewrites ["APPEND"]

val _ = set_fixity "++" (Infixl 480);
val _ = overload_on ("++", Term`APPEND`);

val FLAT = new_recursive_definition
      {name = "FLAT",
       rec_axiom = list_Axiom,
       def = --`(FLAT []     = []) /\
          (!h t. FLAT (h::t) = APPEND h (FLAT t))`--};

val LENGTH = new_recursive_definition
      {name = "LENGTH",
       rec_axiom = list_Axiom,
       def = --`(LENGTH []     = 0) /\
     (!(h:'a) t. LENGTH (h::t) = SUC (LENGTH t))`--};
val _ = export_rewrites ["LENGTH"]

val MAP = new_recursive_definition
      {name = "MAP",
       rec_axiom = list_Axiom,
       def = --`(!f:'a->'b. MAP f [] = []) /\
                   (!f h t. MAP f (h::t) = f h::MAP f t)`--};

val LIST_TO_SET_DEF = new_recursive_definition{
  name = "LIST_TO_SET_DEF",
  rec_axiom = list_Axiom,
  def = ``(!x:'a. LIST_TO_SET [] x <=> F) /\
          (!h:'a t x. LIST_TO_SET (h::t) x = (x = h) \/ LIST_TO_SET t x)``}
val _ = overload_on ("set", ``LIST_TO_SET``)
val _ = overload_on ("MEM", ``\h:'a l:'a list. h IN LIST_TO_SET l``)
val _ = export_rewrites ["LIST_TO_SET_DEF"]

val LIST_TO_SET = store_thm(
  "LIST_TO_SET",
  ``(LIST_TO_SET [] = {}) /\
    (LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t)``,
  SRW_TAC [][FUN_EQ_THM, IN_DEF]);
val _ = export_rewrites ["LIST_TO_SET"]

val IN_LIST_TO_SET = save_thm("IN_LIST_TO_SET", TRUTH)

val FILTER = new_recursive_definition
      {name = "FILTER",
       rec_axiom = list_Axiom,
       def = --`(!P. FILTER P [] = []) /\
             (!(P:'a->bool) h t.
                    FILTER P (h::t) =
                         if P h then (h::FILTER P t) else FILTER P t)`--};
val _ = export_rewrites ["FILTER"]

val FOLDR = new_recursive_definition
      {name = "FOLDR",
       rec_axiom = list_Axiom,
       def = --`(!f e. FOLDR (f:'a->'b->'b) e [] = e) /\
            (!f e x l. FOLDR f e (x::l) = f x (FOLDR f e l))`--};

val FOLDL = new_recursive_definition
      {name = "FOLDL",
       rec_axiom = list_Axiom,
       def = --`(!f e. FOLDL (f:'b->'a->'b) e [] = e) /\
            (!f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l)`--};

val EVERY_DEF = new_recursive_definition
      {name = "EVERY_DEF",
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EVERY P [] = T)  /\
                (!P h t. EVERY P (h::t) = P h /\ EVERY P t)`--};
val _ = export_rewrites ["EVERY_DEF"]

val EXISTS_DEF = new_recursive_definition
      {name = "EXISTS_DEF",
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EXISTS P [] = F)
            /\  (!P h t.      EXISTS P (h::t) = P h \/ EXISTS P t)`--};
val _ = export_rewrites ["EXISTS_DEF"]

val EL = new_recursive_definition
      {name = "EL",
       rec_axiom = num_Axiom,
       def = --`(!l. EL 0 l = (HD l:'a)) /\
                (!l:'a list. !n. EL (SUC n) l = EL n (TL l))`--};



(* ---------------------------------------------------------------------*)
(* Definition of a function 						*)
(*									*)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list		*)
(* 									*)
(* for mapping a curried binary function down a pair of lists:		*)
(* 									*)
(* |- (!f. MAP2 f[][] = []) /\						*)
(*   (!f h1 t1 h2 t2.							*)
(*      MAP2 f(h1::t1)(h2::t2) = CONS(f h1 h2)(MAP2 f t1 t2))	*)
(* 									*)
(* [TFM 92.04.21]							*)
(* ---------------------------------------------------------------------*)

val MAP2_DEF = Define`
  (MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2) /\
  (MAP2 f x y = [])`
val _ = delete_const "MAP2_tupled"

val MAP2 = store_thm ("MAP2",
``(!f. MAP2 f [] [] = []) /\
  (!f h1 t1 h2 t2. MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2)``,
METIS_TAC[MAP2_DEF]);

(* ---------------------------------------------------------------------*)
(* Proofs of some theorems about lists.					*)
(* ---------------------------------------------------------------------*)

val NULL = store_thm ("NULL",
 --`NULL ([] :'a list) /\ (!h t. ~NULL(CONS (h:'a) t))`--,
   REWRITE_TAC [NULL_DEF]);

(*---------------------------------------------------------------------------*)
(* List induction                                                            *)
(* |- P [] /\ (!t. P t ==> !h. P(h::t)) ==> (!x.P x)                         *)
(*---------------------------------------------------------------------------*)

val list_INDUCT0 = TypeBase.induction_of ``:'a list``;

val list_INDUCT = Q.store_thm
("list_INDUCT",
 `!P. P [] /\ (!t. P t ==> !h. P (h::t)) ==> !l. P l`,
 REWRITE_TAC [list_INDUCT0]);  (* must use REWRITE_TAC, ACCEPT_TAC refuses
                                   to respect bound variable names *)

val list_induction  = save_thm("list_induction", list_INDUCT);
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(*---------------------------------------------------------------------------*)
(* List induction as a rewrite rule.                                         *)
(* |- (!l. P l) = P [] /\ !h t. P t ==> P (h::t)                             *)
(*---------------------------------------------------------------------------*)

val FORALL_LIST = Q.store_thm
 ("FORALL_LIST",
  `(!l. P l) = P [] /\ !h t. P t ==> P (h::t)`,
  METIS_TAC [list_INDUCT]);

(*---------------------------------------------------------------------------*)
(* Cases theorem: |- !l. (l = []) \/ (?t h. l = h::t)                        *)
(*---------------------------------------------------------------------------*)

val list_cases = TypeBase.nchotomy_of ``:'a list``;


val list_CASES = store_thm
("list_CASES",
 --`!l. (l = []) \/ (?t h. l = h::t)`--,
 mesonLib.MESON_TAC [list_cases]);

val list_nchotomy = save_thm("list_nchotomy", list_CASES);

(*---------------------------------------------------------------------------*)
(* Definition of list_case more suitable to call-by-value computations       *)
(*---------------------------------------------------------------------------*)

val list_case_def = TypeBase.case_def_of ``:'a list``;

val list_case_compute = store_thm("list_case_compute",
 --`!(l:'a list). list_CASE l (b:'b) f =
                  if NULL l then b else f (HD l) (TL l)`--,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [list_case_def,HD, TL,NULL_DEF]);

(*---------------------------------------------------------------------------*)
(* CONS_11:  |- !h t h' t'. (h::t = h' :: t') = (h = h') /\ (t = t')         *)
(*---------------------------------------------------------------------------*)

val CONS_11 = save_thm("CONS_11", TypeBase.one_one_of ``:'a list``)

val NOT_NIL_CONS = save_thm("NOT_NIL_CONS", TypeBase.distinct_of ``:'a list``);

val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);

val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 --`!l1 l2. ~(l1 = l2) ==> !h1:'a. !h2. ~(h1::l1 = h2::l2)`--,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [CONS_11]);

val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 --`!h1:'a. !h2. ~(h1 = h2) ==> !l1 l2. ~(h1::l1 = h2::l2)`--,
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [CONS_11]);

val EQ_LIST = store_thm("EQ_LIST",
 --`!h1:'a.!h2.(h1=h2) ==> !l1 l2. (l1 = l2) ==> (h1::l1 = h2::l2)`--,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [CONS_11]);


val CONS = store_thm   ("CONS",
  --`!l : 'a list. ~NULL l ==> (HD l :: TL l = l)`--,
       STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC (--`l:'a list`--) list_CASES) THEN
       POP_ASSUM SUBST1_TAC THEN
       ASM_REWRITE_TAC [HD, TL, NULL]);

val APPEND_NIL = store_thm("APPEND_NIL",
--`!(l:'a list). APPEND l [] = l`--,
 LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);
val _ = export_rewrites ["APPEND_NIL"]


val APPEND_ASSOC = store_thm ("APPEND_ASSOC",
 --`!(l1:'a list) l2 l3.
     APPEND l1 (APPEND l2 l3) = (APPEND (APPEND l1 l2) l3)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);

val LENGTH_APPEND = store_thm ("LENGTH_APPEND",
 --`!(l1:'a list) (l2:'a list).
     LENGTH (APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, APPEND, ADD_CLAUSES]);
val _ = export_rewrites ["LENGTH_APPEND"]

val MAP_APPEND = store_thm ("MAP_APPEND",
 --`!(f:'a->'b).!l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`--,
    STRIP_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, APPEND]);

val MAP_ID = store_thm(
  "MAP_ID",
  ``(MAP (\x. x) l = l) /\ (MAP I l = l)``,
  Induct_on `l` THEN SRW_TAC [][MAP]);
val _ = export_rewrites ["MAP_ID"]

val LENGTH_MAP = store_thm ("LENGTH_MAP",
 --`!l. !(f:'a->'b). LENGTH (MAP f l) = LENGTH l`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH]);

val MAP_EQ_NIL = store_thm(
  "MAP_EQ_NIL",
  --`!(l:'a list) (f:'a->'b).
         ((MAP f l = []) = (l = [])) /\
         (([] = MAP f l) = (l = []))`--,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, NOT_CONS_NIL, NOT_NIL_CONS]);

val MAP_EQ_f = store_thm ("MAP_EQ_f",
  ``!f1 f2 l. (MAP f1 l = MAP f2 l) = (!e. MEM e l ==> (f1 e = f2 e))``,
  Induct_on `l` THEN
  ASM_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, MAP, CONS_11, FORALL_AND_THM])

val MAP_o = store_thm("MAP_o",
    (--`!f:'b->'c. !g:'a->'b.  MAP (f o g) = (MAP f) o (MAP g)`--),
    REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP,combinTheory.o_THM]);

val MAP_MAP_o = store_thm("MAP_MAP_o",
    (--`!(f:'b->'c) (g:'a->'b) l. MAP f (MAP g l) = MAP (f o g) l`--),
    REPEAT GEN_TAC THEN REWRITE_TAC [MAP_o,combinTheory.o_DEF]
    THEN BETA_TAC THEN REFL_TAC);

val EL_MAP = store_thm("EL_MAP",
    (--`!n l. n < (LENGTH l) ==> !f:'a->'b. EL n (MAP f l) = f (EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,MAP,LESS_MONO_EQ,NOT_LESS_0,HD,TL]);

val MAP_TL = Q.store_thm("MAP_TL",
  `!l f. ~NULL l ==> (MAP f (TL l) = TL (MAP f l))`,
  Induct THEN REWRITE_TAC [NULL_DEF, TL, MAP]);

val EVERY_EL = store_thm ("EVERY_EL",
 --`!(l:'a list) P. EVERY P l = !n. n < LENGTH l ==> P (EL n l)`--,
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF, LENGTH, NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN INDUCT_TAC THENL
       [ASM_REWRITE_TAC [EL, HD],
        ASM_REWRITE_TAC [LESS_MONO_EQ, EL, TL]],
       REPEAT STRIP_TAC THENL
       [POP_ASSUM (MP_TAC o (SPEC (--`0`--))) THEN
        REWRITE_TAC [LESS_0, EL, HD],
	POP_ASSUM ((ANTE_RES_THEN ASSUME_TAC) o (MATCH_MP LESS_MONO)) THEN
	POP_ASSUM MP_TAC THEN REWRITE_TAC [EL, TL]]]);

val EVERY_CONJ = store_thm("EVERY_CONJ",
 --`!P Q l. EVERY (\(x:'a). (P x) /\ (Q x)) l = (EVERY P l /\ EVERY Q l)`--,
     NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

open pred_setTheory
val EVERY_MEM = store_thm(
  "EVERY_MEM",
  ``!P l:'a list. EVERY P l = !e. MEM e l ==> P e``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, LIST_TO_SET, IN_INSERT, NOT_IN_EMPTY] THEN
  mesonLib.MESON_TAC []);

val EVERY_MAP = store_thm(
  "EVERY_MAP",
  ``!P f l:'a list. EVERY P (MAP f l) = EVERY (\x. P (f x)) l``,
  NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, MAP] THEN BETA_TAC THEN REWRITE_TAC []);

val EVERY_SIMP = store_thm(
  "EVERY_SIMP",
  ``!c l:'a list. EVERY (\x. c) l = (l = []) \/ c``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, NOT_CONS_NIL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []);

val MONO_EVERY = store_thm(
  "MONO_EVERY",
  ``(!x. P x ==> Q x) ==> (EVERY P l ==> EVERY Q l)``,
  Q.ID_SPEC_TAC `l` THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (srw_ss()) []);
val _ = IndDefLib.export_mono "MONO_EVERY"

val EXISTS_MEM = store_thm(
  "EXISTS_MEM",
  ``!P l:'a list. EXISTS P l = ?e. MEM e l /\ P e``,
  Induct_on `l` THEN SRW_TAC [][] THEN MESON_TAC[]);

val EXISTS_MAP = store_thm(
  "EXISTS_MAP",
  ``!P f l:'a list. EXISTS P (MAP f l) = EXISTS (\x. P (f x)) l``,
  NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXISTS_DEF, MAP] THEN BETA_TAC THEN REWRITE_TAC []);

val EXISTS_SIMP = store_thm(
  "EXISTS_SIMP",
  ``!c l:'a list. EXISTS (\x. c) l = ~(l = []) /\ c``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EXISTS_DEF, NOT_CONS_NIL] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []);

val MONO_EXISTS = store_thm(
  "MONO_EXISTS",
  ``(!x. P x ==> Q x) ==> (EXISTS P l ==> EXISTS Q l)``,
  Q.ID_SPEC_TAC `l` THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [DISJ_IMP_THM]);
val _ = IndDefLib.export_mono "MONO_EXISTS"


val EVERY_NOT_EXISTS = store_thm(
  "EVERY_NOT_EXISTS",
  ``!P l. EVERY P l = ~EXISTS (\x. ~P x) l``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF] THEN BETA_TAC THEN
  REWRITE_TAC [DE_MORGAN_THM]);

val EXISTS_NOT_EVERY = store_thm(
  "EXISTS_NOT_EVERY",
  ``!P l. EXISTS P l = ~EVERY (\x. ~P x) l``,
  REWRITE_TAC [EVERY_NOT_EXISTS] THEN BETA_TAC THEN REWRITE_TAC [] THEN
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN REWRITE_TAC []);

val MEM_APPEND = store_thm(
  "MEM_APPEND",
  ``!e l1 l2. MEM e (APPEND l1 l2) = MEM e l1 \/ MEM e l2``,
  Induct_on `l1` THEN SRW_TAC [][DISJ_ASSOC]);
val _ = export_rewrites ["MEM_APPEND"]

val MEM_FILTER = Q.store_thm
("MEM_FILTER",
 `!P L x. MEM x (FILTER P L) = P x /\ MEM x L`,
 Induct_on `L` THEN SRW_TAC [][] THEN PROVE_TAC[]);

val MEM_FLAT = Q.store_thm
("MEM_FLAT",
 `!x L. MEM x (FLAT L) = (?l. MEM l L /\ MEM x l)`,
 Induct_on `L` THEN SRW_TAC [][FLAT] THEN PROVE_TAC[]);

val FLAT_APPEND = Q.store_thm ("FLAT_APPEND",
   `!l1 l2. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`,
   LIST_INDUCT_TAC
   THEN REWRITE_TAC [APPEND, FLAT]
   THEN ASM_REWRITE_TAC [APPEND_ASSOC]);
val _ = export_rewrites ["FLAT_APPEND"]

val EVERY_APPEND = store_thm(
  "EVERY_APPEND",
  ``!P (l1:'a list) l2.
        EVERY P (APPEND l1 l2) = EVERY P l1 /\ EVERY P l2``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, EVERY_DEF, CONJ_ASSOC]);

val EXISTS_APPEND = store_thm(
  "EXISTS_APPEND",
  ``!P (l1:'a list) l2.
       EXISTS P (APPEND l1 l2) = EXISTS P l1 \/ EXISTS P l2``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, EXISTS_DEF, DISJ_ASSOC]);

val NOT_EVERY = store_thm(
  "NOT_EVERY",
  ``!P l. ~EVERY P l = EXISTS ($~ o P) l``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF, DE_MORGAN_THM,
                   combinTheory.o_THM]);

val NOT_EXISTS = store_thm(
  "NOT_EXISTS",
  ``!P l. ~EXISTS P l = EVERY ($~ o P) l``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [EVERY_DEF, EXISTS_DEF, DE_MORGAN_THM,
                   combinTheory.o_THM]);

val MEM_MAP = store_thm(
  "MEM_MAP",
  ``!(l:'a list) (f:'a -> 'b) x.
       MEM x (MAP f l) = ?y. (x = f y) /\ MEM y l``,
  LIST_INDUCT_TAC THEN SRW_TAC [][MAP] THEN PROVE_TAC[]);

val LENGTH_NIL = store_thm("LENGTH_NIL",
 --`!l:'a list. (LENGTH l = 0) = (l = [])`--,
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL]);

val LENGTH_NIL_SYM = store_thm (
   "LENGTH_NIL_SYM",
   ``(0 = LENGTH l) = (l = [])``,
   PROVE_TAC[LENGTH_NIL]);

val NULL_EQ = store_thm("NULL_EQ",
 --`!l. NULL l = (l = [])`--,
   Cases_on `l` THEN REWRITE_TAC[NULL, NOT_CONS_NIL]);

val NULL_LENGTH = Q.store_thm("NULL_LENGTH",
  `!l. NULL l = (LENGTH l = 0)`,
  REWRITE_TAC[NULL_EQ,LENGTH_NIL])

val LENGTH_CONS = store_thm("LENGTH_CONS",
 --`!l n. (LENGTH l = SUC n) =
          ?h:'a. ?l'. (LENGTH l' = n) /\ (l = CONS h l')`--,
    LIST_INDUCT_TAC THENL [
      REWRITE_TAC [LENGTH, NOT_EQ_SYM(SPEC_ALL NOT_SUC), NOT_NIL_CONS],
      REWRITE_TAC [LENGTH, INV_SUC_EQ, CONS_11] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      simpLib.ASM_SIMP_TAC boolSimps.bool_ss []
    ]);

val LENGTH_EQ_CONS = store_thm("LENGTH_EQ_CONS",
 --`!P:'a list->bool.
    !n:num.
      (!l. (LENGTH l = SUC n) ==> P l) =
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)`--,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH,NOT_NIL_CONS,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH,INV_SUC_EQ,CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);

val LENGTH_EQ_SUM = store_thm (
   "LENGTH_EQ_SUM",
  ``(!l:'a list n1 n2. (LENGTH l = n1+n2) = (?l1 l2. (LENGTH l1 = n1) /\ (LENGTH l2 = n2) /\ (l = l1++l2)))``,
  Induct_on `n1` THEN1 (
     SIMP_TAC arith_ss [LENGTH_NIL, APPEND]
  ) THEN
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD_CLAUSES, LENGTH_CONS,
    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM, APPEND] THEN
  PROVE_TAC[]);

val LENGTH_EQ_NUM = store_thm (
   "LENGTH_EQ_NUM",
  ``(!l:'a list. (LENGTH l = 0) = (l = [])) /\
    (!l:'a list n. (LENGTH l = (SUC n)) = (?h l'. (LENGTH l' = n) /\ (l = h::l'))) /\
    (!l:'a list n1 n2. (LENGTH l = n1+n2) = (?l1 l2. (LENGTH l1 = n1) /\ (LENGTH l2 = n2) /\ (l = l1++l2)))``,
  SIMP_TAC arith_ss [LENGTH_NIL, LENGTH_CONS, LENGTH_EQ_SUM]);

val LENGTH_EQ_NUM_compute = save_thm ("LENGTH_EQ_NUM_compute",
   CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV LENGTH_EQ_NUM);


val LENGTH_EQ_NIL = store_thm("LENGTH_EQ_NIL",
 --`!P: 'a list->bool.
    (!l. (LENGTH l = 0) ==> P l) = P []`--,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LENGTH],
    DISCH_TAC THEN
    INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [LENGTH,NOT_SUC]]]);;

val CONS_ACYCLIC = store_thm("CONS_ACYCLIC",
Term`!l x. ~(l = x::l) /\ ~(x::l = l)`,
 LIST_INDUCT_TAC
 THEN ASM_REWRITE_TAC[CONS_11,NOT_NIL_CONS, NOT_CONS_NIL, LENGTH_NIL]);

val APPEND_eq_NIL = store_thm("APPEND_eq_NIL",
Term `(!l1 l2:'a list. ([] = APPEND l1 l2) = (l1=[]) /\ (l2=[])) /\
      (!l1 l2:'a list. (APPEND l1 l2 = []) = (l1=[]) /\ (l2=[]))`,
CONJ_TAC THEN
  INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC
   THEN REWRITE_TAC [CONS_11,NOT_NIL_CONS, NOT_CONS_NIL,APPEND]
   THEN GEN_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);
val _ = export_rewrites ["APPEND_eq_NIL"]

val APPEND_EQ_SING = store_thm(
  "APPEND_EQ_SING",
  ``(l1 ++ l2 = [e:'a]) <=>
      (l1 = [e]) /\ (l2 = []) \/ (l1 = []) /\ (l2 = [e])``,
  Cases_on `l1` THEN SRW_TAC [][CONJ_ASSOC]);

val APPEND_11 = store_thm(
  "APPEND_11",
  Term`(!l1 l2 l3:'a list. (APPEND l1 l2 = APPEND l1 l3) = (l2 = l3)) /\
       (!l1 l2 l3:'a list. (APPEND l2 l1 = APPEND l3 l1) = (l2 = l3))`,
  CONJ_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, CONS_11, APPEND_NIL] THEN
  Q.SUBGOAL_THEN
    `!h l1 l2:'a list. APPEND l1 (h::l2) = APPEND (APPEND l1 [h]) l2`
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

val APPEND_LENGTH_EQ = store_thm(
  "APPEND_LENGTH_EQ",
  ``!l1 l1'. (LENGTH l1 = LENGTH l1') ==>
    !l2 l2'. (LENGTH l2 = LENGTH l2') ==>
             ((l1 ++ l2 = l1' ++ l2') = (l1 = l1') /\ (l2 = l2'))``,
  Induct THEN1
     (GEN_TAC THEN STRIP_TAC THEN `l1' = []` by METIS_TAC [LENGTH_NIL] THEN
      SRW_TAC [][]) THEN
  MAP_EVERY Q.X_GEN_TAC [`h`,`l1'`] THEN SRW_TAC [][] THEN
  `?h' t'. l1' = h'::t'` by METIS_TAC [LENGTH_CONS] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);

val APPEND_11_LENGTH = save_thm ("APPEND_11_LENGTH",
 SIMP_RULE bool_ss [DISJ_IMP_THM, FORALL_AND_THM] (prove (
 (--`!l1 l2 l1' l2'.
        ((LENGTH l1 = LENGTH l1') \/ (LENGTH l2 = LENGTH l2')) ==>
        (((l1 ++ l2) = (l1' ++ l2')) = ((l1 = l1') /\ (l2 = l2')))`--),
     REPEAT GEN_TAC
     THEN Tactical.REVERSE
        (Cases_on `(LENGTH l1 = LENGTH l1') /\ (LENGTH l2 = LENGTH l2')`) THEN1
(
           DISCH_TAC
           THEN `~((l1 = l1') /\ (l2 = l2'))` by PROVE_TAC[]
           THEN ASM_REWRITE_TAC[]
           THEN Tactical.REVERSE
              (`~(LENGTH (l1 ++ l2) = LENGTH (l1' ++ l2'))` by ALL_TAC) THEN1 PROVE_TAC[]
           THEN FULL_SIMP_TAC arith_ss [LENGTH_APPEND]
     ) THEN PROVE_TAC[APPEND_LENGTH_EQ])))


val APPEND_eq_ID = store_thm(
"APPEND_EQ_SELF",
``(!l1 l2:'a list. ((l1 ++ l2 = l1) = (l2 = []))) /\
  (!l1 l2:'a list. ((l1 ++ l2 = l2) = (l1 = []))) /\
  (!l1 l2:'a list. ((l1 = l1 ++ l2) = (l2 = []))) /\
  (!l1 l2:'a list. ((l2 = l1 ++ l2) = (l1 = [])))``,
PROVE_TAC[APPEND_11, APPEND_NIL, APPEND]);


val MEM_SPLIT = Q.store_thm
("MEM_SPLIT",
 `!x l. (MEM x l) = ?l1 l2. (l = l1 ++ x::l2)`,
 Induct_on `l` THEN SRW_TAC [][] THEN EQ_TAC THENL [
   SRW_TAC [][] THEN1 (MAP_EVERY Q.EXISTS_TAC [`[]`,`l`] THEN SRW_TAC [][]) THEN
   MAP_EVERY Q.EXISTS_TAC [`a::l1`, `l2`] THEN SRW_TAC [][],
   DISCH_THEN (Q.X_CHOOSE_THEN `l1` (Q.X_CHOOSE_THEN `l2` ASSUME_TAC)) THEN
   Cases_on `l1` THEN FULL_SIMP_TAC(srw_ss()) [] THEN PROVE_TAC[]
 ])

val LIST_EQ_REWRITE = Q.store_thm
("LIST_EQ_REWRITE",
 `!l1 l2. (l1 = l2) =
      ((LENGTH l1 = LENGTH l2) /\
       ((!x. (x < LENGTH l1) ==> (EL x l1 = EL x l2))))`,

 LIST_INDUCT_TAC THEN Cases_on `l2` THEN (
   ASM_SIMP_TAC arith_ss [LENGTH, NOT_CONS_NIL, CONS_11, EL]
 ) THEN
 GEN_TAC THEN EQ_TAC THEN SIMP_TAC arith_ss [] THENL [
   REPEAT STRIP_TAC THEN Cases_on `x` THEN (
     ASM_SIMP_TAC arith_ss [EL,HD, TL]
   ),
   REPEAT STRIP_TAC THENL [
     POP_ASSUM (MP_TAC o SPEC ``0:num``) THEN
     ASM_SIMP_TAC arith_ss [EL,HD, TL],
     Q.PAT_ASSUM `!x. x < Y ==> P x` (MP_TAC o SPEC ``SUC x``) THEN
     ASM_SIMP_TAC arith_ss [EL,HD, TL]
   ]
 ]);

val LIST_EQ = save_thm("LIST_EQ",
    GENL[``l1:'a list``, ``l2:'a list``]
    (snd(EQ_IMP_RULE (SPEC_ALL LIST_EQ_REWRITE))));

val FOLDL_EQ_FOLDR = Q.store_thm
("FOLDL_EQ_FOLDR",
 `!f l e. (ASSOC f /\ COMM f) ==>
          ((FOLDL f e l) = (FOLDR f e l))`,
GEN_TAC THEN
FULL_SIMP_TAC bool_ss [RIGHT_FORALL_IMP_THM, operatorTheory.COMM_DEF,
  operatorTheory.ASSOC_DEF] THEN
STRIP_TAC THEN LIST_INDUCT_TAC THENL [
  SIMP_TAC bool_ss [FOLDR, FOLDL],

  ASM_SIMP_TAC bool_ss [FOLDR, FOLDL] THEN
  POP_ASSUM (K ALL_TAC) THEN
  Q.SPEC_TAC (`l`, `l`) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [FOLDR]
]);

val FOLDR_CONS = store_thm(
"FOLDR_CONS",
``!f ls a. FOLDR (\x y. f x :: y) a ls = (MAP f ls)++a``,
GEN_TAC THEN Induct THEN SRW_TAC[][FOLDR,MAP])

val LENGTH_TL = Q.store_thm
("LENGTH_TL",
  `!l. 0 < LENGTH l ==> (LENGTH (TL l) = LENGTH l - 1)`,
  Cases_on `l` THEN SIMP_TAC arith_ss [LENGTH, TL]);

val FILTER_EQ_NIL = Q.store_thm
("FILTER_EQ_NIL",
 `!P l. (FILTER P l = []) = (EVERY (\x. ~(P x)) l)`,
 GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN (
    ASM_SIMP_TAC bool_ss [FILTER,EVERY_DEF, COND_RATOR, COND_RAND,
			  NOT_CONS_NIL]
 ));

val FILTER_NEQ_NIL = Q.store_thm
("FILTER_NEQ_NIL",
 `!P l. ~(FILTER P l = []) = ?x. MEM x l /\ P x`,
 SIMP_TAC bool_ss [FILTER_EQ_NIL, EVERY_NOT_EXISTS, EXISTS_MEM]);

val FILTER_EQ_ID = Q.store_thm
("FILTER_EQ_ID",
 `!P l. (FILTER P l = l) = (EVERY P l)`,
 Induct_on `l` THEN SRW_TAC [][] THEN
 DISCH_THEN (ASSUME_TAC o Q.AP_TERM `MEM a`) THEN
 FULL_SIMP_TAC (srw_ss()) [MEM_FILTER]);

val FILTER_NEQ_ID = Q.store_thm
("FILTER_NEQ_ID",
 `!P l. ~(FILTER P l = l) = ?x. MEM x l /\ ~(P x)`,
 SIMP_TAC bool_ss [FILTER_EQ_ID, EVERY_NOT_EXISTS, EXISTS_MEM]);

val FILTER_EQ_CONS = Q.store_thm
("FILTER_EQ_CONS",
 `!P l h lr.
  (FILTER P l = h::lr) =
  (?l1 l2. (l = l1++[h]++l2) /\ (FILTER P l1 = []) /\ (FILTER P l2 = lr) /\ (P h))`,

GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN (
  ASM_SIMP_TAC bool_ss [FILTER, NOT_CONS_NIL, APPEND_eq_NIL]
) THEN
REPEAT STRIP_TAC THEN Cases_on `P h` THEN ASM_REWRITE_TAC[] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
  Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `l` THEN
  FULL_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER],

  Cases_on `l1` THEN (
    FULL_SIMP_TAC bool_ss [APPEND, CONS_11, FILTER, COND_RAND, COND_RATOR, NOT_CONS_NIL]
  ),

  Q.EXISTS_TAC `h::l1` THEN Q.EXISTS_TAC `l2` THEN
  ASM_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER],

  Cases_on `l1` THENL [
    FULL_SIMP_TAC bool_ss [APPEND, CONS_11],
    Q.EXISTS_TAC `l'` THEN Q.EXISTS_TAC `l2` THEN
    FULL_SIMP_TAC bool_ss [CONS_11, APPEND, FILTER, COND_RATOR,
			   COND_RAND, NOT_CONS_NIL]
  ]
]);

val FILTER_APPEND_DISTRIB = Q.store_thm
("FILTER_APPEND_DISTRIB",
 `!P L M. FILTER P (APPEND L M) = APPEND (FILTER P L) (FILTER P M)`,
   GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN RW_TAC bool_ss [FILTER,APPEND]);

val MEM = store_thm(
  "MEM",
  ``(!x:'a. MEM x [] = F) /\ (!x:'a h t. MEM x (h::t) = (x = h) \/ MEM x t)``,
  SRW_TAC [][]);
val _ = export_rewrites ["MEM"];

val FILTER_EQ_APPEND = Q.store_thm
("FILTER_EQ_APPEND",
 `!P l l1 l2.
  (FILTER P l = l1 ++ l2) =
  (?l3 l4. (l = l3++l4) /\ (FILTER P l3 = l1) /\ (FILTER P l4 = l2))`,
GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN1 (
  ASM_SIMP_TAC bool_ss [FILTER, APPEND_eq_NIL] THEN PROVE_TAC[]
) THEN
REPEAT STRIP_TAC THEN Cases_on `P h` THEN
ASM_SIMP_TAC bool_ss [FILTER] THENL [
  Cases_on `l1` THENL [
    Cases_on `l2` THENL [
      SIMP_TAC bool_ss [APPEND, NOT_CONS_NIL, FILTER_EQ_NIL, EVERY_MEM] THEN
      PROVE_TAC[MEM_APPEND, MEM],

      ASM_SIMP_TAC bool_ss [APPEND, CONS_11] THEN
      EQ_TAC THEN STRIP_TAC THENL [
        Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `h::l` THEN
        FULL_SIMP_TAC bool_ss [APPEND, FILTER],

        Tactical.REVERSE (Cases_on `l3`) THEN1 (
           FULL_SIMP_TAC bool_ss [CONS_11, FILTER, APPEND,
	                          COND_RAND, COND_RATOR, NOT_CONS_NIL]
        ) THEN
        Cases_on `l4` THEN (
          FULL_SIMP_TAC bool_ss [FILTER, NOT_CONS_NIL, APPEND,
	                         COND_RATOR, COND_RAND, CONS_11] THEN
          PROVE_TAC[]
        )
      ]
    ],

    ASM_SIMP_TAC bool_ss [APPEND, CONS_11] THEN
    EQ_TAC THEN STRIP_TAC THENL [
       Q.EXISTS_TAC `h::l3` THEN Q.EXISTS_TAC `l4` THEN
       FULL_SIMP_TAC bool_ss [APPEND, FILTER],

       Cases_on `l3` THEN (
         FULL_SIMP_TAC bool_ss [APPEND, FILTER, NOT_CONS_NIL, FILTER, CONS_11,
			        COND_RAND, COND_RATOR] THEN
         PROVE_TAC[]
       )
    ]
  ],

  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `h::l3` THEN Q.EXISTS_TAC `l4` THEN
    ASM_SIMP_TAC bool_ss [APPEND, FILTER],

    Cases_on `l3` THENL [
       Cases_on `l4` THEN
       FULL_SIMP_TAC bool_ss [APPEND, NOT_CONS_NIL, CONS_11] THEN
       Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `l` THEN
       FULL_SIMP_TAC bool_ss [FILTER, APPEND] THEN
       PROVE_TAC[],

       Q.EXISTS_TAC `l'` THEN Q.EXISTS_TAC `l4` THEN
       FULL_SIMP_TAC bool_ss [FILTER, APPEND, CONS_11] THEN
       PROVE_TAC[]
    ]
  ]
]);

val EVERY_FILTER = Q.store_thm
("EVERY_FILTER",
 `!P1 P2 l. EVERY P1 (FILTER P2 l) =
            EVERY (\x. P2 x ==> P1 x) l`,

GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN (
  ASM_SIMP_TAC bool_ss [FILTER, EVERY_DEF, COND_RATOR, COND_RAND]
));

val EVERY_FILTER_IMP = Q.store_thm
("EVERY_FILTER_IMP",
 `!P1 P2 l. EVERY P1 l ==> EVERY P1 (FILTER P2 l)`,
GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN (
  ASM_SIMP_TAC bool_ss [FILTER, EVERY_DEF, COND_RATOR, COND_RAND]
));

val FILTER_COND_REWRITE = Q.store_thm
("FILTER_COND_REWRITE",
 `(FILTER P [] = []) /\
  (!h. (P h) ==> ((FILTER P (h::l) = h::FILTER P l))) /\
  (!h. ~(P h) ==> (FILTER P (h::l) = FILTER P l))`,
SIMP_TAC bool_ss [FILTER]);

val NOT_NULL_MEM = Q.store_thm
("NOT_NULL_MEM",
 `!l. ~(NULL l) = (?e. MEM e l)`,
  Cases_on `l` THEN SIMP_TAC bool_ss [EXISTS_OR_THM, MEM, NOT_CONS_NIL, NULL]);

(* Computing EL when n is in numeral representation *)
val EL_compute = store_thm("EL_compute",
Term `!n. EL n l = if n=0 then HD l else EL (PRE n) (TL l)`,
INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC, EL, PRE]);

(* a version of the above that is safe to use in the simplifier *)
(* only bother with BIT1/2 cases because the zero case is already provided
   by the definition. *)
val EL_simp = store_thm(
  "EL_simp",
  ``(EL (NUMERAL (BIT1 n)) l = EL (PRE (NUMERAL (BIT1 n))) (TL l)) /\
    (EL (NUMERAL (BIT2 n)) l = EL (NUMERAL (BIT1 n)) (TL l))``,
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF,
               arithmeticTheory.BIT1, arithmeticTheory.BIT2,
               arithmeticTheory.ADD_CLAUSES,
               prim_recTheory.PRE, EL]);

val EL_restricted = store_thm(
  "EL_restricted",
  ``(EL 0 = HD) /\
    (EL (SUC n) (l::ls) = EL n ls)``,
  REWRITE_TAC [FUN_EQ_THM, EL, TL, HD]);
val _ = export_rewrites ["EL_restricted"]

val EL_simp_restricted = store_thm(
  "EL_simp_restricted",
  ``(EL (NUMERAL (BIT1 n)) (l::ls) = EL (PRE (NUMERAL (BIT1 n))) ls) /\
    (EL (NUMERAL (BIT2 n)) (l::ls) = EL (NUMERAL (BIT1 n)) ls)``,
  REWRITE_TAC [EL_simp, TL]);
val _ = export_rewrites ["EL_simp_restricted"]

val SUM_eq_0 = store_thm("SUM_eq_0",
  ``!ls. (SUM ls = 0) = !x. MEM x ls ==> (x = 0)``,
  LIST_INDUCT_TAC THEN SRW_TAC[][SUM,MEM] THEN METIS_TAC[])

val NULL_FILTER = store_thm("NULL_FILTER",
  ``!P ls. NULL (FILTER P ls) = !x. MEM x ls ==> ~P x``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  SRW_TAC[][NULL,FILTER,MEM] THEN METIS_TAC[])


val WF_LIST_PRED = store_thm("WF_LIST_PRED",
Term`WF \L1 L2. ?h:'a. L2 = h::L1`,
REWRITE_TAC[relationTheory.WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC CONTRAPOS_CONV
  THEN Ho_Rewrite.REWRITE_TAC
         [NOT_FORALL_THM,NOT_EXISTS_THM,NOT_IMP,DE_MORGAN_THM]
  THEN REWRITE_TAC [GSYM IMP_DISJ_THM] THEN STRIP_TAC
  THEN LIST_INDUCT_TAC THENL [ALL_TAC,GEN_TAC]
  THEN STRIP_TAC THEN RES_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_NIL_CONS,CONS_11])
  THENL [FIRST_ASSUM ACCEPT_TAC,
         PAT_ASSUM (Term`x /\ y`) (SUBST_ALL_TAC o CONJUNCT2) THEN RES_TAC]);

(* ----------------------------------------------------------------------
    LIST_REL : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

    Lifts a relation point-wise to two lists
   ---------------------------------------------------------------------- *)

val (LIST_REL_rules, LIST_REL_ind, LIST_REL_cases) = IndDefLib.Hol_reln`
  (LIST_REL R [] []) /\
  (!h1 h2 t1 t2. R h1 h2 /\ LIST_REL R t1 t2 ==> LIST_REL R (h1::t1) (h2::t2))
`;

val _ = overload_on ("listRel", ``LIST_REL``)
val _ = overload_on ("LIST_REL", ``LIST_REL``)

val LIST_REL_EL_EQN = store_thm(
  "LIST_REL_EL_EQN",
  ``!R l1 l2. LIST_REL R l1 l2 <=>
              (LENGTH l1 = LENGTH l2) /\
              !n. n < LENGTH l1 ==> R (EL n l1) (EL n l2)``,
  GEN_TAC THEN SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    Induct_on `LIST_REL` THEN SRW_TAC [][] THEN
    Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [],
    Induct_on `l1` THEN Cases_on `l2` THEN SRW_TAC [][LIST_REL_rules] THEN
    POP_ASSUM (fn th => Q.SPEC_THEN `0` MP_TAC th THEN
                        Q.SPEC_THEN `SUC m` (MP_TAC o Q.GEN `m`) th) THEN
    SRW_TAC [][LIST_REL_rules]
  ]);

val LIST_REL_def = store_thm(
  "LIST_REL_def",
  ``(LIST_REL R [][] <=> T) /\
    (LIST_REL R (a::as) [] <=> F) /\
    (LIST_REL R [] (b::bs) <=> F) /\
    (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs)``,
  REPEAT CONJ_TAC THEN SRW_TAC [][Once LIST_REL_cases, SimpLHS]);
val _ = export_rewrites ["LIST_REL_def"]

val LIST_REL_mono = store_thm(
  "LIST_REL_mono",
  ``(!x y. R1 x y ==> R2 x y) ==> LIST_REL R1 l1 l2 ==> LIST_REL R2 l1 l2``,
  SRW_TAC [][LIST_REL_EL_EQN]);
val _ = IndDefLib.export_mono "LIST_REL_mono"

val LIST_REL_NIL = store_thm(
  "LIST_REL_NIL",
  ``(LIST_REL R [] x <=> (x = [])) /\ (LIST_REL R [] y <=> (y = []))``,
  Cases_on `x` THEN Cases_on `y` THEN SRW_TAC [][]);
val _ = export_rewrites ["LIST_REL_NIL"]

val LIST_REL_CONS1 = store_thm(
  "LIST_REL_CONS1",
  ``LIST_REL R (h::t) xs <=> ?h' t'. (xs = h'::t') /\ R h h' /\ LIST_REL R t t'``,
  Cases_on `xs` THEN SRW_TAC [][]);

val LIST_REL_CONS2 = store_thm(
  "LIST_REL_CONS2",
  ``LIST_REL R xs (h::t) <=> ?h' t'. (xs = h'::t') /\ R h' h /\ LIST_REL R t' t``,
  Cases_on `xs` THEN SRW_TAC [][]);

val LIST_REL_CONJ = store_thm(
  "LIST_REL_CONJ",
  ``LIST_REL (\a b. P a b /\ Q a b) l1 l2 <=>
      LIST_REL (\a b. P a b) l1 l2 /\ LIST_REL (\a b. Q a b) l1 l2``,
  SRW_TAC [][LIST_REL_EL_EQN] THEN METIS_TAC []);

val LIST_REL_MAP1 = store_thm(
  "LIST_REL_MAP1",
  ``LIST_REL R (MAP f l1) l2 <=> LIST_REL (R o f) l1 l2``,
  SRW_TAC [][LIST_REL_EL_EQN, EL_MAP, LENGTH_MAP]);

val LIST_REL_MAP2 = store_thm(
  "LIST_REL_MAP2",
  ``LIST_REL (\a b. R a b) l1 (MAP f l2) <=>
      LIST_REL (\a b. R a (f b)) l1 l2``,
  SRW_TAC [CONJ_ss][LIST_REL_EL_EQN, EL_MAP, LENGTH_MAP]);

val LIST_REL_LENGTH = store_thm(
  "LIST_REL_LENGTH",
  ``!x y. LIST_REL R x y ==> (LENGTH x = LENGTH y)``,
  Induct_on `LIST_REL` THEN SRW_TAC [][LENGTH]);

(* example of LIST_REL in action :
val (rules,ind,cases) = IndDefLib.Hol_reln`
  (!n m. n < m ==> R n m) /\
  (!n m. R n m ==> R1 (INL n) (INL m)) /\
  (!l1 l2. LIST_REL R l1 l2 ==> R1 (INR l1) (INR l2))
`
val strong = IndDefLib.derive_strong_induction (rules,ind)
*)


(*---------------------------------------------------------------------------
     Congruence rules for higher-order functions. Used when making
     recursive definitions by so-called higher-order recursion.
 ---------------------------------------------------------------------------*)

val list_size_def =
  REWRITE_RULE [arithmeticTheory.ADD_ASSOC]
               (#2 (TypeBase.size_of ``:'a list``));

val Induct = INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC;

val list_size_cong = store_thm("list_size_cong",
Term
  `!M N f f'.
    (M=N) /\ (!x. MEM x N ==> (f x = f' x))
          ==>
    (list_size f M = list_size f' N)`,
Induct
  THEN REWRITE_TAC [list_size_def,MEM]
  THEN REPEAT STRIP_TAC
  THEN PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM)
  THEN REWRITE_TAC [list_size_def]
  THEN MK_COMB_TAC THENL
  [NTAC 2 (MK_COMB_TAC THEN TRY REFL_TAC)
     THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [MEM],
   FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [] THEN GEN_TAC
     THEN PAT_ASSUM (Term`!x. MEM x l ==> Q x`)
                    (MP_TAC o SPEC (Term`x:'a`))
     THEN REWRITE_TAC [MEM] THEN REPEAT STRIP_TAC
     THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val FOLDR_CONG = store_thm("FOLDR_CONG",
Term
  `!l l' b b' (f:'a->'b->'b) f'.
    (l=l') /\ (b=b') /\ (!x a. MEM x l' ==> (f x a = f' x a))
          ==>
    (FOLDR f b l = FOLDR f' b' l')`,
Induct
  THEN REWRITE_TAC [FOLDR,MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [FOLDR]
  THEN POP_ASSUM (fn th => MP_TAC (SPEC (Term`h`) th) THEN ASSUME_TAC th)
  THEN REWRITE_TAC [MEM]
  THEN DISCH_TAC
  THEN MK_COMB_TAC
  THENL [CONV_TAC FUN_EQ_CONV THEN ASM_REWRITE_TAC [],
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
           THEN REPEAT STRIP_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]);

val FOLDL_CONG = store_thm("FOLDL_CONG",
Term
  `!l l' b b' (f:'b->'a->'b) f'.
    (l=l') /\ (b=b') /\ (!x a. MEM x l' ==> (f a x = f' a x))
          ==>
    (FOLDL f b l = FOLDL f' b' l')`,
Induct
  THEN REWRITE_TAC [FOLDL,MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [FOLDL]
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN REWRITE_TAC[]
  THEN CONJ_TAC
  THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [MEM],
         REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]);


val MAP_CONG = store_thm("MAP_CONG",
Term
  `!l1 l2 f f'.
    (l1=l2) /\ (!x. MEM x l2 ==> (f x = f' x))
          ==>
    (MAP f l1 = MAP f' l2)`,
Induct THEN REWRITE_TAC [MAP,MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [MAP]
  THEN MK_COMB_TAC
  THENL [MK_COMB_TAC THEN TRY REFL_TAC
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN REWRITE_TAC [MEM],
         FIRST_ASSUM MATCH_MP_TAC
             THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC [MEM]]);

val MAP2_CONG = store_thm("MAP2_CONG",
Term
  `!l1 l1' l2 l2' f f'.
    (l1=l1') /\ (l2=l2') /\
    (!x y. MEM x l1' /\ MEM y l2' ==> (f x y = f' x y))
          ==>
    (MAP2 f l1 l2 = MAP2 f' l1' l2')`,
Induct THEN SRW_TAC[][MAP2_DEF,MEM] THEN
SRW_TAC[][MAP2_DEF] THEN
Cases_on `l2` THEN
SRW_TAC[][MAP2_DEF])

val EXISTS_CONG = store_thm("EXISTS_CONG",
Term
  `!l1 l2 P P'.
    (l1=l2) /\ (!x. MEM x l2 ==> (P x = P' x))
          ==>
    (EXISTS P l1 = EXISTS P' l2)`,
Induct THEN REWRITE_TAC [EXISTS_DEF,MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM))
  THENL [PAT_ASSUM (Term`EXISTS x y`) MP_TAC THEN REWRITE_TAC [EXISTS_DEF],
         REWRITE_TAC [EXISTS_DEF]
           THEN MK_COMB_TAC
           THENL [MK_COMB_TAC THEN TRY REFL_TAC
                    THEN FIRST_ASSUM MATCH_MP_TAC
                    THEN REWRITE_TAC [MEM],
                  FIRST_ASSUM MATCH_MP_TAC
                    THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
                    THEN FIRST_ASSUM MATCH_MP_TAC
                    THEN ASM_REWRITE_TAC [MEM]]]);;


val EVERY_CONG = store_thm("EVERY_CONG",
Term
  `!l1 l2 P P'.
    (l1=l2) /\ (!x. MEM x l2 ==> (P x = P' x))
          ==>
    (EVERY P l1 = EVERY P' l2)`,
Induct THEN REWRITE_TAC [EVERY_DEF,MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_ASSUM (Term`x = y`) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [EVERY_DEF]
  THEN MK_COMB_TAC
  THENL [MK_COMB_TAC THEN TRY REFL_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [MEM],
         FIRST_ASSUM MATCH_MP_TAC
           THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]);

val EVERY_MONOTONIC = store_thm(
  "EVERY_MONOTONIC",
  ``!(P:'a -> bool) Q.
       (!x. P x ==> Q x) ==> !l. EVERY P l ==> EVERY Q l``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC [EVERY_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC);

(* ----------------------------------------------------------------------
   ZIP and UNZIP functions (taken from rich_listTheory)
   ---------------------------------------------------------------------- *)
val ZIP =
    let val lemma = prove(
    (--`?ZIP. (ZIP ([], []) = []) /\
       (!(x1:'a) l1 (x2:'b) l2.
        ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))`--),
    let val th = prove_rec_fn_exists list_Axiom
        (--`(fn [] l = []) /\
         (fn (CONS (x:'a) l') (l:'b list) =
                           CONS (x, (HD l)) (fn  l' (TL l)))`--)
        in
    STRIP_ASSUME_TAC th
    THEN EXISTS_TAC
           (--`UNCURRY (fn:('a)list -> (('b)list -> ('a # 'b)list))`--)
    THEN ASM_REWRITE_TAC[pairTheory.UNCURRY_DEF,HD,TL]
     end)
    in
    Rsyntax.new_specification
        {consts = [{const_name = "ZIP", fixity = NONE}],
         name = "ZIP",
         sat_thm = lemma
        }
    end;

val UNZIP = new_recursive_definition {
  name = "UNZIP",   rec_axiom = list_Axiom,
  def  = ``(UNZIP [] = ([], [])) /\
    (!x l. UNZIP (CONS (x:'a # 'b) l) =
               (CONS (FST x) (FST (UNZIP l)),
                CONS (SND x) (SND (UNZIP l))))``}

val UNZIP_THM = Q.store_thm
("UNZIP_THM",
 `(UNZIP [] = ([]:'a list,[]:'b list)) /\
  (UNZIP ((x:'a,y:'b)::t) = let (L1,L2) = UNZIP t in (x::L1, y::L2))`,
 RW_TAC bool_ss [UNZIP]
   THEN Cases_on `UNZIP t`
   THEN RW_TAC bool_ss [LET_THM,pairTheory.UNCURRY_DEF,
                        pairTheory.FST,pairTheory.SND]);

val UNZIP_MAP = Q.store_thm
("UNZIP_MAP",
 `!L. UNZIP L = (MAP FST L, MAP SND L)`,
 LIST_INDUCT_TAC THEN
 ASM_SIMP_TAC arith_ss [UNZIP, MAP,
    PAIR_EQ, pairTheory.FST, pairTheory.SND]);

val SUC_NOT = arithmeticTheory.SUC_NOT
val LENGTH_ZIP = store_thm("LENGTH_ZIP",
  --`!(l1:'a list) (l2:'b list).
         (LENGTH l1 = LENGTH l2) ==>
         (LENGTH(ZIP(l1,l2)) = LENGTH l1) /\
         (LENGTH(ZIP(l1,l2)) = LENGTH l2)`--,
  LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--)) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ZIP,LENGTH,NOT_SUC,SUC_NOT,INV_SUC_EQ] THEN
  DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LENGTH_UNZIP = store_thm(
  "LENGTH_UNZIP",
  ``!pl. (LENGTH (FST (UNZIP pl)) = LENGTH pl) /\
         (LENGTH (SND (UNZIP pl)) = LENGTH pl)``,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [UNZIP, LENGTH]);

val ZIP_UNZIP = store_thm("ZIP_UNZIP",
    (--`!l:('a # 'b)list. ZIP(UNZIP l) = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,ZIP]);

val UNZIP_ZIP = store_thm("UNZIP_ZIP",
    (--`!l1:'a list. !l2:'b list.
     (LENGTH l1 = LENGTH l2) ==> (UNZIP(ZIP(l1,l2)) = (l1,l2))`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[UNZIP,ZIP,LENGTH,NOT_SUC,SUC_NOT,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);


val ZIP_MAP = store_thm(
  "ZIP_MAP",
  ``!l1 l2 f1 f2.
       (LENGTH l1 = LENGTH l2) ==>
       (ZIP (MAP f1 l1, l2) = MAP (\p. (f1 (FST p), SND p)) (ZIP (l1, l2))) /\
       (ZIP (l1, MAP f2 l2) = MAP (\p. (FST p, f2 (SND p))) (ZIP (l1, l2)))``,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LENGTH] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THENL [
    Q.SUBGOAL_THEN `l2 = []` SUBST_ALL_TAC THEN
    REWRITE_TAC [ZIP, MAP] THEN mesonLib.ASM_MESON_TAC [LENGTH_NIL],
    Q.SUBGOAL_THEN
       `?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)`
    STRIP_ASSUME_TAC THENL [
      mesonLib.ASM_MESON_TAC [LENGTH_CONS],
      ASM_SIMP_TAC bool_ss [ZIP, MAP, FST, SND]
    ]
  ]);

val MEM_ZIP = store_thm(
  "MEM_ZIP",
  ``!(l1:'a list) (l2:'b list) p.
       (LENGTH l1 = LENGTH l2) ==>
       (MEM p (ZIP(l1, l2)) =
        ?n. n < LENGTH l1 /\ (p = (EL n l1, EL n l2)))``,
  LIST_INDUCT_TAC THEN SIMP_TAC bool_ss [LENGTH] THEN REPEAT STRIP_TAC THENL [
    `l2 = []`  by ASM_MESON_TAC [LENGTH_NIL] THEN
    FULL_SIMP_TAC arith_ss [ZIP, MEM, LENGTH],
    `?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)`
      by ASM_MESON_TAC [LENGTH_CONS] THEN
    FULL_SIMP_TAC arith_ss [MEM,ZIP,LENGTH] THEN EQ_TAC THEN
    STRIP_TAC THENL [
      Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC arith_ss [EL, HD],
      Q.EXISTS_TAC `SUC n` THEN ASM_SIMP_TAC arith_ss [EL,TL],
      Cases_on `n` THEN FULL_SIMP_TAC arith_ss [EL,HD,TL] THEN
      ASM_MESON_TAC []
    ]
  ]);

val EL_ZIP = store_thm(
  "EL_ZIP",
  ``!(l1:'a list) (l2:'b list) n.
        (LENGTH l1 = LENGTH l2) /\ n < LENGTH l1 ==>
        (EL n (ZIP (l1, l2)) = (EL n l1, EL n l2))``,
  Induct THEN SIMP_TAC arith_ss [LENGTH] THEN REPEAT STRIP_TAC THEN
  `?l2h l2t. (l2 = l2h::l2t) /\ (LENGTH l2t = LENGTH l1)`
     by ASM_MESON_TAC [LENGTH_CONS] THEN
  FULL_SIMP_TAC arith_ss [ZIP,LENGTH] THEN
  Cases_on `n` THEN ASM_SIMP_TAC arith_ss [ZIP,EL,HD,TL]);


val MAP2_ZIP = store_thm("MAP2_ZIP",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !f:'a->'b->'c. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))`--),
    let val UNCURRY_DEF = pairTheory.UNCURRY_DEF
    in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,MAP2,ZIP,LENGTH,NOT_SUC,SUC_NOT]
    THEN ASM_REWRITE_TAC[CONS_11,UNCURRY_DEF,INV_SUC_EQ]
    end);

val MAP2_MAP = save_thm("MAP2_MAP",MAP2_ZIP)

val MAP_ZIP = Q.store_thm(
  "MAP_ZIP",
  `(LENGTH l1 = LENGTH l2) ==>
     (MAP FST (ZIP (l1,l2)) = l1) /\
     (MAP SND (ZIP (l1,l2)) = l2) /\
     (MAP (f o FST) (ZIP (l1,l2)) = MAP f l1) /\
     (MAP (g o SND) (ZIP (l1,l2)) = MAP g l2)`,
  Q.ID_SPEC_TAC `l2` THEN Induct_on `l1` THEN
  SRW_TAC [][] THEN Cases_on `l2` THEN
  FULL_SIMP_TAC (srw_ss()) [ZIP, MAP]);

val MEM_EL = store_thm(
  "MEM_EL",
  ``!(l:'a list) x. MEM x l = ?n. n < LENGTH l /\ (x = EL n l)``,
  Induct THEN ASM_SIMP_TAC arith_ss [MEM,LENGTH] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC arith_ss [EL, HD],
    Q.EXISTS_TAC `SUC n` THEN ASM_SIMP_TAC arith_ss [EL, TL],
    Cases_on `n` THEN FULL_SIMP_TAC arith_ss [EL, HD, TL] THEN
    ASM_MESON_TAC []
  ]);

val SUM_MAP_PLUS_ZIP = store_thm(
  "SUM_MAP_PLUS_ZIP",
  ``!ls1 ls2. (LENGTH ls1 = LENGTH ls2) /\ (!x y. f (x,y) = g x + h y) ==>
              (SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2))``,
  Induct THEN Cases_on `ls2` THEN
  SRW_TAC [numSimps.ARITH_ss][MAP,ZIP,MAP_ZIP,SUM]);

val LIST_REL_EVERY_ZIP = store_thm(
"LIST_REL_EVERY_ZIP",
``!R l1 l2. LIST_REL R l1 l2 = ((LENGTH l1 = LENGTH l2) /\ EVERY (UNCURRY R) (ZIP (l1,l2)))``,
GEN_TAC THEN Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
SRW_TAC[][EQ_IMP_THM,LIST_REL_CONS1] THEN SRW_TAC[][EVERY_DEF,ZIP] THEN
Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[EVERY_DEF,ZIP])

(* --------------------------------------------------------------------- *)
(* REVERSE                                                               *)
(* --------------------------------------------------------------------- *)

val REVERSE_DEF = new_recursive_definition {
  name = "REVERSE_DEF",
  rec_axiom = list_Axiom,
  def = ``(REVERSE [] = []) /\
          (REVERSE (h::t) = (REVERSE t) ++ [h])``};
val _ = export_rewrites ["REVERSE_DEF"]

val REVERSE_APPEND = store_thm(
  "REVERSE_APPEND",
  ``!l1 l2:'a list.
       REVERSE (l1 ++ l2) = (REVERSE l2) ++ (REVERSE l1)``,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, REVERSE_DEF, APPEND_NIL, APPEND_ASSOC]);

val REVERSE_REVERSE = store_thm(
  "REVERSE_REVERSE",
  ``!l:'a list. REVERSE (REVERSE l) = l``,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE_DEF, REVERSE_APPEND, APPEND]);
val _ = export_rewrites ["REVERSE_REVERSE"]

val REVERSE_11 = store_thm(
  "REVERSE_11",
 ``!l1 l2:'a list. (REVERSE l1 = REVERSE l2) <=> (l1 = l2)``,
 REPEAT GEN_TAC THEN EQ_TAC THEN1
   (DISCH_THEN (MP_TAC o AP_TERM ``REVERSE : 'a list -> 'a list``) THEN
    REWRITE_TAC [REVERSE_REVERSE]) THEN
 STRIP_TAC THEN ASM_REWRITE_TAC []);
val _ = export_rewrites ["REVERSE_11"]

val MEM_REVERSE = store_thm(
  "MEM_REVERSE",
  ``!l x. MEM x (REVERSE l) = MEM x l``,
  Induct THEN SRW_TAC [][] THEN PROVE_TAC []);
val _ = export_rewrites ["MEM_REVERSE"]

val LENGTH_REVERSE = store_thm(
  "LENGTH_REVERSE",
  ``!l. LENGTH (REVERSE l) = LENGTH l``,
  Induct THEN SRW_TAC [][arithmeticTheory.ADD1]);
val _ = export_rewrites ["LENGTH_REVERSE"]

val REVERSE_EQ_NIL = store_thm(
  "REVERSE_EQ_NIL",
  ``(REVERSE l = []) <=> (l = [])``,
  Cases_on `l` THEN SRW_TAC [][]);
val _ = export_rewrites ["REVERSE_EQ_NIL"]

val REVERSE_EQ_SING = store_thm(
  "REVERSE_EQ_SING",
  ``(REVERSE l = [e:'a]) <=> (l = [e])``,
  Cases_on `l` THEN SRW_TAC [][APPEND_EQ_SING, CONJ_COMM]);
val _ = export_rewrites ["REVERSE_EQ_SING"]

val FILTER_REVERSE = store_thm(
  "FILTER_REVERSE",
  ``!l P. FILTER P (REVERSE l) = REVERSE (FILTER P l)``,
  Induct THEN
  ASM_SIMP_TAC bool_ss [FILTER, REVERSE_DEF, FILTER_APPEND_DISTRIB,
    COND_RAND, COND_RATOR, APPEND_NIL]);


(* ----------------------------------------------------------------------
    FRONT and LAST
   ---------------------------------------------------------------------- *)

val LAST_DEF = new_recursive_definition {
  name = "LAST_DEF",
  rec_axiom = list_Axiom,
  def = ``LAST (h::t) = if t = [] then h else LAST t``};

val FRONT_DEF = new_recursive_definition {
  name = "FRONT_DEF",
  rec_axiom = list_Axiom,
  def = ``FRONT (h::t) = if t = [] then [] else h :: FRONT t``};

val LAST_CONS = store_thm(
  "LAST_CONS",
  ``(!x:'a. LAST [x] = x) /\
    (!(x:'a) y z. LAST (x::y::z) = LAST(y::z))``,
  REWRITE_TAC [LAST_DEF, NOT_CONS_NIL]);
val _ = export_rewrites ["LAST_CONS"]

val LAST_EL = store_thm(
"LAST_EL",
``!ls. (ls <> []) ==> (LAST ls = EL (PRE (LENGTH ls)) ls)``,
Induct THEN SRW_TAC[][] THEN
Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [])

val FRONT_CONS = store_thm(
  "FRONT_CONS",
  ``(!x:'a. FRONT [x] = []) /\
    (!x:'a y z. FRONT (x::y::z) = x :: FRONT (y::z))``,
  REWRITE_TAC [FRONT_DEF, NOT_CONS_NIL]);
val _ = export_rewrites ["FRONT_CONS"]

val LENGTH_FRONT_CONS = store_thm ("LENGTH_FRONT_CONS",
``!x xs. LENGTH (FRONT (x::xs)) = LENGTH xs``,
Induct_on `xs` THEN ASM_SIMP_TAC bool_ss [FRONT_CONS, LENGTH])
val _ = export_rewrites ["LENGTH_FRONT_CONS"]

val FRONT_CONS_EQ_NIL = store_thm ("FRONT_CONS_EQ_NIL",
``(!x:'a xs. (FRONT (x::xs) = []) = (xs = [])) /\
  (!x:'a xs. ([] = FRONT (x::xs)) = (xs = [])) /\
  (!x:'a xs. NULL (FRONT (x::xs)) = NULL xs)``,
SIMP_TAC bool_ss [GSYM FORALL_AND_THM] THEN
Cases_on `xs` THEN SIMP_TAC bool_ss [FRONT_CONS, NOT_NIL_CONS, NULL_DEF]);
val _ = export_rewrites ["FRONT_CONS_EQ_NIL"]

val APPEND_FRONT_LAST = store_thm(
  "APPEND_FRONT_LAST",
  ``!l:'a list. ~(l = []) ==> (APPEND (FRONT l) [LAST l] = l)``,
  LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL] THEN
  POP_ASSUM MP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC [NOT_CONS_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [FRONT_CONS, LAST_CONS, APPEND]);

val LAST_CONS_cond = store_thm(
  "LAST_CONS_cond",
  ``LAST (h::t) = if t = [] then h else LAST t``,
  Cases_on `t` THEN SRW_TAC [][]);

val LAST_APPEND_CONS = store_thm(
  "LAST_APPEND_CONS",
  ``!h l1 l2. LAST (l1 ++ h::l2) = LAST (h::l2)``,
  Induct_on `l1` THEN SRW_TAC [][LAST_CONS_cond]);
val _ = export_rewrites ["LAST_APPEND_CONS"]


(* ----------------------------------------------------------------------
    TAKE and DROP
   ---------------------------------------------------------------------- *)

(* these are FIRSTN and BUTFIRSTN from rich_listTheory, but made total *)

val TAKE_def = zDefine`
  (TAKE n [] = []) /\
  (TAKE n (x::xs) = if n = 0 then [] else x :: TAKE (n - 1) xs)
`;
val _ = export_rewrites ["TAKE_def"]

val DROP_def = zDefine`
  (DROP n [] = []) /\
  (DROP n (x::xs) = if n = 0 then x::xs else DROP (n - 1) xs)
`;
val _ = export_rewrites ["DROP_def"]

val TAKE_0 = store_thm(
  "TAKE_0",
  ``TAKE 0 l = []``,
  Cases_on `l` THEN SRW_TAC [][]);
val _  = export_rewrites ["TAKE_0"]

val TAKE_LENGTH_ID = store_thm(
  "TAKE_LENGTH_ID",
  ``!l. TAKE (LENGTH l) l = l``,
  Induct_on `l` THEN SRW_TAC [][]);
val _ = export_rewrites ["TAKE_LENGTH_ID"]

val LENGTH_TAKE = store_thm(
  "LENGTH_TAKE",
  ``!n l. n <= LENGTH l ==> (LENGTH (TAKE n l) = n)``,
  Induct_on `l` THEN SRW_TAC [numSimps.ARITH_ss][]);
val _ = export_rewrites ["LENGTH_TAKE"]

val TAKE_APPEND1 = store_thm(
  "TAKE_APPEND1",
  ``!n. n <= LENGTH l1 ==> (TAKE n (APPEND l1 l2) = TAKE n l1)``,
  Induct_on `l1` THEN SRW_TAC [numSimps.ARITH_ss][]);

val TAKE_APPEND2 = store_thm(
  "TAKE_APPEND2",
  ``!n. LENGTH l1 < n ==> (TAKE n (l1 ++ l2) = l1 ++ TAKE (n - LENGTH l1) l2)``,
  Induct_on `l1` THEN SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.ADD1]);

val DROP_0 = store_thm(
  "DROP_0",
  ``DROP 0 l = l``,
  Induct_on `l` THEN SRW_TAC [][])
val _ = export_rewrites ["DROP_0"]

val TAKE_DROP = store_thm(
  "TAKE_DROP",
  ``!n l. TAKE n l ++ DROP n l = l``,
  Induct_on `l` THEN SRW_TAC [numSimps.ARITH_ss][]);
val _ = export_rewrites ["TAKE_DROP"]

val LENGTH_DROP = store_thm(
  "LENGTH_DROP",
  ``!n l. LENGTH (DROP n l) = LENGTH l - n``,
  Induct_on `l` THEN SRW_TAC [numSimps.ARITH_ss][]);
val _ = export_rewrites ["LENGTH_DROP"]

val MEM_DROP = store_thm(
"MEM_DROP",
``!x ls n. MEM x (DROP n ls) = (n < LENGTH ls /\ (x = (EL n ls))) \/ MEM x (DROP (SUC n) ls)``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
NTAC 2 GEN_TAC THEN
SIMP_TAC (srw_ss()) [] THEN
Cases_on `n` THEN SIMP_TAC (srw_ss()) [] THEN
PROVE_TAC[])

val DROP_NIL = store_thm(
"DROP_NIL",
``!ls n. (DROP n ls = []) = (n >= LENGTH ls)``,
Induct THEN SRW_TAC[][] THEN numLib.DECIDE_TAC)

(* More functions for operating on pairs of lists *)

val FOLDL2_def = Define`
  (FOLDL2 f a (b::bs) (c::cs) = FOLDL2 f (f a b c) bs cs) /\
  (FOLDL2 f a bs cs = a)`
val _ = export_rewrites["FOLDL2_def"]
val _ = delete_const "FOLDL2_tupled"

val FOLDL2_cong = store_thm(
"FOLDL2_cong",
``!l1 l1' l2 l2' a a' f f'.
  (l1 = l1') /\ (l2 = l2') /\ (a = a') /\
  (!z b c. MEM b l1' /\ MEM c l2' ==> (f z b c = f' z b c))
  ==>
  (FOLDL2 f a l1 l2 = FOLDL2 f' a' l1' l2')``,
Induct THEN SIMP_TAC(srw_ss()) [FOLDL2_def] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][FOLDL2_def])

val FOLDL2_FOLDL = store_thm(
"FOLDL2_FOLDL",
``!l1 l2. (LENGTH l1 = LENGTH l2) ==> !f a. FOLDL2 f a l1 l2 = FOLDL (\a. UNCURRY (f a)) a (ZIP (l1,l2))``,
Induct THEN1 SRW_TAC[][LENGTH_NIL_SYM,ZIP,FOLDL] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][ZIP,FOLDL])

val _ = overload_on ("EVERY2", ``LIST_REL``)
val _ = overload_on ("LIST_REL", ``LIST_REL``)

val EVERY2_cong = store_thm(
"EVERY2_cong",
``!l1 l1' l2 l2' P P'.
  (l1 = l1') /\ (l2 = l2') /\
  (!x y. MEM x l1' /\ MEM y l2' ==> (P x y = P' x y)) ==>
  (EVERY2 P l1 l2 = EVERY2 P' l1' l2')``,
Induct THEN SIMP_TAC (srw_ss()) [] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][] THEN
METIS_TAC[])

val MAP_EQ_EVERY2 = store_thm(
"MAP_EQ_EVERY2",
``!f1 f2 l1 l2. (MAP f1 l1 = MAP f2 l2) =
                (LENGTH l1 = LENGTH l2) /\
                (EVERY2 (\x y. f1 x = f2 y) l1 l2)``,
NTAC 2 GEN_TAC THEN
Induct THEN SRW_TAC[][LENGTH_NIL_SYM,MAP,MAP_EQ_NIL] THEN
Cases_on `l2` THEN SRW_TAC[][MAP] THEN
PROVE_TAC[])

val EVERY2_EVERY = store_thm(
"EVERY2_EVERY",
``!l1 l2 f. EVERY2 f l1 l2 = (LENGTH l1 = LENGTH l2) /\ EVERY (UNCURRY f) (ZIP (l1,l2))``,
Induct THEN1 SRW_TAC[][LENGTH_NIL_SYM,EQ_IMP_THM,ZIP] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][ZIP,EQ_IMP_THM])

val EVERY2_LENGTH = store_thm(
"EVERY2_LENGTH",
``!P l1 l2. EVERY2 P l1 l2 ==> (LENGTH l1 = LENGTH l2)``,
PROVE_TAC[EVERY2_EVERY])

val EVERY2_mono = save_thm("EVERY2_mono", LIST_REL_mono)

(* ----------------------------------------------------------------------
    ALL_DISTINCT
   ---------------------------------------------------------------------- *)

val ALL_DISTINCT = new_recursive_definition {
  def = Term`(ALL_DISTINCT [] = T) /\
             (ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t)`,
  name = "ALL_DISTINCT",
  rec_axiom = list_Axiom};
val _ = export_rewrites ["ALL_DISTINCT"]

val lemma = prove(
  ``!l x. (FILTER ((=) x) l = []) = ~MEM x l``,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (bool_ss ++ COND_elim_ss)
               [FILTER, MEM, NOT_CONS_NIL, EQ_IMP_THM,
                LEFT_AND_OVER_OR, FORALL_AND_THM, DISJ_IMP_THM]);

val ALL_DISTINCT_FILTER = store_thm(
  "ALL_DISTINCT_FILTER",
  ``!l. ALL_DISTINCT l = !x. MEM x l ==> (FILTER ((=) x) l = [x])``,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC (bool_ss ++ COND_elim_ss)
               [ALL_DISTINCT, MEM, FILTER, DISJ_IMP_THM,
                FORALL_AND_THM, CONS_11, EQ_IMP_THM, lemma] THEN
  metisLib.METIS_TAC []);

val FILTER_ALL_DISTINCT = store_thm (
  "FILTER_ALL_DISTINCT",
  ``!P l. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)``,
  Induct_on `l` THEN SRW_TAC [][MEM_FILTER]);

val ALL_DISTINCT_MAP = store_thm(
"ALL_DISTINCT_MAP",
``!f ls. ALL_DISTINCT (MAP f ls) ==> ALL_DISTINCT ls``,
GEN_TAC THEN Induct THEN SRW_TAC[][ALL_DISTINCT, MAP, MEM_MAP] THEN PROVE_TAC[])

val ALL_DISTINCT_EL_EQ = store_thm (
   "EL_ALL_DISTINCT_EL_EQ",
   ``!l. ALL_DISTINCT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
                 ((EL n1 l = EL n2 l) = (n1 = n2)))``,
  Induct THEN SRW_TAC [][] THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN Cases_on `n1` THEN Cases_on `n2` THEN
    SRW_TAC [numSimps.ARITH_ss][] THEN PROVE_TAC [MEM_EL, LESS_MONO_EQ],

    REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`0`, `SUC n`] MP_TAC) THEN
      SRW_TAC [][],

      FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n1`, `SUC n2`] MP_TAC) THEN
      SRW_TAC [][]
    ]
  ]);

val ALL_DISTINCT_EL_IMP = store_thm (
   "ALL_DISTINCT_EL_IMP",
   ``!l n1 n2. ALL_DISTINCT l /\ n1 < LENGTH l /\ n2 < LENGTH l ==>
               ((EL n1 l = EL n2 l) = (n1 = n2))``,
   PROVE_TAC[ALL_DISTINCT_EL_EQ]);


val ALL_DISTINCT_APPEND = store_thm (
   "ALL_DISTINCT_APPEND",
   ``!l1 l2. ALL_DISTINCT (l1++l2) =
             (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
             (!e. MEM e l1 ==> ~(MEM e l2)))``,
  Induct THEN SRW_TAC [][] THEN PROVE_TAC []);

val ALL_DISTINCT_SING = store_thm(
   "ALL_DISTINCT_SING",
   ``!x. ALL_DISTINCT [x]``,
   SRW_TAC [][]);

val ALL_DISTINCT_ZIP = store_thm(
   "ALL_DISTINCT_ZIP",
   ``!l1 l2. ALL_DISTINCT l1 /\ (LENGTH l1 = LENGTH l2) ==> ALL_DISTINCT (ZIP (l1,l2))``,
   Induct THEN Cases_on `l2` THEN SRW_TAC [][ZIP] THEN RES_TAC THEN
   FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
   SRW_TAC [][LENGTH_ZIP] THEN
   Q.MATCH_ABBREV_TAC `~X \/ Y` THEN
   Cases_on `X` THEN SRW_TAC [][Abbr`Y`] THEN
   SRW_TAC [][EL_ZIP] THEN METIS_TAC []);

val ALL_DISTINCT_ZIP_SWAP = store_thm(
   "ALL_DISTINCT_ZIP_SWAP",
   ``!l1 l2. ALL_DISTINCT (ZIP (l1,l2)) /\ (LENGTH l1 = LENGTH l2) ==> ALL_DISTINCT (ZIP (l2,l1))``,
   SRW_TAC [][ALL_DISTINCT_EL_EQ] THEN
   Q.PAT_ASSUM `X = Y` (ASSUME_TAC o SYM) THEN
   FULL_SIMP_TAC (srw_ss()) [EL_ZIP,LENGTH_ZIP] THEN
   METIS_TAC [])

val ALL_DISTINCT_REVERSE = store_thm (
   "ALL_DISTINCT_REVERSE",
   ``!l. ALL_DISTINCT (REVERSE l) = ALL_DISTINCT l``,
   SIMP_TAC bool_ss [ALL_DISTINCT_FILTER, MEM_REVERSE, FILTER_REVERSE] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      RES_TAC THEN
      `(FILTER ($= x) l) = REVERSE [x]` by METIS_TAC[REVERSE_REVERSE] THEN
      FULL_SIMP_TAC bool_ss [REVERSE_DEF, APPEND],
      ASM_SIMP_TAC bool_ss [REVERSE_DEF, APPEND]
   ]);


(* ----------------------------------------------------------------------
    LRC
      Where NRC has the number of steps in a transitive path,
      LRC has a list of the elements in the path (excluding the rightmost)
   ---------------------------------------------------------------------- *)

val LRC_def = Define`
  (LRC R [] x y = (x = y)) /\
  (LRC R (h::t) x y =
   (x = h) /\ ?z. R x z /\ LRC R t z y)`;

val NRC_LRC = Q.store_thm(
"NRC_LRC",
`NRC R n x y <=> ?ls. LRC R ls x y /\ (LENGTH ls = n)`,
MAP_EVERY Q.ID_SPEC_TAC [`y`,`x`] THEN
Induct_on `n` THEN SRW_TAC [][] THEN1 (
  SRW_TAC [][EQ_IMP_THM] THEN1 (
    Q.EXISTS_TAC `[]` THEN SRW_TAC [][LRC_def] ) THEN
  Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def]
) THEN
SRW_TAC [][arithmeticTheory.NRC,EQ_IMP_THM] THEN1 (
  Q.EXISTS_TAC `x::ls` THEN
  SRW_TAC [][LRC_def] THEN
  METIS_TAC [] ) THEN
Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
SRW_TAC [][] THEN METIS_TAC []);

val LRC_MEM = Q.store_thm(
"LRC_MEM",
`LRC R ls x y /\ MEM e ls ==> ?z t. R e z /\ LRC R t z y`,
Q_TAC SUFF_TAC
`!ls x y. LRC R ls x y ==> !e. MEM e ls ==> ?z t. R e z /\ LRC R t z y`
THEN1 METIS_TAC [] THEN
Induct THEN SRW_TAC [][LRC_def] THEN METIS_TAC []);

val LRC_MEM_right = Q.store_thm(
"LRC_MEM_right",
`LRC R (h::t) x y /\ MEM e t ==> ?z p. R z e /\ LRC R p x z`,
Q_TAC SUFF_TAC
`!ls x y. LRC R ls x y ==> !h t e. (ls = h::t) /\ MEM e t ==> ?z p. R z e /\ LRC R p x z`
THEN1 METIS_TAC [] THEN
Induct THEN SRW_TAC [][LRC_def] THEN
Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
SRW_TAC [][] THENL [
  MAP_EVERY Q.EXISTS_TAC [`h`,`[]`] THEN SRW_TAC [][LRC_def],
  RES_TAC THEN
  MAP_EVERY Q.EXISTS_TAC  [`z''`,`h::p`] THEN
  SRW_TAC [][LRC_def] THEN
  METIS_TAC []
]);

(* ----------------------------------------------------------------------
    Theorems relating (finite) sets and lists.  First

       LIST_TO_SET : 'a list -> 'a set

    which is overloaded to "set".
   ---------------------------------------------------------------------- *)

val LIST_TO_SET_APPEND = Q.store_thm
("LIST_TO_SET_APPEND",
 `!l1 l2. set (l1 ++ l2) = set l1 UNION set l2`,
 Induct THEN SRW_TAC [][INSERT_UNION_EQ]);
val _ = export_rewrites ["LIST_TO_SET_APPEND"]

val UNION_APPEND = save_thm ("UNION_APPEND", GSYM LIST_TO_SET_APPEND)

val LIST_TO_SET_EQ_EMPTY = store_thm(
  "LIST_TO_SET_EQ_EMPTY",
  ``((set l = {}) <=> (l = [])) /\ (({} = set l) <=> (l = []))``,
  Cases_on `l` THEN SRW_TAC [][]);
val _ = export_rewrites ["LIST_TO_SET_EQ_EMPTY"]

val FINITE_LIST_TO_SET = Q.store_thm
("FINITE_LIST_TO_SET",
 `!l. FINITE (set l)`,
 Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_LIST_TO_SET"]

val SUM_IMAGE_LIST_TO_SET_upper_bound = store_thm(
  "SUM_IMAGE_LIST_TO_SET_upper_bound",
  ``!ls. SIGMA f (set ls) <= SUM (MAP f ls)``,
  Induct THEN
  SRW_TAC [][MAP,SUM,SUM_IMAGE_THM,SUM_IMAGE_DELETE] THEN
  numLib.DECIDE_TAC);

val SUM_MAP_MEM_bound = store_thm(
"SUM_MAP_MEM_bound",
``!f x ls. MEM x ls ==> f x <= SUM (MAP f ls)``,
NTAC 2 GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
FULL_SIMP_TAC(srw_ss()++numSimps.ARITH_ss)[MEM,MAP,SUM])

val INJ_MAP_EQ = store_thm(
"INJ_MAP_EQ",
``!f l1 l2. (INJ f (set l1 UNION set l2) UNIV) /\ (MAP f l1 = MAP f l2) ==> (l1 = l2)``,
GEN_TAC THEN Induct THEN1 SRW_TAC[][MAP,MAP_EQ_NIL] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][MAP] THEN1 (
  IMP_RES_TAC INJ_DEF THEN
  FIRST_X_ASSUM (MATCH_MP_TAC o MP_CANON) THEN
  SRW_TAC[][] ) THEN
PROVE_TAC[INJ_SUBSET,SUBSET_REFL,SUBSET_DEF,IN_UNION,IN_INSERT])

local open numLib in
val CARD_LIST_TO_SET = Q.store_thm(
"CARD_LIST_TO_SET",
`CARD (set ls) <= LENGTH ls`,
Induct_on `ls` THEN SRW_TAC [][] THEN
DECIDE_TAC);
end

val ALL_DISTINCT_CARD_LIST_TO_SET = Q.store_thm(
"ALL_DISTINCT_CARD_LIST_TO_SET",
`!ls. ALL_DISTINCT ls ==> (CARD (set ls) = LENGTH ls)`,
Induct THEN SRW_TAC [][]);

val LIST_TO_SET_REVERSE = store_thm(
  "LIST_TO_SET_REVERSE",
  ``!ls: 'a list. set (REVERSE ls) = set ls``,
  Induct THEN SRW_TAC [][pred_setTheory.EXTENSION]);
val _ = export_rewrites ["LIST_TO_SET_REVERSE"]

val LIST_TO_SET_THM = save_thm("LIST_TO_SET_THM", LIST_TO_SET)
val LIST_TO_SET_MAP = store_thm ("LIST_TO_SET_MAP",
``!f l. LIST_TO_SET (MAP f l) = IMAGE f (LIST_TO_SET l)``,
Induct_on `l` THEN
ASM_SIMP_TAC bool_ss [pred_setTheory.IMAGE_EMPTY, pred_setTheory.IMAGE_INSERT,
   MAP, LIST_TO_SET_THM]);

val LIST_TO_SET_FILTER = store_thm(
  "LIST_TO_SET_FILTER",
  ``LIST_TO_SET (FILTER P l) = { x | P x } INTER LIST_TO_SET l``,
  SRW_TAC [][pred_setTheory.EXTENSION, MEM_FILTER]);


(* ----------------------------------------------------------------------
    SET_TO_LIST : 'a set -> 'a list

    Only defined if the set is finite; order of elements in list is
    unspecified.
   ---------------------------------------------------------------------- *)

val _ = Defn.def_suffix := "";
val SET_TO_LIST_defn = Defn.Hol_defn "SET_TO_LIST"
  `SET_TO_LIST s =
     if FINITE s then
        if s={} then []
        else CHOICE s :: SET_TO_LIST (REST s)
     else ARB`;

(*---------------------------------------------------------------------------
       Termination of SET_TO_LIST.
 ---------------------------------------------------------------------------*)

val (SET_TO_LIST_EQN, SET_TO_LIST_IND) =
 Defn.tprove (SET_TO_LIST_defn,
   TotalDefn.WF_REL_TAC `measure CARD` THEN
   PROVE_TAC [CARD_PSUBSET, REST_PSUBSET]);

(*---------------------------------------------------------------------------
      Desired recursion equation.

      FINITE s |- SET_TO_LIST s = if s = {} then []
                               else CHOICE s::SET_TO_LIST (REST s)

 ---------------------------------------------------------------------------*)

val SET_TO_LIST_THM = save_thm("SET_TO_LIST_THM",
 DISCH_ALL (ASM_REWRITE_RULE [ASSUME ``FINITE s``] SET_TO_LIST_EQN));

val SET_TO_LIST_IND = save_thm("SET_TO_LIST_IND",SET_TO_LIST_IND);



(*---------------------------------------------------------------------------
            Some consequences
 ---------------------------------------------------------------------------*)

val SET_TO_LIST_EMPTY = store_thm(
  "SET_TO_LIST_EMPTY",
  ``SET_TO_LIST {} = []``,
  SRW_TAC [][SET_TO_LIST_THM])
val _ = export_rewrites ["SET_TO_LIST_EMPTY"]

val SET_TO_LIST_INV = Q.store_thm("SET_TO_LIST_INV",
`!s. FINITE s ==> (LIST_TO_SET(SET_TO_LIST s) = s)`,
 Induction.recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [LIST_TO_SET_THM]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, CHOICE_INSERT_REST]);

val SET_TO_LIST_CARD = Q.store_thm("SET_TO_LIST_CARD",
`!s. FINITE s ==> (LENGTH (SET_TO_LIST s) = CARD s)`,
 Induction.recInduct SET_TO_LIST_IND
   THEN REPEAT STRIP_TAC
   THEN SRW_TAC [][Once (UNDISCH SET_TO_LIST_THM)]
   THEN `FINITE (REST s)` by METIS_TAC [REST_DEF,FINITE_DELETE]
   THEN `~(CARD s = 0)` by METIS_TAC [CARD_EQ_0]
   THEN SRW_TAC [numSimps.ARITH_ss][REST_DEF, CHOICE_DEF]);

val SET_TO_LIST_IN_MEM = Q.store_thm("SET_TO_LIST_IN_MEM",
`!s. FINITE s ==> !x. x IN s = MEM x (SET_TO_LIST s)`,
 Induction.recInduct SET_TO_LIST_IND
   THEN RW_TAC bool_ss []
   THEN ONCE_REWRITE_TAC [UNDISCH SET_TO_LIST_THM]
   THEN RW_TAC bool_ss [MEM,NOT_IN_EMPTY]
   THEN PROVE_TAC [REST_DEF, FINITE_DELETE, IN_INSERT, CHOICE_INSERT_REST]);

(* this version of the above is a more likely rewrite: a complicated LHS
   turns into a simple RHS *)
val MEM_SET_TO_LIST = Q.store_thm("MEM_SET_TO_LIST",
`!s. FINITE s ==> !x. MEM x (SET_TO_LIST s) = x IN s`,
 METIS_TAC [SET_TO_LIST_IN_MEM]);
val _ = export_rewrites ["MEM_SET_TO_LIST"];

val SET_TO_LIST_SING = store_thm(
  "SET_TO_LIST_SING",
  ``SET_TO_LIST {x} = [x]``,
  SRW_TAC [][SET_TO_LIST_THM]);
val _ = export_rewrites ["SET_TO_LIST_SING"]

val ALL_DISTINCT_SET_TO_LIST = store_thm("ALL_DISTINCT_SET_TO_LIST",
  ``!s. FINITE s ==> ALL_DISTINCT (SET_TO_LIST s)``,
  Induction.recInduct SET_TO_LIST_IND THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SET_TO_LIST_THM THEN
  `FINITE (REST s)` by PROVE_TAC[pred_setTheory.FINITE_DELETE,
				 pred_setTheory.REST_DEF] THEN
  Cases_on `s = EMPTY` THEN
  FULL_SIMP_TAC bool_ss [ALL_DISTINCT, MEM_SET_TO_LIST,
			 pred_setTheory.CHOICE_NOT_IN_REST]);
val _ = export_rewrites ["ALL_DISTINCT_SET_TO_LIST"];

val ITSET_eq_FOLDL_SET_TO_LIST = Q.store_thm(
"ITSET_eq_FOLDL_SET_TO_LIST",
`!s. FINITE s ==> !f a. ITSET f s a = FOLDL (combin$C f) a (SET_TO_LIST s)`,
HO_MATCH_MP_TAC pred_setTheory.FINITE_COMPLETE_INDUCTION THEN
SRW_TAC [][pred_setTheory.ITSET_THM,SET_TO_LIST_THM,FOLDL]);


(* ----------------------------------------------------------------------
    isPREFIX
   ---------------------------------------------------------------------- *)

val isPREFIX = Define`
  (isPREFIX [] l = T) /\
  (isPREFIX (h::t) l = case l of [] => F
                               | h'::t' => (h = h') /\ isPREFIX t t')
`;
val _ = export_rewrites ["isPREFIX"]

val _ = set_fixity "<<=" (Infix(NONASSOC, 450));
val _ = overload_on ("<<=", ``isPREFIX``)
val _ = Unicode.unicode_version {u = UTF8.chr 0x227C, tmnm = "<<="}
        (* in tex input mode in emacs, produce U+227C with \preceq *)
        (* tempting to add a not-isprefix macro keyed to U+22E0 \npreceq, but
           hard to know what the ASCII version should be.  *)
val _ = TexTokenMap.TeX_notation {hol = "<<=",
                                  TeX = ("\\HOLTokenIsPrefix{}", 1)}
val _ = TexTokenMap.TeX_notation {hol = UTF8.chr 0x227C,
                                  TeX = ("\\HOLTokenIsPrefix{}", 1)}

(* type annotations are there solely to make theorem have only one
   type variable; without them the theorem ends up with three (because the
   three clauses are independent). *)
val isPREFIX_THM = store_thm(
  "isPREFIX_THM",
  ``(([]:'a list) <<= l = T) /\
    ((h::t:'a list) <<= [] = F) /\
    ((h1::t1:'a list) <<= h2::t2 = (h1 = h2) /\ isPREFIX t1 t2)``,
  SRW_TAC [][])
val _ = export_rewrites ["isPREFIX_THM"]

(* ----------------------------------------------------------------------
    SNOC
   ---------------------------------------------------------------------- *)

(* use new_recursive_definition to get quantification and variable names
   exactly as they were in rich_listTheory *)
val SNOC = new_recursive_definition {
  def = ``(!x:'a. SNOC x [] = [x]) /\
          (!x:'a x' l. SNOC x (CONS x' l) = CONS x' (SNOC x l))``,
  name = "SNOC",
  rec_axiom = list_Axiom
};
val _ = BasicProvers.export_rewrites ["SNOC"]

val LENGTH_SNOC = store_thm(
  "LENGTH_SNOC",
  ``!(x:'a) l. LENGTH (SNOC x l) = SUC (LENGTH l)``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH,SNOC]);
val _ = export_rewrites ["LENGTH_SNOC"]

val LAST_SNOC = store_thm(
  "LAST_SNOC",
  ``!x:'a l. LAST (SNOC x l) = x``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW_TAC bool_ss [SNOC, LAST_DEF] THEN
  POP_ASSUM MP_TAC THEN
  Q.SPEC_THEN `l`  STRUCT_CASES_TAC list_CASES THEN
  RW_TAC bool_ss [SNOC]);
val _ = export_rewrites ["LAST_SNOC"]

val FRONT_SNOC = store_thm(
  "FRONT_SNOC",
  ``!x:'a l. FRONT (SNOC x l) = l``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW_TAC bool_ss [SNOC, FRONT_DEF] THEN
  POP_ASSUM MP_TAC THEN
  Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES THEN
  RW_TAC bool_ss [SNOC]);
val _ = export_rewrites ["FRONT_SNOC"]

val SNOC_APPEND = store_thm("SNOC_APPEND",
   ``!x (l:('a) list). SNOC x l = APPEND l [x]``,
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC,APPEND]);

val LIST_TO_SET_SNOC = Q.store_thm("LIST_TO_SET_SNOC",
    `set (SNOC x ls) = x INSERT set ls`,
    Induct_on `ls` THEN SRW_TAC [][INSERT_COMM]);

val MAP_SNOC  = store_thm("MAP_SNOC",
    (--`!(f:'a->'b) x (l:'a list). MAP f(SNOC x l) = SNOC(f x)(MAP f l)`--),
     (REWRITE_TAC [SNOC_APPEND,MAP_APPEND,MAP]));

val EL_SNOC = store_thm("EL_SNOC",
    (--`!n (l:'a list). n < (LENGTH l) ==> (!x. EL n (SNOC x l) = EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[SNOC,EL,HD],
        REWRITE_TAC[SNOC,EL,TL,LESS_MONO_EQ]
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val EL_LENGTH_SNOC = store_thm("EL_LENGTH_SNOC",
    (--`!l:'a list. !x. EL (LENGTH l) (SNOC x l) = x`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EL,SNOC,HD,TL,LENGTH]);

val APPEND_SNOC = store_thm("APPEND_SNOC",
    (--`!l1 (x:'a) l2. APPEND l1 (SNOC x l2) = SNOC x (APPEND l1 l2)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,SNOC]);

val EVERY_SNOC = store_thm("EVERY_SNOC",
    (--`!P (x:'a) l. EVERY P (SNOC x l) = EVERY P l /\ P x`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,EVERY_DEF,CONJ_ASSOC]);

val EXISTS_SNOC = store_thm("EXISTS_SNOC",
    (--`!P (x:'a) l. EXISTS P (SNOC x l) = P x \/ (EXISTS P l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,EXISTS_DEF] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);

val MEM_SNOC = store_thm("MEM_SNOC",
    (--`!(y:'a) x l. MEM y (SNOC x l) = (y = x) \/ MEM y l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,MEM] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);
val _ = export_rewrites ["MEM_SNOC"]

val SNOC_11 = store_thm(
  "SNOC_11",
  ``!x y a b. (SNOC x y = SNOC a b) <=> (x = a) /\ (y = b)``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o Q.AP_TERM `LAST`) THEN SRW_TAC [][LAST_SNOC],
    POP_ASSUM (MP_TAC o Q.AP_TERM `FRONT`) THEN SRW_TAC [][FRONT_SNOC]
  ]);
val _ = export_rewrites ["SNOC_11"]

val REVERSE_SNOC_DEF = store_thm (
  "REVERSE_SNOC_DEF",
    ``(REVERSE [] = []) /\
        (!x:'a l. REVERSE (x::l) = SNOC x (REVERSE l))``,
          REWRITE_TAC [REVERSE_DEF, SNOC_APPEND]);

val REVERSE_SNOC = store_thm(
  "REVERSE_SNOC",
    ``!(x:'a) l. REVERSE (SNOC x l) = CONS x (REVERSE l)``,
      GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,REVERSE_SNOC_DEF]);

val forall_REVERSE = TAC_PROOF(([],
    (--`!P. (!l:('a)list. P(REVERSE l)) = (!l. P l)`--)),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC (--`REVERSE l:('a)list`--)))));

val f_REVERSE_lemma = TAC_PROOF (([],
    (--`!f1 f2.
    ((\x. (f1:('a)list->'b) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)`--)),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (fn x => ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN (--`x:('a)list`--) (BETA_RULE (AP_THM x (--`REVERSE (x:('a)list)`--))))))),
      ASM_REWRITE_TAC[]]);


val SNOC_Axiom_old = prove(
  --`!(e:'b) (f:'b -> ('a -> (('a)list -> 'b))).
        ?! fn1.
          (fn1[] = e) /\
          (!x l. fn1(SNOC x l) = f(fn1 l)x l)`--,

 let val  lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
         [(--`e:'b`--),(--`(\ft x l. f ft x (REVERSE l)):'b -> ('a -> (('a)list -> 'b))`--)]
        (PURE_ONCE_REWRITE_RULE
         [SYM (CONJUNCT1 REVERSE_DEF),
          PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
           (BETA_RULE (SPEC (--`\l:('a)list.fn1(CONS x l) =
                       (f:'b -> ('a -> (('a)list -> 'b)))(fn1 l)x l`--)
             (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
            list_Axiom_old))))
 in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL
    [
      EXISTS_TAC (--`(fn1:('a)list->'b) o REVERSE`--)
      THEN REWRITE_TAC[combinTheory.o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[],

      REPEAT GEN_TAC THEN POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
        REWRITE_RULE[REVERSE_REVERSE,f_REVERSE_lemma] o
        BETA_RULE o REWRITE_RULE[combinTheory.o_DEF] o
        SPECL [(--`(fn1' o REVERSE):('a)list->'b`--),(--`(fn1'' o REVERSE):('a)list->'b`--)])
     ]
  end);

val SNOC_Axiom = store_thm(
  "SNOC_Axiom",
  --`!e f. ?fn:'a list -> 'b.
       (fn [] = e) /\
       (!x l. fn (SNOC x l) = f x l (fn l))`--,
  REPEAT GEN_TAC THEN
  STRIP_ASSUME_TAC (CONV_RULE EXISTS_UNIQUE_CONV
                    (BETA_RULE
                     (Q.SPECL [`e`, `\x y z. f y z x`] SNOC_Axiom_old))) THEN
  Q.EXISTS_TAC `fn1` THEN ASM_REWRITE_TAC []);

val SNOC_INDUCT = save_thm("SNOC_INDUCT", prove_induction_thm SNOC_Axiom_old);
val SNOC_CASES =  save_thm("SNOC_CASES", hd (prove_cases_thm SNOC_INDUCT));

(*--------------------------------------------------------------*)
(* List generator                                               *)
(*  GENLIST f n = [f 0;...; f(n-1)]                             *)
(*--------------------------------------------------------------*)

val GENLIST = new_recursive_definition
      {name = "GENLIST",
       rec_axiom =  num_Axiom,
       def = --`(GENLIST (f:num->'a) 0 = []) /\
                (GENLIST f (SUC n) = SNOC (f n) (GENLIST f n))`--};

val LENGTH_GENLIST = store_thm("LENGTH_GENLIST",
    (--`!(f:num->'a) n. LENGTH(GENLIST f n) = n`--),
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[GENLIST,LENGTH,LENGTH_SNOC]);
val _ = export_rewrites ["LENGTH_GENLIST"]

val GENLIST_AUX = Define`
  (GENLIST_AUX f 0 l = l) /\
  (GENLIST_AUX f (SUC n) l = GENLIST_AUX f n ((f n)::l))`;

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val GENLIST_AUX_compute = save_thm(
  "GENLIST_AUX_compute",
  SUC_RULE GENLIST_AUX)
val _ = export_rewrites ["GENLIST_AUX_compute"]

(*---------------------------------------------------------------------------
       String padding (left and right)
 ---------------------------------------------------------------------------*)

val PAD_LEFT_def = Define`
  PAD_LEFT c n s = (GENLIST (K c) (n - LENGTH s)) ++ s`;

val PAD_RIGHT_def = Define`
  PAD_RIGHT c n s = s ++ (GENLIST (K c) (n - LENGTH s))`;

(*---------------------------------------------------------------------------
   Theorems about genlist. From Anthony Fox's theories. Added by Thomas Tuerk.
   Moved from rich_listTheory.
 ---------------------------------------------------------------------------*)

val MAP_GENLIST = store_thm("MAP_GENLIST",
  ``!f g n. MAP f (GENLIST g n) = GENLIST (f o g) n``,
  Induct_on `n`
  THEN ASM_SIMP_TAC arith_ss [GENLIST,MAP_SNOC, MAP,combinTheory.o_THM]);

val EL_GENLIST = store_thm("EL_GENLIST",
  ``!f n x. x < n ==> (EL x (GENLIST f n) = f x)``,
  Induct_on `n` THEN1 SIMP_TAC arith_ss [] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC [GENLIST] THEN
  Cases_on `x < n` THEN
  POP_ASSUM (fn th => ASSUME_TAC
           (SUBS [(GSYM o Q.SPECL [`f`,`n`]) LENGTH_GENLIST] th) THEN
            ASSUME_TAC th) THEN1 (
    ASM_SIMP_TAC bool_ss [EL_SNOC]
  ) THEN
  `x = LENGTH (GENLIST f n)` by FULL_SIMP_TAC arith_ss [LENGTH_GENLIST] THEN
  ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC] THEN
  REWRITE_TAC [LENGTH_GENLIST]);
val _ = export_rewrites ["EL_GENLIST"]

val HD_GENLIST = save_thm("HD_GENLIST",
  (SIMP_RULE arith_ss [EL] o Q.SPECL [`f`,`SUC n`,`0`]) EL_GENLIST);

val HD_GENLIST_COR = Q.store_thm("HD_GENLIST_COR",
  `!n f. 0 < n ==> (HD (GENLIST f n) = f 0)`,
  Cases THEN REWRITE_TAC [prim_recTheory.LESS_REFL, HD_GENLIST]);

val GENLIST_FUN_EQ = store_thm("GENLIST_FUN_EQ",
  ``!n f g. (GENLIST f n = GENLIST g n) = (!x. x < n ==> (f x = g x))``,
  SIMP_TAC bool_ss [LIST_EQ_REWRITE, LENGTH_GENLIST, EL_GENLIST]);

val GENLIST_APPEND = store_thm("GENLIST_APPEND",
  ``!f a b. GENLIST f (a + b) = (GENLIST f b) ++ (GENLIST (\t. f (t + b)) a)``,
  Induct_on `a` THEN
  ASM_SIMP_TAC arith_ss
    [GENLIST,APPEND_SNOC,APPEND_NIL,arithmeticTheory.ADD_CLAUSES]
);

val EVERY_GENLIST = store_thm("EVERY_GENLIST",
  ``!n. EVERY P (GENLIST f n) = (!i. i < n ==> P (f i))``,
  Induct_on `n` THEN ASM_SIMP_TAC arith_ss [GENLIST,EVERY_SNOC,EVERY_DEF]
    THEN metisLib.METIS_TAC [prim_recTheory.LESS_THM]);

val EXISTS_GENLIST = store_thm ("EXISTS_GENLIST",
  ``!n. EXISTS P (GENLIST f n) = (?i. i < n /\ P (f i))``,
  Induct_on `n` THEN RW_TAC arith_ss [GENLIST, EXISTS_SNOC, EXISTS_DEF]
    THEN metisLib.METIS_TAC [prim_recTheory.LESS_THM]);

val TL_GENLIST = Q.store_thm ("TL_GENLIST",
  `!f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_EQ
    THEN SRW_TAC [] [EL_GENLIST, LENGTH_GENLIST, LENGTH_TL]
    THEN ONCE_REWRITE_TAC [EL |> CONJUNCT2 |> GSYM]
    THEN `SUC x < SUC n` by numLib.DECIDE_TAC
    THEN IMP_RES_TAC EL_GENLIST
    THEN ASM_SIMP_TAC arith_ss []);

val ZIP_GENLIST = store_thm("ZIP_GENLIST",
  ``!l f n. (LENGTH l = n) ==>
      (ZIP (l,GENLIST f n) = GENLIST (\x. (EL x l,f x)) n)``,
  REPEAT STRIP_TAC THEN
  `LENGTH (ZIP (l,GENLIST f n)) = LENGTH (GENLIST (\x. (EL x l,f x)) n)`
    by ASM_SIMP_TAC arith_ss [LENGTH_GENLIST,LENGTH_ZIP] THEN
  ASM_SIMP_TAC arith_ss [LIST_EQ_REWRITE, LENGTH_GENLIST, LENGTH_ZIP,
                         EL_ZIP, EL_GENLIST]);

val GENLIST_CONS = store_thm(
  "GENLIST_CONS",
  ``GENLIST f (SUC n) = f 0 :: (GENLIST (f o SUC) n)``,
  Induct_on `n` THEN SRW_TAC [][GENLIST, SNOC]);

val NULL_GENLIST = Q.store_thm("NULL_GENLIST",
  `!n f. NULL (GENLIST f n) = (n = 0)`,
  Cases THEN
  REWRITE_TAC [numTheory.NOT_SUC, NULL_DEF, CONJUNCT1 GENLIST, GENLIST_CONS]);

val GENLIST_AUX_lem = Q.prove(
  `!n l1 l2. GENLIST_AUX f n l1 ++ l2 = GENLIST_AUX f n (l1 ++ l2)`,
  Induct_on `n` THEN SRW_TAC [] [GENLIST_AUX]);

val GENLIST_GENLIST_AUX = Q.store_thm("GENLIST_GENLIST_AUX",
  `!n. GENLIST f n = GENLIST_AUX f n []`,
  Induct_on `n`
  THEN RW_TAC bool_ss
         [SNOC_APPEND, APPEND, GENLIST_AUX, GENLIST_AUX_lem, GENLIST]);

val GENLIST_NUMERALS = store_thm(
  "GENLIST_NUMERALS",
  ``(GENLIST f 0 = []) /\
    (GENLIST f (NUMERAL n) = GENLIST_AUX f (NUMERAL n) [])``,
  REWRITE_TAC [GENLIST_GENLIST_AUX, GENLIST_AUX]);
val _ = export_rewrites ["GENLIST_NUMERALS"]

val MEM_GENLIST = Q.store_thm(
"MEM_GENLIST",
`MEM x (GENLIST f n) <=> ?m. m < n /\ (x = f m)`,
SRW_TAC [][MEM_EL,EL_GENLIST,EQ_IMP_THM] THEN
PROVE_TAC [EL_GENLIST] )

val ALL_DISTINCT_SNOC = store_thm (
   "ALL_DISTINCT_SNOC",
   ``!x l. ALL_DISTINCT (SNOC x l) =
             ~(MEM x l) /\ (ALL_DISTINCT l)``,
SRW_TAC [][SNOC_APPEND, ALL_DISTINCT_APPEND] THEN PROVE_TAC[]);

local open prim_recTheory in
val ALL_DISTINCT_GENLIST = Q.store_thm(
"ALL_DISTINCT_GENLIST",
`ALL_DISTINCT (GENLIST f n) <=>
 (!m1 m2. m1 < n /\ m2 < n /\ (f m1 = f m2) ==> (m1 = m2))`,
Induct_on `n` THEN
SRW_TAC [][GENLIST,ALL_DISTINCT_SNOC,MEM_EL] THEN
SRW_TAC [][EQ_IMP_THM] THEN1 (
  IMP_RES_TAC LESS_SUC_IMP THEN
  Cases_on `m1 = n` THEN Cases_on `m2 = n` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN1 (
    NTAC 2 (FIRST_X_ASSUM (Q.SPEC_THEN `m2` MP_TAC)) THEN
    SRW_TAC [][] ) THEN
  NTAC 2 (FIRST_X_ASSUM (Q.SPEC_THEN `m1` MP_TAC)) THEN
  SRW_TAC [][] ) THEN1 (
  Q.MATCH_RENAME_TAC `~(m < n) \/ f n <> EL m (GENLIST f n)` [] THEN
  Cases_on `m < n` THEN SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`m`,`n`] MP_TAC) THEN
  SRW_TAC [][LESS_SUC] THEN
  METIS_TAC [LESS_REFL] ) THEN
METIS_TAC [LESS_SUC] )
end

(* ---------------------------------------------------------------------- *)

val FOLDL_SNOC = store_thm("FOLDL_SNOC",
    (--`!(f:'b->'a->'b) e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x`--),
    let val lem = prove(
        (--`!l (f:'b->'a->'b) e x. FOLDL f e (SNOC x l) = f (FOLDL f e l) x`--),
        LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,FOLDL]
        THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[])
   in
    MATCH_ACCEPT_TAC lem
   end);

local open arithmeticTheory in
val SUM_SNOC = store_thm("SUM_SNOC",
    (--`!x l. SUM (SNOC x l) = (SUM l) + x`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUM,SNOC,ADD,ADD_0]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC]);

val SUM_APPEND = store_thm("SUM_APPEND",
    (--`!l1 l2. SUM (APPEND l1 l2) = SUM l1 + SUM l2`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,APPEND,ADD,ADD_0,ADD_ASSOC]);
end

val SUM_MAP_FOLDL = Q.store_thm(
"SUM_MAP_FOLDL",
`!ls. SUM (MAP f ls) = FOLDL (\a e. a + f e) 0 ls`,
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [][FOLDL_SNOC,MAP_SNOC,SUM_SNOC,MAP,SUM,FOLDL]);

val SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST = Q.store_thm(
"SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST",
`FINITE s ==> (SIGMA f s = SUM (MAP f (SET_TO_LIST s)))`,
SRW_TAC [][SUM_IMAGE_DEF] THEN
SRW_TAC [][ITSET_eq_FOLDL_SET_TO_LIST,SUM_MAP_FOLDL] THEN
AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
SRW_TAC [][FUN_EQ_THM,arithmeticTheory.ADD_COMM]);

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

local open arithmeticTheory prim_recTheory in
val EL_REVERSE = store_thm("EL_REVERSE",
    (--`!n (l:'a list). n < (LENGTH l) ==>
     (EL n (REVERSE l) = EL (PRE(LENGTH l - n)) l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,
        EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ,SUB_0] THENL[
        REWRITE_TAC[REVERSE_SNOC,PRE,EL_LENGTH_SNOC,HD],
        REWRITE_TAC[REVERSE_SNOC,SUB_MONO_EQ,TL]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
        THEN MATCH_MP_TAC (GSYM EL_SNOC)
        THEN REWRITE_TAC(PRE_SUB1 :: (map GSYM [SUB_PLUS,ADD1]))
        THEN numLib.DECIDE_TAC]);
end

val REVERSE_GENLIST = Q.store_thm("REVERSE_GENLIST",
`REVERSE (GENLIST f n) = GENLIST (\m. f (PRE n - m)) n`,
  MATCH_MP_TAC LIST_EQ THEN
  SRW_TAC [][EL_REVERSE] THEN
  `PRE (n - x) < n` by numLib.DECIDE_TAC THEN
  SRW_TAC [][EL_GENLIST] THEN
  AP_TERM_TAC THEN numLib.DECIDE_TAC)

val FOLDL_UNION_BIGUNION = store_thm(
"FOLDL_UNION_BIGUNION",
``!f ls s. FOLDL (\s x. s UNION f x) s ls = s UNION BIGUNION (IMAGE f (set ls))``,
GEN_TAC THEN Induct THEN SRW_TAC[][FOLDL,UNION_ASSOC])

val FOLDL_UNION_BIGUNION_paired = store_thm(
"FOLDL_UNION_BIGUNION_paired",
``!f ls s. FOLDL (\s (x,y). s UNION f x y) s ls = s UNION BIGUNION (IMAGE (UNCURRY f) (set ls))``,
GEN_TAC THEN Induct THEN1 SRW_TAC[][FOLDL] THEN
Cases THEN SRW_TAC[][FOLDL,UNION_ASSOC,GSYM pairTheory.LAMBDA_PROD])

val FOLDL_ZIP_SAME = store_thm(
"FOLDL_ZIP_SAME",
``!ls f e. FOLDL f e (ZIP (ls,ls)) = FOLDL (\x y. f x (y,y)) e ls``,
Induct THEN SRW_TAC[][FOLDL,ZIP])
val _ = export_rewrites["FOLDL_ZIP_SAME"]

val MAP_ZIP_SAME = store_thm(
"MAP_ZIP_SAME",
``!ls f. MAP f (ZIP (ls,ls)) = MAP (\x. f (x,x)) ls``,
Induct THEN SRW_TAC[][MAP,ZIP])
val _ = export_rewrites["MAP_ZIP_SAME"]

(* ----------------------------------------------------------------------
    All lists have infinite universes
   ---------------------------------------------------------------------- *)

val INFINITE_LIST_UNIV = store_thm(
  "INFINITE_LIST_UNIV",
  ``INFINITE univ(:'a list)``,
  REWRITE_TAC [GSYM INFINITE_DEF] THEN
  SRW_TAC [][INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\l. x::l` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `[]` THEN SRW_TAC [][])
val _ = export_rewrites ["INFINITE_LIST_UNIV"]


(*---------------------------------------------------------------------------*)
(* Tail recursive versions for better memory usage when applied in ML        *)
(*---------------------------------------------------------------------------*)

val _ = Defn.def_suffix := "_DEF";

(* EVAL performance of LEN seems to be worse than of LENGTH *)

val LEN_DEF = Define
  `(LEN [] n = n) /\
   (LEN (h::t) n = LEN t (n+1))`;

val REV_DEF = Define
  `(REV [] acc = acc) /\
   (REV (h::t) acc = REV t (h::acc))`;

val LEN_LENGTH_LEM = Q.store_thm
("LEN_LENGTH_LEM",
 `!L n. LEN L n = LENGTH L + n`,
 Induct THEN RW_TAC arith_ss [LEN_DEF,LENGTH]);

val REV_REVERSE_LEM = Q.store_thm
("REV_REVERSE_LEM",
 `!L1 L2. REV L1 L2 = (REVERSE L1) ++ L2`,
 Induct THEN RW_TAC arith_ss [REV_DEF,REVERSE_DEF,APPEND]
        THEN REWRITE_TAC [GSYM APPEND_ASSOC]
        THEN RW_TAC bool_ss [APPEND]);

val LENGTH_LEN = Q.store_thm
("LENGTH_LEN",
 `!L. LENGTH L = LEN L 0`,
 RW_TAC arith_ss [LEN_LENGTH_LEM]);

val REVERSE_REV = Q.store_thm
("REVERSE_REV",
 `!L. REVERSE L = REV L []`,
 PROVE_TAC [REV_REVERSE_LEM,APPEND_NIL]);

val SUM_ACC_DEF = Define
  `(SUM_ACC [] acc = acc) /\
   (SUM_ACC (h::t) acc = SUM_ACC t (h+acc))`

val SUM_ACC_SUM_LEM = store_thm
("SUM_ACC_SUM_LEM",
 ``!L n. SUM_ACC L n = SUM L + n``,
 Induct THEN RW_TAC arith_ss [SUM_ACC_DEF,SUM]);

val SUM_SUM_ACC = store_thm
("SUM_SUM_ACC",
  ``!L. SUM L = SUM_ACC L 0``,
  PROVE_TAC [SUM_ACC_SUM_LEM,arithmeticTheory.ADD_0])

(* ----------------------------------------------------------------------
    List "splitting" results
   ---------------------------------------------------------------------- *)

(* These loop! Use with care *)
val EXISTS_LIST = store_thm(
  "EXISTS_LIST",
  ``(?l. P l) <=> P [] \/ ?h t. P (h::t)``,
  METIS_TAC [list_CASES]);

val FORALL_LIST = store_thm(
  "FORALL_LIST",
  ``(!l. P l) <=> P [] /\ !h t. P (h::t)``,
  METIS_TAC [list_CASES]);

(* now on with the show *)
val MEM_SPLIT_APPEND_first = store_thm(
  "MEM_SPLIT_APPEND_first",
  ``MEM e l <=> ?pfx sfx. (l = pfx ++ [e] ++ sfx) /\ ~MEM e pfx``,
  Induct_on `l` THEN SRW_TAC [][] THEN Cases_on `e = a` THEN
  SRW_TAC [][] THENL[
    MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN SRW_TAC [][],
    SRW_TAC [][SimpRHS, Once EXISTS_LIST]
  ]);

val MEM_SPLIT_APPEND_last = store_thm(
  "MEM_SPLIT_APPEND_last",
  ``MEM e l <=> ?pfx sfx. (l = pfx ++ [e] ++ sfx) /\ ~MEM e sfx``,
  Q.ID_SPEC_TAC `l` THEN SNOC_INDUCT_TAC THEN SRW_TAC [][] THEN
  Cases_on `e = x` THEN SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`l`, `[]`] THEN SRW_TAC [][SNOC_APPEND],
    SRW_TAC [][EQ_IMP_THM] THENL [
      MAP_EVERY Q.EXISTS_TAC [`pfx`, `SNOC x sfx`] THEN
      SRW_TAC [][APPEND_ASSOC, APPEND_SNOC],
      Q.SPEC_THEN `sfx` STRIP_ASSUME_TAC SNOC_CASES THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
        FULL_SIMP_TAC (srw_ss()) [GSYM SNOC_APPEND] THEN
      FULL_SIMP_TAC (srw_ss()) [APPEND_SNOC] THEN SRW_TAC [][] THEN
      METIS_TAC []
    ]
  ]);

val APPEND_EQ_APPEND = store_thm(
  "APPEND_EQ_APPEND",
  ``(l1 ++ l2 = m1 ++ m2) <=>
      (?l. (l1 = m1 ++ l) /\ (m2 = l ++ l2)) \/
      (?l. (m1 = l1 ++ l) /\ (l2 = l ++ m2))``,
  MAP_EVERY Q.ID_SPEC_TAC [`m2`, `m1`, `l2`, `l1`] THEN Induct_on `l1` THEN
  SRW_TAC [][] THEN
  Cases_on `m1` THEN SRW_TAC [][] THEN METIS_TAC []);

val APPEND_EQ_CONS = store_thm(
  "APPEND_EQ_CONS",
  ``(l1 ++ l2 = h::t) <=>
       ((l1 = []) /\ (l2 = h::t)) \/
       ?lt. (l1 = h::lt) /\ (t = lt ++ l2)``,
  MAP_EVERY Q.ID_SPEC_TAC [`t`, `h`, `l2`, `l1`] THEN Induct_on `l1` THEN
  SRW_TAC [][] THEN METIS_TAC []);

(* could just use APPEND_EQ_APPEND and APPEND_EQ_SING, but this gives you
   four possibilities
      |- (x ++ [e] ++ y = a ++ b) ⇔
           (∃l'. (x = a ++ l') ∧ (b = l' ++ [e] ++ y)) ∨
           (a = x ++ [e]) ∧ (b = y) ∨
           (a = x) ∧ (b = e::y) ∨
           ∃l. (a = x ++ [e] ++ l) ∧ (y = l ++ b)
   Note that the middle two are instances of the outer two with the
   existentially quantified l set to []
*)
val APPEND_EQ_APPEND_MID = store_thm(
  "APPEND_EQ_APPEND_MID",
  ``(l1 ++ [e] ++ l2 = m1 ++ m2) <=>
       (?l. (m1 = l1 ++ [e] ++ l) /\ (l2 = l ++ m2)) \/
       (?l. (l1 = m1 ++ l) /\ (m2 = l ++ [e] ++ l2))``,
  MAP_EVERY Q.ID_SPEC_TAC [`m2`, `m1`, `l2`, `e`, `l1`] THEN Induct THEN
  Cases_on `m1` THEN SRW_TAC [][] THEN METIS_TAC []);

(* --------------------------------------------------------------------- *)

local
   val lupdate_exists = prove(
     ``?lupdate.
         (!e: 'a n: num. lupdate e n ([]: 'a list) = []: 'a list) /\
         (!e x l. lupdate e 0 (x::l) = e::l) /\
         (!e n x l. lupdate e (SUC n) (x::l) =
                       CONS x (lupdate e n l))``,
     REPEAT STRIP_TAC
     THEN STRIP_ASSUME_TAC
          (Q.ISPECL
             [`(\x1 x2. []): 'a -> num -> 'a list`,
              `\(x: 'a) (l: 'a list) (r: 'a -> num -> 'a list) (e: 'a)
                (n: num).
                  if n = 0 then
                     e::l
                  else
                     (CONS x (r e (PRE n)):'a list)`] list_Axiom)
     THEN Q.EXISTS_TAC `\x1 x2 x3. fn x3 x1 x2`
     THEN ASM_SIMP_TAC arith_ss [])
in
   val LUPDATE_def =
      Definition.new_specification
         ("LUPDATE_def", ["LUPDATE"], lupdate_exists)
end;

val LUPDATE_SEM = store_thm ("LUPDATE_SEM",
  ``(!e:'a n l. LENGTH (LUPDATE e n l) = LENGTH l) /\
    (!e:'a n l p.
       p < LENGTH l ==>
       (EL p (LUPDATE e n l) = if p = n then e else EL p l))``,
  CONJ_TAC
  THEN Induct_on `n`
  THEN Cases_on `l`
  THEN ASM_SIMP_TAC arith_ss [LUPDATE_def, LENGTH]
  THEN Cases_on `p`
  THEN ASM_SIMP_TAC arith_ss [EL, HD, TL]);

val EL_LUPDATE = store_thm("EL_LUPDATE",
  ``!ys (x:'a) i k.
      EL i (LUPDATE x k ys) =
      if (i = k) /\ k < LENGTH ys then x else EL i ys``,
  Induct_on `ys` THEN Cases_on `k` THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC arith_ss [LUPDATE_def,LENGTH]
  THEN Cases_on `i`
  THEN FULL_SIMP_TAC arith_ss [LUPDATE_def,LENGTH,EL,HD,TL]);

val LENGTH_LUPDATE = store_thm("LENGTH_LUPDATE",
  ``!(x:'a) n ys. LENGTH (LUPDATE x n ys) = LENGTH ys``,
  SIMP_TAC bool_ss [LUPDATE_SEM]);
val _ = export_rewrites ["LENGTH_LUPDATE"]

val LUPDATE_LENGTH = store_thm("LUPDATE_LENGTH",
  ``!xs x (y:'a) ys. LUPDATE x (LENGTH xs) (xs ++ y::ys) = xs ++ x::ys``,
  Induct THEN FULL_SIMP_TAC bool_ss [LENGTH,APPEND,LUPDATE_def,
    NOT_SUC,PRE,INV_SUC_EQ]);

val LUPDATE_SNOC = store_thm("LUPDATE_SNOC",
  ``!ys k x (y:'a).
      LUPDATE x k (SNOC y ys) =
      if k = LENGTH ys then SNOC x ys else SNOC y (LUPDATE x k ys)``,
  Induct THEN Cases_on `k` THEN Cases_on `n = LENGTH ys`
  THEN FULL_SIMP_TAC bool_ss [SNOC,LUPDATE_def,LENGTH,NOT_SUC,
         PRE,INV_SUC_EQ]);

val MEM_LUPDATE_E = store_thm("MEM_LUPDATE_E",
  ``!l x y i. MEM x (LUPDATE y i l) ==> (x = y) \/ MEM x l``,
  Induct THEN SRW_TAC[][LUPDATE_def] THEN
  Cases_on`i`THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def] THEN
  PROVE_TAC[])

val MEM_LUPDATE = store_thm(
  "MEM_LUPDATE",
  ``!l x y i. MEM x (LUPDATE y i l) <=>
                i < LENGTH l /\ (x = y) \/
                ?j. j < LENGTH l /\ i <> j /\ (EL j l = x)``,
  Induct THEN SRW_TAC [][LUPDATE_def] THEN
  Cases_on `i` THEN SRW_TAC [][LUPDATE_def] THENL [
    SRW_TAC [][Once arithmeticTheory.EXISTS_NUM] THEN
    METIS_TAC [MEM_EL],
    EQ_TAC THEN SRW_TAC [][] THENL [
      DISJ2_TAC THEN Q.EXISTS_TAC `0` THEN SRW_TAC [][],
      DISJ2_TAC THEN Q.EXISTS_TAC `SUC j` THEN SRW_TAC [][],
      Cases_on `j` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC[]
    ]
  ]);

val LUPDATE_compute = save_thm("LUPDATE_compute",
   numLib.SUC_RULE LUPDATE_def)

val EVERYi_def = Define`
  (EVERYi P [] = T) /\
  (EVERYi P (h::t) = P 0 h /\ EVERYi (P o SUC) t)
`

val splitAtPki_def = Define`
  (splitAtPki P k [] = k [] []) /\
  (splitAtPki P k (h::t) =
     if P 0 h then k [] (h::t)
     else splitAtPki (P o SUC) (\p s. k (h::p) s) t)
`

val splitAtPki_APPEND = store_thm(
  "splitAtPki_APPEND",
  ``!l1 l2 P k.
      EVERYi (\i. $~ o P i) l1 /\ (0 < LENGTH l2 ==> P (LENGTH l1) (HD l2)) ==>
      (splitAtPki P k (l1 ++ l2) = k l1 l2)``,
  Induct THEN SRW_TAC[][EVERYi_def, splitAtPki_def] THEN1
    (Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss())[splitAtPki_def]) THEN
  FULL_SIMP_TAC (srw_ss()) [combinTheory.o_DEF]);

val splitAtPki_EQN = store_thm(
  "splitAtPki_EQN",
  ``splitAtPki P k l =
      case OLEAST i. i < LENGTH l /\ P i (EL i l) of
          NONE => k l []
        | SOME i => k (TAKE i l) (DROP i l)``,
  MAP_EVERY Q.ID_SPEC_TAC [`P`, `k`, `l`] THEN Induct THEN
  ASM_SIMP_TAC (srw_ss()) [splitAtPki_def] THEN POP_ASSUM (K ALL_TAC) THEN
  MAP_EVERY Q.X_GEN_TAC [`h`, `k`, `P`] THEN Cases_on `P 0 h` THEN1
    (ASM_SIMP_TAC (srw_ss()) [] THEN
     `(OLEAST i. i < SUC (LENGTH l) /\ P i (EL i (h::l))) = SOME 0`
        suffices_by SRW_TAC [][] THEN
     DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN SRW_TAC [][] THEN1
       (Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
     `~(0 < n)` suffices_by numLib.ARITH_TAC THEN STRIP_TAC THEN RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][] THEN
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  CONJ_TAC THENL [
    STRIP_TAC THEN
    `(OLEAST i. i < SUC (LENGTH l) /\ P i (EL i (h::l))) = NONE`
      suffices_by SRW_TAC [][] THEN
    DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN CONJ_TAC
      THEN1 SRW_TAC [][] THEN
    Cases THEN SRW_TAC [][],

    Q.X_GEN_TAC `i` THEN STRIP_TAC THEN
    `(OLEAST i. i < SUC (LENGTH l) /\ P i (EL i (h::l))) = SOME (SUC i)`
      suffices_by SRW_TAC [][] THEN
    DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN CONJ_TAC THEN1
      (DISCH_THEN (Q.SPEC_THEN `SUC i` MP_TAC) THEN SRW_TAC [][]) THEN
    Q.X_GEN_TAC `j` THEN SRW_TAC [][] THEN
    `~(j < SUC i) /\ ~(SUC i < j)` suffices_by numLib.ARITH_TAC THEN
    REPEAT STRIP_TAC THENL [
      Cases_on `j` THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
      POP_ASSUM
        (fn si_lt_j => FIRST_X_ASSUM (MP_TAC o C MATCH_MP si_lt_j)) THEN
      SRW_TAC [][]
    ]
  ]);

val TAKE_LENGTH_TOO_LONG = store_thm(
  "TAKE_LENGTH_TOO_LONG",
  ``!l n. LENGTH l <= n ==> (TAKE n l = l)``,
  Induct THEN SRW_TAC [numSimps.ARITH_ss][]);

val DROP_LENGTH_TOO_LONG = store_thm(
  "DROP_LENGTH_TOO_LONG",
  ``!l n. LENGTH l <= n ==> (DROP n l = [])``,
  Induct THEN SRW_TAC [numSimps.ARITH_ss][]);

val TAKE_splitAtPki = store_thm(
  "TAKE_splitAtPki",
  ``TAKE n l = splitAtPki (K o (=) n) K l``,
  SRW_TAC [][splitAtPki_EQN] THEN
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN
  SRW_TAC[numSimps.ARITH_ss][TAKE_LENGTH_TOO_LONG])

val DROP_splitAtPki = store_thm(
  "DROP_splitAtPki",
  ``DROP n l = splitAtPki (K o (=) n) (K I) l``,
  SRW_TAC [][splitAtPki_EQN] THEN
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO THEN
  SRW_TAC[numSimps.ARITH_ss][DROP_LENGTH_TOO_LONG]);


(* --------------------------------------------------------------------- *)

val LAST_compute = Q.store_thm("LAST_compute",
   `(!x. LAST [x] = x) /\
    (!h1 h2 t. LAST (h1::h2::t) = LAST (h2::t))`,
   SRW_TAC [] [LAST_DEF]);

val TAKE_compute = Q.prove(
   `(!l. TAKE 0 l = []) /\
    (!n. TAKE (SUC n) [] = []) /\
    (!n h t. TAKE (SUC n) (h::t) = h :: TAKE n t)`,
   SRW_TAC [] []);

val DROP_compute = Q.prove(
   `(!l. DROP 0 l = l) /\
    (!n. DROP (SUC n) [] = []) /\
    (!n h t. DROP (SUC n) (h::t) = DROP n t)`,
   SRW_TAC [] []);

val TAKE_compute =
   Theory.save_thm("TAKE_compute", numLib.SUC_RULE TAKE_compute);

val DROP_compute =
   Theory.save_thm("DROP_compute", numLib.SUC_RULE DROP_compute);

val _ = app DefnBase.export_cong ["EXISTS_CONG", "EVERY_CONG", "MAP_CONG",
                                  "MAP2_CONG", "EVERY2_cong", "FOLDL2_cong",
                                  "FOLDL_CONG", "FOLDR_CONG", "list_size_cong"]

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
   fun NL() = PP.add_newline ppstrm
 in
   S "val _ = let open computeLib";
   S "        in add_funs [APPEND,APPEND_NIL, FLAT, HD, TL,";
   S "             LENGTH, MAP, MAP2, NULL_DEF, MEM, EXISTS_DEF, DROP_compute,";
   S "             EVERY_DEF, ZIP, UNZIP, FILTER, FOLDL, FOLDR, TAKE_compute,";
   S "             FOLDL, REVERSE_REV, SUM_SUM_ACC, ALL_DISTINCT, GENLIST_AUX,";
   S "             EL_restricted, EL_simp_restricted, SNOC, LUPDATE_compute,";
   S "             GENLIST_NUMERALS, computeLib.lazyfy_thm list_case_compute,";
   S "             list_size_def, FRONT_DEF, LAST_compute, isPREFIX]";
   S "        end;";
   NL(); NL();
   S "val _ =";
   S "  let val list_info = Option.valOf (TypeBase.read {Thy = \"list\",Tyop=\"list\"})";
   S "      val lift_list = mk_var(\"listSyntax.lift_list\",Parse.Type`:'type -> ('a -> 'term) -> 'a list -> 'term`)";
   S "      val list_info' = TypeBasePure.put_lift lift_list list_info";
   S "  in TypeBase.write [list_info']";
   S "  end;"
 end)};

val _ = export_rewrites
          ["APPEND_11", "FLAT",
           "MAP", "MAP2", "NULL_DEF",
           "SUM", "APPEND_ASSOC", "CONS", "CONS_11",
           "LENGTH_MAP", "MAP_APPEND",
           "NOT_CONS_NIL", "NOT_NIL_CONS", "MAP_EQ_NIL",
           "CONS_ACYCLIC", "list_case_def",
           "ZIP", "UNZIP", "ZIP_UNZIP", "UNZIP_ZIP",
           "LENGTH_ZIP", "LENGTH_UNZIP",
           "EVERY_APPEND", "EXISTS_APPEND", "EVERY_SIMP",
           "EXISTS_SIMP", "NOT_EVERY", "NOT_EXISTS",
           "FOLDL", "FOLDR", "LENGTH_LUPDATE",
           "LUPDATE_LENGTH"];

val nil_tm = Term.prim_mk_const{Name="NIL",Thy="list"};
val cons_tm = Term.prim_mk_const{Name="CONS",Thy="list"};

fun dest_cons M =
  case strip_comb M
   of (c,[p,q]) => if Term.same_const c cons_tm then (p,q)
                   else raise ERR "listScript" "dest_cons"
    | otherwise => raise ERR "listScript" "dest_cons" ;

fun dest_list M =
   case total dest_cons M
    of NONE => if same_const nil_tm M then []
               else raise ERR "dest_list" "not terminated with nil"
     | SOME(h,t) => h::dest_list t

val _ = export_theory();
