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


structure listScript =
struct

(*---------------------------------------------------------------------------*
 * Require ancestor theory structures to be present. The parents of list     *
 * are "arithmetic" and "pair".                                              *
 *---------------------------------------------------------------------------*)

local open arithmeticTheory pairTheory in end;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib Num_conv Prim_rec BasicProvers mesonLib
     simpLib boolSimps pairTheory TotalDefn SingleStep metisLib;;

val arith_ss = bool_ss ++ numSimps.ARITH_ss ++ numSimps.REDUCE_ss

val _ = new_theory "list";

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val NOT_SUC      = numTheory.NOT_SUC
and INV_SUC      = numTheory.INV_SUC
fun INDUCT_TAC g = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g;

val LESS_0       = prim_recTheory.LESS_0;
val NOT_LESS_0   = prim_recTheory.NOT_LESS_0;
val PRE          = prim_recTheory.PRE;
val LESS_MONO    = prim_recTheory.LESS_MONO;
val INV_SUC_EQ   = prim_recTheory.INV_SUC_EQ;
val PRIM_REC_THM = prim_recTheory.PRIM_REC_THM;
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

(*---------------------------------------------------------------------------*)
(* Fiddle with concrete syntax                                               *)
(*---------------------------------------------------------------------------*)

val _ = set_MLname "CONS" "CONS_def";

val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "["], rightdelim = [TOK "]"],
                      cons = "CONS", nilstr = "NIL",
                      block_info = (PP.INCONSISTENT, 0)};

val _ = add_rule {term_name = "CONS", fixity = Infixr 450,
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

val TL = new_recursive_definition
      {name = "TL",
       rec_axiom = list_Axiom,
       def = --`TL (h::t) = t`--};

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

val _ = set_fixity "++" (Infixl 440);
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

val MAP = new_recursive_definition
      {name = "MAP",
       rec_axiom = list_Axiom,
       def = --`(!f:'a->'b. MAP f [] = []) /\
                   (!f h t. MAP f (h::t) = f h::MAP f t)`--};

val MEM = new_recursive_definition
      {name = "MEM",
       rec_axiom = list_Axiom,
       def = --`(!x. MEM x [] = F) /\
            (!x h t. MEM x (h::t) = (x=h) \/ MEM x t)`--};
val _ = export_rewrites ["MEM"]

val FILTER = new_recursive_definition
      {name = "FILTER",
       rec_axiom = list_Axiom,
       def = --`(!P. FILTER P [] = []) /\
             (!(P:'a->bool) h t.
                    FILTER P (h::t) =
                         if P h then (h::FILTER P t) else FILTER P t)`--};

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

val MAP2 =
  let val lemma = prove
     (--`?fn.
         (!f:'a -> 'b -> 'c. fn f [] [] = []) /\
         (!f h1 t1 h2 t2.
           fn f (h1::t1) (h2::t2) = f h1 h2::fn f t1 t2)`--,
      let val th = prove_rec_fn_exists list_Axiom
           (--`(fn (f:'a -> 'b -> 'c) [] l = []) /\
               (fn f (h::t) l = CONS (f h (HD l)) (fn f t (TL l)))`--)
      in
      STRIP_ASSUME_TAC th THEN
      EXISTS_TAC (--`fn:('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list`--)
      THEN ASM_REWRITE_TAC [HD,TL]
      end)
  in
      Rsyntax.new_specification{
        name = "MAP2", sat_thm = lemma,
        consts = [{const_name="MAP2", fixity=Prefix}]
      }
  end

val MAP2_FAIL = Q.prove
(`(!f h t.
   (MAP2 (f:'a->'b->'c) [] (h::t) =
    FAIL MAP2 ^(mk_var("unequal length lists",bool)) f [] (h::t))) /\
  !f h t.
    (MAP2 (f:'a->'b->'c) (h::t) [] =
     FAIL MAP2 ^(mk_var("unequal length lists",bool)) f (h::t) [])`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

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
 --`!(l:'a list). list_case (b:'b) f l =
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


val APPEND_ASSOC = store_thm ("APPEND_ASSOC",
 --`!(l1:'a list) l2 l3.
     APPEND l1 (APPEND l2 l3) = (APPEND (APPEND l1 l2) l3)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);

val LENGTH_APPEND = store_thm ("LENGTH_APPEND",
 --`!(l1:'a list) (l2:'a list).
     LENGTH (APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, APPEND, ADD_CLAUSES]);

val MAP_APPEND = store_thm ("MAP_APPEND",
 --`!(f:'a->'b).!l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`--,
    STRIP_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, APPEND]);

val LENGTH_MAP = store_thm ("LENGTH_MAP",
 --`!l. !(f:'a->'b). LENGTH (MAP f l) = LENGTH l`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH]);

val MAP_EQ_NIL = store_thm(
  "MAP_EQ_NIL",
  --`!(l:'a list) (f:'a->'b).
         ((MAP f l = []) = (l = [])) /\
         (([] = MAP f l) = (l = []))`--,
  LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, NOT_CONS_NIL, NOT_NIL_CONS]);

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
 --`!l. EVERY (\(x:'a). (P x) /\ (Q x)) l = (EVERY P l /\ EVERY Q l)`--,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

val EVERY_MEM = store_thm(
  "EVERY_MEM",
  ``!P l:'a list. EVERY P l = !e. MEM e l ==> P e``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EVERY_DEF, MEM] THEN
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

val EXISTS_MEM = store_thm(
  "EXISTS_MEM",
  ``!P l:'a list. EXISTS P l = ?e. MEM e l /\ P e``,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EXISTS_DEF, MEM] THEN
  mesonLib.MESON_TAC []);

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
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND, MEM, DISJ_ASSOC]);
val _ = export_rewrites ["MEM_APPEND"]

val MEM_FILTER = Q.store_thm
("MEM_FILTER",
 `!P L x. MEM x (FILTER P L) = P x /\ MEM x L`,
 GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
   THEN RW_TAC bool_ss [MEM,FILTER]
   THEN PROVE_TAC [MEM]);

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
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, MEM] THEN
  mesonLib.ASM_MESON_TAC []);

val LENGTH_NIL = store_thm("LENGTH_NIL",
 --`!l:'a list. (LENGTH l = 0) = (l = [])`--,
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL]);

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
val _ = export_rewrites ["EL_simp"]



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
        {consts = [{const_name = "ZIP", fixity = Prefix}],
         name = "ZIP",
         sat_thm = lemma
        }
    end;

val ZIP_FAIL = Q.prove
(`(!(h:'b) t. ZIP ([]:'a list,h::t) =
         FAIL ZIP ^(mk_var("unequal length lists",bool)) ([],h::t)) /\
  (!(h:'a) t. ZIP (h::t,[]:'b list) =
              FAIL ZIP ^(mk_var("unequal length lists",bool)) (h::t,[]))`,
 REWRITE_TAC [combinTheory.FAIL_THM]);


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

val MEM_REVERSE = store_thm(
  "MEM_REVERSE",
  ``!l x. MEM x (REVERSE l) = MEM x l``,
  Induct THEN SRW_TAC [][] THEN PROVE_TAC []);

val _ = export_rewrites ["MEM_REVERSE"]


(* ----------------------------------------------------------------------
    FRONT and LAST
   ---------------------------------------------------------------------- *)

val LAST_DEF = new_recursive_definition {
  name = "LAST_DEF",
  rec_axiom = list_Axiom,
  def = ``LAST (h::t) = if t = [] then h else LAST t``};

val LAST_NIL = Q.prove
(`LAST [] = FAIL LAST ^(mk_var("empty list",bool))  []`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val FRONT_DEF = new_recursive_definition {
  name = "FRONT_DEF",
  rec_axiom = list_Axiom,
  def = ``FRONT (h::t) = if t = [] then [] else h :: FRONT t``};

val FRONT_NIL = Q.prove
(`FRONT [] = FAIL FRONT ^(mk_var("empty list",bool))  []`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val LAST_CONS = store_thm(
  "LAST_CONS",
  ``(!x:'a. LAST [x] = x) /\
    (!(x:'a) y z. LAST (x::y::z) = LAST(y::z))``,
  REWRITE_TAC [LAST_DEF, NOT_CONS_NIL]);

val FRONT_CONS = store_thm(
  "FRONT_CONS",
  ``(!x:'a. FRONT [x] = []) /\
    (!x:'a y z. FRONT (x::y::z) = x :: FRONT (y::z))``,
  REWRITE_TAC [FRONT_DEF, NOT_CONS_NIL]);

val APPEND_FRONT_LAST = store_thm(
  "APPEND_FRONT_LAST",
  ``!l:'a list. ~(l = []) ==> (APPEND (FRONT l) [LAST l] = l)``,
  LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL] THEN
  POP_ASSUM MP_TAC THEN Q.SPEC_THEN `l` STRUCT_CASES_TAC list_CASES THEN
  REWRITE_TAC [NOT_CONS_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [FRONT_CONS, LAST_CONS, APPEND]);

val FILTER_APPEND_DISTRIB = Q.store_thm
("FILTER_APPEND_DISTRIB",
 `!P L M. FILTER P (APPEND L M) = APPEND (FILTER P L) (FILTER P M)`,
   GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC
    THEN RW_TAC bool_ss [FILTER,APPEND]);

(* ----------------------------------------------------------------------
    ALL_DISTINCT
   ---------------------------------------------------------------------- *)

val ALL_DISTINCT = new_recursive_definition {
  def = Term`(ALL_DISTINCT [] = T) /\
             (ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t)`,
  name = "ALL_DISTINCT",
  rec_axiom = list_Axiom};

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

(* ----------------------------------------------------------------------
    LIST_TO_SET
   ---------------------------------------------------------------------- *)

val LIST_TO_SET =
    new_definition("LIST_TO_SET", ``LIST_TO_SET = combin$C MEM``);

val IN_LIST_TO_SET = store_thm(
  "IN_LIST_TO_SET",
  ``x IN LIST_TO_SET l = MEM x l``,
  SRW_TAC [][LIST_TO_SET, boolTheory.IN_DEF]);
val _ = export_rewrites ["IN_LIST_TO_SET"]

(* ----------------------------------------------------------------------
    listRel
       lifts a binary relation to its point-wise extension on pairs of
       lists
   ---------------------------------------------------------------------- *)

val (listRel_rules, listRel_ind, listRel_cases) = IndDefLib.Hol_reln`
  listRel R [] [] /\
  (!h1 h2 t1 t2. R h1 h2 /\ listRel R t1 t2 ==>
                 listRel R (h1::t1) (h2::t2))
`;

val listRel_NIL = store_thm(
  "listRel_NIL",
  ``(listRel R [] y = (y = [])) /\ (listRel R x [] = (x = []))``,
  ONCE_REWRITE_TAC [listRel_cases] THEN SRW_TAC [][])
val _ = export_rewrites ["listRel_NIL"]

val listRel_CONS = store_thm(
  "listRel_CONS",
  ``(listRel R (h::t) y = ?h' t'. (y = h'::t') /\ R h h' /\ listRel R t t') /\
    (listRel R x (h'::t') = ?h t. (x = h::t) /\ R h h' /\ listRel R t t')``,
  CONJ_TAC THEN CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [listRel_cases])) THEN
  SRW_TAC [][])

val listRel_LENGTH = store_thm(
  "listRel_LENGTH",
  ``!x y. listRel R x y ==> (LENGTH x = LENGTH y)``,
  HO_MATCH_MP_TAC listRel_ind THEN SRW_TAC [][LENGTH])

val listRel_strong_ind = save_thm(
  "listRel_strong_ind",
  IndDefLib.derive_strong_induction(listRel_rules, listRel_ind))

val listRel_monotone = store_thm(
  "listRel_monotone",
  ``(!x y. R x y ==> R' x y) ==> (listRel R x y ==> listRel R' x y)``,
  STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC listRel_ind THEN SRW_TAC [][listRel_rules])


(*---------------------------------------------------------------------------*)
(* Tail recursive versions for better memory usage when applied in ML        *)
(*---------------------------------------------------------------------------*)

val _ = Defn.def_suffix := "_DEF";

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

(* --------------------------------------------------------------------- *)

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
   fun NL() = PP.add_newline ppstrm
 in
   S "local val hocongs = [EXISTS_CONG,EVERY_CONG,MAP_CONG,";
   S "                     FOLDL_CONG, FOLDR_CONG,list_size_cong]";
   S "in";
   S "val _ = DefnBase.write_congs (hocongs@DefnBase.read_congs())";
   S "end;";
   NL(); NL();
   S "val _ = let open computeLib";
   S "        in add_funs [APPEND,APPEND_NIL, FLAT, HD, TL,";
   S "              LENGTH, MAP, MAP2, NULL_DEF, MEM, EXISTS_DEF,";
   S "              EVERY_DEF, ZIP, UNZIP, FILTER, FOLDL, FOLDR,";
   S "              FOLDL, REVERSE_DEF, EL_compute, ALL_DISTINCT,";
   S "              computeLib.lazyfy_thm list_case_compute,";
   S "              list_size_def,FRONT_DEF,LAST_DEF]";
   S "        end;";
   NL(); NL();
   S "val _ =";
   S "  let val list_info = Option.valOf (TypeBase.read {Thy = \"list\",Tyop=\"list\"})";
   S "      val lift_list = mk_var(\"listSyntax.lift_list\",Parse.Type`:'type -> ('a -> 'term) -> 'a list -> 'term`)";
   S "      val list_info' = TypeBasePure.put_lift lift_list list_info";
   S "  in TypeBase.write [list_info']";
   S "  end;"
 end)};

val _ = BasicProvers.export_rewrites
          ["APPEND", "APPEND_11", "EL", "EVERY_DEF", "FLAT", "HD",
           "LENGTH", "MAP", "MAP2", "NULL_DEF",
           "SUM", "TL", "APPEND_ASSOC", "CONS", "CONS_11",
           "LENGTH_APPEND", "LENGTH_MAP", "MAP_APPEND",
           "NOT_CONS_NIL", "NOT_NIL_CONS", "MAP_EQ_NIL", "APPEND_NIL",
           "CONS_ACYCLIC", "list_case_def", "APPEND_eq_NIL", "ZIP",
           "UNZIP", "EVERY_APPEND", "EXISTS_APPEND", "EVERY_SIMP",
           "EXISTS_SIMP", "NOT_EVERY", "NOT_EXISTS",
           "LAST_CONS", "FRONT_CONS", "FOLDL", "FOLDR", "FILTER",
           "ALL_DISTINCT"];

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

val _ = EmitML.dest_cons_hook := dest_cons;
val _ = EmitML.dest_list_hook := dest_list;
val _ = EmitML.is_list_hook   := can dest_list;

(*---------------------------------------------------------------------------*)
(* Need to install the constructors for lists into the const map.          *)
(*---------------------------------------------------------------------------*)

val _ = ConstMapML.insert(Term.prim_mk_const{Name="CONS",Thy="list"});
val _ = ConstMapML.insert(Term.prim_mk_const{Name="NIL",Thy="list"});

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
  let val S = PP.add_string ppstrm
      fun NL() = PP.add_newline ppstrm
  in S "val _ = ConstMapML.insert (Term.prim_mk_const{Name=\"CONS\",Thy=\"list\"});";
     NL();
     S "val _ = ConstMapML.insert (Term.prim_mk_const{Name=\"NIL\",Thy=\"list\"});";
     NL(); NL()
  end)};


(*---------------------------------------------------------------------------*)
(* Export ML versions of list functions                                      *)
(*---------------------------------------------------------------------------*)

val LENGTH_THM = REWRITE_RULE [arithmeticTheory.ADD1] LENGTH;
val HD_NIL = Q.prove(`HD [] = FAIL HD ^(mk_var("Empty list",bool)) []`,
                     REWRITE_TAC [combinTheory.FAIL_THM]);
val TL_NIL = Q.prove(`TL [] = FAIL TL ^(mk_var("Empty list",bool)) []`,
                     REWRITE_TAC [combinTheory.FAIL_THM]);
val MAP2_THM = let val [a,b] = CONJUNCTS MAP2
                   val [c,d] = CONJUNCTS MAP2_FAIL
               in LIST_CONJ [a,c,d,b]
               end;
val ZIP_THM = let val [a,b] = CONJUNCTS ZIP
                  val [c,d] = CONJUNCTS ZIP_FAIL
               in LIST_CONJ [a,c,d,b]
               end;

val _ =
 let open EmitML
 in emitML (!Globals.emitMLDir)
      ("list",
         MLSIG "type num = numML.num"
         :: OPEN ["num"]
         ::
         map (DEFN o PURE_REWRITE_RULE[arithmeticTheory.NUMERAL_DEF])
             [NULL_DEF, CONJ HD_NIL HD, CONJ TL_NIL TL, APPEND, FLAT, MAP,
              MEM, FILTER, FOLDR, FOLDL, EVERY_DEF,
              EXISTS_DEF, MAP2_THM, ZIP_THM, UNZIP_THM, REVERSE_DEF,
              CONJ LAST_NIL LAST_CONS, CONJ FRONT_NIL FRONT_CONS,
              ALL_DISTINCT, EL_compute, LENGTH_THM, LEN_DEF, REV_DEF,
              list_size_def])
 end;

val _ = export_theory();

end
