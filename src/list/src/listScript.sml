(* ===================================================================== *)
(* FILE          : mk_list.sml                                           *)
(* DESCRIPTION   : The logical definition of the list type operator. The *)
(*                 type is defined and the following "axiomatization" is *)
(*                 proven from the definition of the type:               *)
(*                                                                       *)
(*                    |- !x f. ?!fn. (fn [] = x) /\                     *)
(*                             (!h t. fn (h::t) = f (fn t) h t)      *)
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

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;


(*---------------------------------------------------------------------------
 * Open structures used in the body.
 *---------------------------------------------------------------------------*)

open HolKernel Parse basicHol90Lib Num_conv ;
infix THEN ORELSE THENL THENC ORELSEC  |->;

type thm = Thm.thm;

val _ = new_theory "list";


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

val ADD_CLAUSES   = arithmeticTheory.ADD_CLAUSES;
val LESS_ADD_1    = arithmeticTheory.LESS_ADD_1;
val LESS_EQ       = arithmeticTheory.LESS_EQ;
val NOT_LESS      = arithmeticTheory.NOT_LESS;
val LESS_EQ_ADD   = arithmeticTheory.LESS_EQ_ADD;
val num_CASES     = arithmeticTheory.num_CASES;
val LESS_MONO_EQ  = arithmeticTheory.LESS_MONO_EQ;
val LESS_MONO_EQ  = arithmeticTheory.LESS_MONO_EQ;
val ADD_EQ_0      = arithmeticTheory.ADD_EQ_0;
val ONE           = arithmeticTheory.ONE;

val PAIR_EQ = pairTheory.PAIR_EQ;


val _ = Datatype.Hol_datatype `list = NIL | CONS of 'a => list`;

val _ = set_MLname "CONS" "CONS_def";

val _ = add_listform {separator = ";", leftdelim = "[", rightdelim = "]",
                      cons = "CONS", nilstr = "NIL"};

val _ = add_rule {term_name = "CONS", fixity = Infixr 300,
                  pp_elements = [TOK "::"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 2))};

(* ---------------------------------------------------------------------*)
(* Now, prove the axiomatization of lists.				*)
(* ---------------------------------------------------------------------*)

val listinfo = valOf (TypeBase.read "list")
val list_Axiom = TypeBase.axiom_of listinfo

val list_Axiom_old = store_thm(
  "list_Axiom_old",
  Term`!x f. ?!fn1:'a list -> 'b.
          (fn1 [] = x) /\ (!h t. fn1 (h::t) = f (fn1 t) h t)`,
  REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL [
    ASSUME_TAC list_Axiom THEN
    POP_ASSUM (ACCEPT_TAC o BETA_RULE o Q.SPECL [`x`, `\x y z. f z x y`]),
    REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
    Ho_resolve.MATCH_MP_TAC (TypeBase.induction_of listinfo) THEN
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
  new_specification{name = "MAP2", sat_thm = lemma,
                    consts = [{const_name="MAP2", fixity=Prefix}]}
  end

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

val list_INDUCT0 = TypeBase.induction_of listinfo;
(* only the variables have changed their names, but some proofs rely on
   names -- bad proofs! *)
val list_INDUCT = store_thm(
  "list_INDUCT",
  --`!P. P [] /\ (!t. P t ==> !h. P (h::t)) ==> !l. P l`--,
  REWRITE_TAC [list_INDUCT0]);  (* must use REWRITE_TAC, ACCEPT_TAC refuses
                                   to respect bound variable names *)
val list_induction = save_thm("list_induction", list_INDUCT);

val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(*---------------------------------------------------------------------------*)
(* Cases theorem: |- !l. (l = []) \/ (?t h. l = h::t)                        *)
(*---------------------------------------------------------------------------*)

val list_cases = TypeBase.nchotomy_of listinfo;
val list_CASES = store_thm(
  "list_CASES",
  --`!l. (l = []) \/ (?t h. l = h::t)`--,
  mesonLib.MESON_TAC [list_cases]);
val list_nchotomy = save_thm("list_nchotomy", list_CASES);

(*---------------------------------------------------------------------------*)
(* Definition of list_case more suitable to call-by-value computations       *)
(*---------------------------------------------------------------------------*)

val list_case_def = TypeBase.case_def_of listinfo
val list_case_compute = store_thm("list_case_compute",
 --`!(l:'a list). list_case (b:'b) f l =
                  if NULL l then b else f (HD l) (TL l)`--,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [list_case_def,HD, TL,NULL_DEF]);

(*---------------------------------------------------------------------------*)
(* CONS11:  |- !h t h' t'. (h::t = h' :: t') = (h = h') /\ (t = t')          *)
(*---------------------------------------------------------------------------*)

val CONS_11 = save_thm("CONS_11", valOf (TypeBase.one_one_of listinfo));

val NOT_NIL_CONS = save_thm("NOT_NIL_CONS",
                            valOf (TypeBase.distinct_of listinfo));

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

(* Computing EL when n is in numeral representation *)
val EL_compute = store_thm("EL_compute",
Term `!n. EL n l = if n=0 then HD l else EL (PRE n) (TL l)`,
INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC, EL, PRE]);

val WF_LIST_PRED = store_thm("WF_LIST_PRED",
Term`WF \L1 L2. ?h:'a. L2 = h::L1`,
REWRITE_TAC[relationTheory.WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC CONTRAPOS_CONV
  THEN Ho_rewrite.REWRITE_TAC
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
  (#2 (valOf (TypeBase.size_of listinfo)))
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


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "local val hocongs = [EXISTS_CONG,EVERY_CONG,MAP_CONG,";
   S "                     FOLDL_CONG, FOLDR_CONG,list_size_cong]";
   S "in";
   S "val _ = Defn0.write_context (hocongs@Defn0.read_context())";
   S "end;"
 end)};


val _ = export_theory();

end;
