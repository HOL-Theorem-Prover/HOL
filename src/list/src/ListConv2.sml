structure ListConv2 :> ListConv2 =
struct

open HolKernel Parse basicHol90Lib;

infix THEN THENL THENC ##;

type term = Term.term;
type thm = Thm.thm;
type conv = Abbrev.conv;


(* ========================================================================  *)
(*                                                                           *)
(* LIST_CONV is a conversion which returns theorems about terms of the       *)
(* following form:                                                           *)
(*                                                                           *)
(* (--`CONST1 ... (CONST2 ...) ...`--)                                       *)
(*                                                                           *)
(* where CONST1 and CONST2 are operators on lists.  CONST2 returns a list    *)
(* result. It can be one of NIL, CONS, SNOC, APPEND, FLAT or REVERSE.  The   *)
(* form of the resulting theorem depends on CONST1 and CONST2. Some          *)
(* auxiliary information must be provided about CONST1. LIST_CONV maintains a*)
(* database of such auxiliary information. It initially holds information    *)
(* about the constants in the system. However, it can be updated to include  *)
(* information about user-defined constants. The main information that is    *)
(* needed is a theorem defining the constant in terms of FOLDR or FOLDL. The *)
(* definition should generally have the form:                                *)
(*                                                                           *)
(* CONST1 ...l... = FOLDR f e l                                              *)
(*                                                                           *)
(* or                                                                        *)
(*                                                                           *)
(* CONST1 ...l... = FOLDL f e l                                              *)
(*                                                                           *)
(* where f is a function, e a base element and l a list variable.            *)
(*                                                                           *)
(* For example, a suitable theorem for SUM is                                *)
(*                                                                           *)
(* |- SUM l = FOLDR $+ 0 l                                                   *)
(*                                                                           *)
(* Knowing this theorem and given the term (--`SUM (CONS x l)`--),           *)
(* LIST_CONV returns the theorem:                                            *)
(*                                                                           *)
(* |- SUM (CONS x l) = x + (SUM l)                                           *)
(*                                                                           *)
(* Other auxiliary theorems that are needed concern the terms f and e found  *)
(* in the definition with respect to FOLDR or FOLDL. The most useful         *)
(* information that can be given is that f and e form a monoid. That is a    *)
(* theorem of the form:                                                      *)
(*                                                                           *)
(* |- MONOID f e                                                             *)
(*                                                                           *)
(* For example, knowing the theorem:                                         *)
(*                                                                           *)
(* |- MONOID $+ 0                                                            *)
(*                                                                           *)
(* and given the term (--`SUM (CONS x l)`--), LIST_CONV returns the theorem  *)
(*                                                                           *)
(* |- SUM (APPEND l1 l2) = (SUM l1) + (SUM l2)                               *)
(*                                                                           *)
(*                                                                           *)
(* f and e may not always form a monoid, however, in which case more         *)
(* restricted information can still be of use.                               *)
(*                                                                           *)
(* The following tables show the form of the theorem returned and the        *)
(*  auxiliary theorems needed.                                               *)
(*                                                                           *)
(* ==========================================================================*)
(*                     CONST1 ... l ... = FOLDR f e l                        *)
(* ==============|================================|==========================*)
(*               |                                |                          *)
(*  CONST2       |  side conditions               |tm2 in result |- tm1 = tm2*)
(* ==============|================================|==========================*)
(* []            | NONE                           | e                        *)
(* [h]           | NONE                           | f x e                    *)
(* CONS x l      | NONE                           | f x (CONST1 l)           *)
(* SNOC x l      | e is a list variable           | CONST1 (f x e) l         *)
(* APPEND l1 l2  | e is a list variable           | CONST1 (CONST1 l1) l2    *)
(* APPEND l1 l2  | |- FCOMM g f, |- LEFT_ID g e   | g (CONST1 l1) (CONST2 l2)*)
(* FLAT l1       | |- FCOMM g f, |- LEFT_ID g e,  |                          *)
(*               | |- CONST3 l = FOLDR g e l      | CONST3 (MAP CONST1 l)    *)
(* REVERSE l     | |- COMM f, |- ASSOC f          | CONST1 l                 *)
(* REVERSE l     | f == (\x l. h (g x) l)         |                          *)
(*               | |- COMM h, |- ASSOC h          | CONST1 l                 *)
(*                                                                           *)
(* ==========================================================================*)
(*                     CONST1 ... l ... = FOLDL f e l                        *)
(* ==============|================================|==========================*)
(*               |                                |                          *)
(*  CONST2       |  side conditions               |tm2 in result |- tm1 = tm2*)
(* ==============|================================|==========================*)
(* []            | NONE                           | e                        *)
(* [h]           | NONE                           | f x e                    *)
(* SNOC x l      | NONE                           | f x (CONST1 l)           *)
(* CONS x l      | e is a list variable           | CONST1 (f x e) l         *)
(* APPEND l1 l2  | e is a list variable           | CONST1 (CONST1 l1) l2    *)
(* APPEND l1 l2  | |- FCOMM f g, |- RIGHT_ID g e  | g (CONST1 l1) (CONST2 l2)*)
(* FLAT l1       | |- FCOMM f g, |- RIGHT_ID g e, |                          *)
(*               | |- CONST3 l = FOLDR g e l      | CONST3 (MAP CONST1 l)    *)
(* REVERSE l     | |- COMM f, |- ASSOC f          | CONST1 l                 *)
(* REVERSE l     | f == (\l x. h l (g x))         |                          *)
(*               | |- COMM h, |- ASSOC h          | CONST1 l                 *)
(*                                                                           *)
(* The theorem |- MONOID f e can be used at any point instead of |-FCOMM f f,*)
(* |- LEFT_ID f or |- RIGHT_ID f. |- ASSOC f can also be used in place of    *)
(* |- FCOMM f f.                                                             *)
(*                                                                           *)
(* Definitions of constants in terms of FOLDR and FOLDL are held in the      *)
(* assignable list variables, foldr_thms and foldl_thms respectively. Side   *)
(* condition (ie monoid, commutativity, associativity, left identity, right  *)
(*  identity and binary function commutativity) theorems are held in the     *)
(*  assignable list variables monoid_thms, comm_thms, assoc_thms,            *)
(*  left_id_thms, right_id_thms and fcomm_thms. These can be updated by the  *)
(*  user to allow LIST_CONV to prove theorems about new constants.           *)
(*                                                                           *)
(* The database initially holds FOLD{R/L} theorems for the following system  *)
(* constants: APPEND, FLAT, LENGTH, NULL, REVERSE, MAP, FILTER, ALL_EL, SUM, *)
(* SOME_EL, MEMBER, AND_EL, OR_EL, PREFIX, SUFFIX and FLAT combined with     *)
(* REVERSE.                                                                  *)
(* The following auxiliary information is stored:                            *)
(*                                                                           *)
(* |- MONOID $/\ T                                                           *)
(* |- MONOID $\/ F                                                           *)
(* |- MONOID $+ 0                                                            *)
(* |- MONOID APPEND []                                                       *)
(* |- MONOID (\l1 l2. APPEND l2 l1) []                                       *)
(*                                                                           *)
(* |- FCOMM $\/ (\x l'. T)                                                   *)
(* |- FCOMM (\l' x. T) $\/                                                   *)
(* |- FCOMM (\l' x. F) $/\                                                   *)
(* |- FCOMM $/\ (\x l'. F)                                                   *)
(* |- FCOMM (\n x. SUC n) $+                                                 *)
(* |- FCOMM $+ (\x n. SUC n)                                                 *)
(* |- FCOMM (\l1 l2. APPEND l2 l1) SNOC                                      *)
(* |- FCOMM (\l' x. CONS x l') (\l1 l2. APPEND l2 l1)                        *)
(* |- !P. FCOMM $/\ (\x l'. P x /\ l')                                       *)
(* |- !P. FCOMM (\l' x. l' /\ P x) $/\                                       *)
(* |- !P. FCOMM $\/ (\x l'. P x \/ l')                                       *)
(* |- !P. FCOMM (\l' x. l' \/ P x) $\/                                       *)
(* |- !f. FCOMM APPEND (\x l'. CONS (f x) l')                                *)
(* |- !f. FCOMM (\l' x. SNOC (f x) l') APPEND                                *)
(* |- !P. FCOMM (\l' x. (P x) => (SNOC x l') | l') APPEND                    *)
(* |- !P. FCOMM APPEND (\x l'. (P x) => (CONS x l') | l')                    *)
(*                                                                           *)
(* |- COMM $+                                                                *)
(* |- COMM $/\                                                               *)
(* |- COMM $\/                                                               *)
(* |- !c. COMM (\x y. c)                                                     *)
(*                                                                           *)
(* |- !c. ASSOC (\x y. c)                                                    *)
(*                                                                           *)
(* PURE_LIST_CONV is a version of the prover which does not use these        *)
(* databases. Instead, the definitions and auxiliary theorem lists must be   *)
(* provided as the first and second arguments, respectively.                 *)
(*                                                                           *)
(*===========================================================================*)

val FCOMM_DEF = operatorTheory.FCOMM_DEF;
val MONOID_DEF = operatorTheory.MONOID_DEF;
val COMM_DEF = operatorTheory.COMM_DEF;
val RIGHT_ID_DEF = operatorTheory.RIGHT_ID_DEF;
val ASSOC_DEF = operatorTheory.ASSOC_DEF;
val LEFT_ID_DEF = operatorTheory.LEFT_ID_DEF;

val FCOMM_ASSOC = operatorTheory.FCOMM_ASSOC;
val MONOID_DISJ_F = operatorTheory.MONOID_DISJ_F;
val MONOID_CONJ_T = operatorTheory.MONOID_CONJ_T;

val ASSOC_DEF = operatorTheory.ASSOC_DEF;
val RIGHT_ID_DEF = operatorTheory.RIGHT_ID_DEF;
val LEFT_ID_DEF = operatorTheory.LEFT_ID_DEF;
val MONOID_DEF = operatorTheory.MONOID_DEF;

val ADD_SYM = arithmeticTheory.ADD_SYM;
val ADD_ASSOC = arithmeticTheory.ADD_ASSOC;
val ADD = arithmeticTheory.ADD;
val ADD_CLAUSES = arithmeticTheory.ADD_CLAUSES;

val ASSOC_ADD = TAC_PROOF(([],    --`ASSOC $+`--),
    REWRITE_TAC[ASSOC_DEF,ADD_ASSOC]);

val RIGHT_ID_ADD_0 = TAC_PROOF(([], --`RIGHT_ID $+ 0`--),
    REWRITE_TAC[RIGHT_ID_DEF,ADD_CLAUSES]);

val LEFT_ID_ADD_0 = TAC_PROOF(([],    --`LEFT_ID $+ 0`--),
    REWRITE_TAC[LEFT_ID_DEF,ADD_CLAUSES]);
 
val MONOID_ADD_0 = TAC_PROOF(([],  --`MONOID $+ 0`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_ADD,
    	LEFT_ID_ADD_0,RIGHT_ID_ADD_0]);


val FOLDR = rich_listTheory.FOLDR;
val MAP = rich_listTheory.MAP;
val FLAT = rich_listTheory.FLAT;
val FOLDL = rich_listTheory.FOLDL;
val APPEND = rich_listTheory.APPEND;
val REVERSE = rich_listTheory.REVERSE;
val SNOC = rich_listTheory.SNOC;
val SUFFIX_DEF = rich_listTheory.SUFFIX_DEF;

val FCOMM_FOLDR_APPEND = rich_listTheory.FCOMM_FOLDR_APPEND;
val FCOMM_FOLDL_APPEND = rich_listTheory.FCOMM_FOLDL_APPEND;
val FCOMM_FOLDR_FLAT = rich_listTheory.FCOMM_FOLDR_FLAT;
val FCOMM_FOLDL_FLAT = rich_listTheory.FCOMM_FOLDL_FLAT;
val COMM_ASSOC_FOLDR_REVERSE = rich_listTheory.COMM_ASSOC_FOLDR_REVERSE;
val COMM_ASSOC_FOLDL_REVERSE = rich_listTheory.COMM_ASSOC_FOLDL_REVERSE;
val ASSOC_FOLDR_FLAT = rich_listTheory.ASSOC_FOLDR_FLAT;
val ASSOC_FOLDL_FLAT = rich_listTheory.ASSOC_FOLDL_FLAT;
val FOLDL_APPEND = rich_listTheory.FOLDL_APPEND;
val FOLDR_APPEND = rich_listTheory.FOLDR_APPEND;
val FOLDL_SNOC = rich_listTheory.FOLDL_SNOC;
val FOLDR_SNOC = rich_listTheory.FOLDR_SNOC;

val MAP_SNOC = rich_listTheory.MAP_SNOC;
val FLAT_SNOC = rich_listTheory.FLAT_SNOC;
val REVERSE_SNOC = rich_listTheory.REVERSE_SNOC;
val APPEND_SNOC = rich_listTheory.APPEND_SNOC;
val MONOID_APPEND_NIL = rich_listTheory.MONOID_APPEND_NIL;

val MAP_REVERSE = rich_listTheory.MAP_REVERSE;
val APPEND_ASSOC = rich_listTheory.APPEND_ASSOC;
val SNOC_APPEND = rich_listTheory.SNOC_APPEND;
val APPEND_NIL = rich_listTheory.APPEND_NIL;

val OR_EL_FOLDL = rich_listTheory.OR_EL_FOLDL;
val AND_EL_FOLDL = rich_listTheory.AND_EL_FOLDL;
val IS_EL_FOLDL = rich_listTheory.IS_EL_FOLDL;
val SOME_EL_FOLDL = rich_listTheory.SOME_EL_FOLDL;
val ALL_EL_FOLDL = rich_listTheory.ALL_EL_FOLDL;
val REVERSE_FOLDL = rich_listTheory.REVERSE_FOLDL;
val FILTER_FOLDL = rich_listTheory.FILTER_FOLDL;
val NULL_FOLDL = rich_listTheory.NULL_FOLDL;
val LENGTH_FOLDL = rich_listTheory.LENGTH_FOLDL;
val FLAT_FOLDL = rich_listTheory.FLAT_FOLDL;
val SUM_FOLDL = rich_listTheory.SUM_FOLDL; 
val MAP_FOLDL = rich_listTheory.MAP_FOLDL;  
val APPEND_FOLDL = rich_listTheory.APPEND_FOLDL;  

val OR_EL_FOLDR = rich_listTheory.OR_EL_FOLDR;
val AND_EL_FOLDR = rich_listTheory.AND_EL_FOLDR;
val IS_EL_FOLDR = rich_listTheory.IS_EL_FOLDR;
val SOME_EL_FOLDR = rich_listTheory.SOME_EL_FOLDR;
val ALL_EL_FOLDR = rich_listTheory.ALL_EL_FOLDR;
val REVERSE_FOLDR = rich_listTheory.REVERSE_FOLDR;
val FILTER_FOLDR = rich_listTheory.FILTER_FOLDR;
val NULL_FOLDR = rich_listTheory.NULL_FOLDR;
val LENGTH_FOLDR = rich_listTheory.LENGTH_FOLDR;
val FLAT_FOLDR = rich_listTheory.FLAT_FOLDR;
val SUM_FOLDR = rich_listTheory.SUM_FOLDR; 
val MAP_FOLDR = rich_listTheory.MAP_FOLDR;  
val APPEND_FOLDR = rich_listTheory.APPEND_FOLDR;  
val PREFIX_FOLDR = rich_listTheory.PREFIX_FOLDR;  
val SNOC_FOLDR = rich_listTheory.SNOC_FOLDR;



(* ======================================================================== *)
(* THEOREMS USED BY  LIST_CONV and PURE_LIST_CONV                           *)
(* ======================================================================== *)

val FCOMM_PRED_DISJ = prove(
(--`!P: 'a -> bool. FCOMM (\ l' x. l' \/ P x) $\/ `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[DISJ_ASSOC] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN
STRIP_TAC THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_PRED_CONJ = prove(
(--`!P: 'a -> bool. FCOMM (\ l' x. l' /\ P x) $/\ `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[CONJ_ASSOC] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN
STRIP_TAC THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)

val ASSOC_FOLDR_APPEND = prove(
(--`!(f:'a->'a->'a).
      ASSOC f ==>
      (!e. LEFT_ID f e ==>
       (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2)))
`--),
 REWRITE_TAC[FCOMM_FOLDR_APPEND,GSYM FCOMM_ASSOC]
);
(* ======================================================================== *)
val ASSOC_FOLDL_APPEND = prove(
(--`!(f:'a->'a->'a).
      ASSOC f ==>
      (!e. RIGHT_ID f e ==>
       (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2)))
`--),
 REWRITE_TAC[FCOMM_FOLDL_APPEND,GSYM FCOMM_ASSOC]
);

(* ======================================================================== *)
val MONOID_FOLDR_APPEND = prove(
(--`!(f:'a->'a->'a) e.
      MONOID f e ==>
       (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2))
`--),
 REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDR_APPEND THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val MONOID_FOLDL_APPEND = prove(
(--`!(f:'a->'a->'a) e.
      MONOID f e ==>
       (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2))
`--),
 REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDL_APPEND THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val MONOID_FOLDR_FLAT = prove(
(--`!(f:'a->'a->'a) e.
     MONOID f e ==>
           (!l. FOLDR f e (FLAT l) = FOLDR f e (MAP  (FOLDR f e) l))
`--),

GEN_TAC THEN
GEN_TAC THEN
DISCH_TAC THEN
ListConv1.LIST_INDUCT_TAC THEN
ASM_REWRITE_TAC[FLAT,MAP,FOLDR] THEN
IMP_RES_TAC MONOID_FOLDR_APPEND THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val MONOID_FOLDL_FLAT = prove(
(--`!(f:'a->'a->'a) e.
     MONOID f e ==>
           (!l. FOLDL f e (FLAT l) = FOLDL f e (MAP  (FOLDL f e) l))
`--),

GEN_TAC THEN
GEN_TAC THEN
DISCH_TAC THEN
ListConv1.SNOC_INDUCT_TAC THEN
ASM_REWRITE_TAC[FLAT_SNOC,MAP_SNOC,FLAT,MAP,FOLDL,FOLDL_SNOC] THEN
IMP_RES_TAC MONOID_FOLDL_APPEND THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val FCOMM_MONOID_FOLDR_APPEND = prove(
(--`! (g:'a->'a->'a) (f:'b->'a->'a).
     FCOMM g f ==>
     (!e. MONOID g e ==>
       (!l1 l2. FOLDR f e (APPEND l1 l2) = g (FOLDR f e l1) (FOLDR f e l2)))
`--),
 REWRITE_TAC[MONOID_DEF] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDR_APPEND THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val FCOMM_MONOID_FOLDL_APPEND = prove(
(--`! (f:'a->'b->'a)(g:'a->'a->'a).
     FCOMM f g ==>
     (!e. MONOID g e ==>
       (!l1 l2. FOLDL f e (APPEND l1 l2) = g (FOLDL f e l1) (FOLDL f e l2)))
`--),
 REWRITE_TAC[MONOID_DEF] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDL_APPEND THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val FCOMM_MONOID_FOLDR_FLAT = prove(
(--`!(g:'a->'a->'a) (f:'b->'a->'a) .
     FCOMM g f ==>
     (! e. MONOID g e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)))
`--),
 REWRITE_TAC[MONOID_DEF] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDR_FLAT THEN
 ASM_REWRITE_TAC[]
);

(* ======================================================================== *)
val FCOMM_MONOID_FOLDL_FLAT = prove(
(--`!(f:'a->'b->'a) (g:'a->'a->'a)  .
     FCOMM f g ==>
     (! e. MONOID g e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)))
`--),
 REWRITE_TAC[MONOID_DEF] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_FOLDL_FLAT THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val COMM_MONOID_FOLDR_REVERSE = prove(
(--`!(f:'a->'a->'a) .
     COMM f ==>
     (! e. MONOID f e ==>
       (!l. FOLDR f e (REVERSE l) = FOLDR f e l))
`--),
REWRITE_TAC[MONOID_DEF] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDR_REVERSE THEN
ASM_REWRITE_TAC[]
);

(* ======================================================================== *)
val COMM_MONOID_FOLDL_REVERSE = prove(
(--`!(f:'a->'a->'a) .
     COMM f ==>
     (! e. MONOID f e ==>
       (!l. FOLDL f e (REVERSE l) = FOLDL f e l))
`--),
REWRITE_TAC[MONOID_DEF] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDL_REVERSE THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val FOLDR_FOLDR_MAP = prove(
(--`!(f:'a->'b->'b) (g:'c->'a) l.
           FOLDR (\x l. f (g x) l) e l = FOLDR f e (MAP g l)
`--),

GEN_TAC THEN
GEN_TAC THEN
ListConv1.LIST_INDUCT_TAC THEN
ASM_REWRITE_TAC[FOLDR, MAP] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)
val COMM_ASSOC_FOLDR_REVERSE2 = prove(
(--`!(f:'a->'a->'a) .
     COMM f /\ ASSOC f ==>
       (!(g:'b->'a) l. FOLDR (\x l. f (g x) l) e (REVERSE l) = 
                   FOLDR (\x l. f (g x) l) e l)
`--),
REWRITE_TAC [FOLDR_FOLDR_MAP] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDR_REVERSE THEN
ASM_REWRITE_TAC[MAP_REVERSE]
);
(* ======================================================================== *)
val COMM_MONOID_FOLDR_REVERSE2 = prove(
(--`!(f:'a->'a->'a) .
     COMM f ==>
     (! e. MONOID f e ==>
       (!(g:'b->'a) l. FOLDR (\x l. f (g x) l) e (REVERSE l) =
                 FOLDR (\x l. f (g x) l) e l))
`--),
REWRITE_TAC[MONOID_DEF] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDR_REVERSE2 THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)
val FOLDL_FOLDL_MAP = prove(
(--`!(f:'a->'b->'a) (g:'c->'b) l.
           FOLDL (\l x. f l (g x)) e l = FOLDL f e (MAP g l)
`--),

GEN_TAC THEN
GEN_TAC THEN
ListConv1.SNOC_INDUCT_TAC THEN
ASM_REWRITE_TAC[FOLDL, MAP, MAP_SNOC, FOLDL_SNOC] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)
val COMM_ASSOC_FOLDL_REVERSE2 = prove(
(--`!(f:'a->'a->'a) .
     COMM f /\ ASSOC f ==>
       (!(g:'b->'a) l. FOLDL (\l x. f l (g x)) e (REVERSE l) = 
                   FOLDL (\l  x. f l (g x)) e l)
`--),
REWRITE_TAC [FOLDL_FOLDL_MAP] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDL_REVERSE THEN
ASM_REWRITE_TAC[MAP_REVERSE]
);
(* ======================================================================== *)
val COMM_MONOID_FOLDL_REVERSE2 = prove(
(--`!(f:'a->'a->'a) .
     COMM f ==>
     (! e. MONOID f e ==>
       (!(g:'b->'a) l. FOLDL (\l x. f l (g x)) e (REVERSE l) =
                 FOLDL (\l x. f l (g x)) e l))
`--),
REWRITE_TAC[MONOID_DEF] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC COMM_ASSOC_FOLDL_REVERSE2 THEN
ASM_REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_RAPPEND_SNOC = prove(
(--`FCOMM (\l1 l2. APPEND l2 l1) (SNOC:'a->'a list->'a list)`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[APPEND,SNOC_APPEND,APPEND_ASSOC]
);
(* ======================================================================== *)

val FCOMM_CONS_RAPPEND = prove(
(--`FCOMM (\l' x . CONS x l') (\l1 l2. APPEND l2 (l1:'a list))`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[APPEND,SNOC_APPEND,APPEND_ASSOC]
);

(* ======================================================================== *)
val MONOID_RAPPEND_NIL = prove(
(--`MONOID (\l1 l2. APPEND l2 l1) ([]:'a list)`--),

REWRITE_TAC[MONOID_DEF, LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[APPEND,APPEND_NIL,APPEND_ASSOC]
);
(* ======================================================================== *)
val FLAT_REVERSE_FOLDR = prove(
(--`!l. 
     (FLAT o REVERSE) (l:'a list list) = 
            FOLDR (\l1 l2. APPEND l2 l1) [] l
`--),

REWRITE_TAC[combinTheory.o_THM] THEN
ListConv1.LIST_INDUCT_TAC THEN
REWRITE_TAC[REVERSE, FLAT, FOLDR] THEN
BETA_TAC THEN
ASM_REWRITE_TAC [FLAT_SNOC]
);
(* ======================================================================== *)
val FLAT_REVERSE_FOLDL = prove(
(--`!l. 
     (FLAT o REVERSE) (l:'a list list) = 
            FOLDL (\l1 l2. APPEND l2 l1) [] l
`--),

REWRITE_TAC[combinTheory.o_THM] THEN
ListConv1.SNOC_INDUCT_TAC THEN
REWRITE_TAC[REVERSE_SNOC,REVERSE, FLAT, FOLDL, FOLDL_SNOC] THEN
BETA_TAC THEN
ASM_REWRITE_TAC [FLAT_SNOC]

);
(* ======================================================================== *)
val ASSOC_CONST = prove(
(--`!(c:'a). ASSOC (\x y. c)`--),

REWRITE_TAC[ ASSOC_DEF]
);
(* ======================================================================== *)
val COMM_CONST = prove(
(--`!(c:'a). COMM (\(x:'b) y. c)`--),

REWRITE_TAC[COMM_DEF]
);
(* ======================================================================== *)
val COMM_DISJ = prove(
(--`COMM $\/`--),

REWRITE_TAC[COMM_DEF] THEN
REPEAT GEN_TAC THEN
SUBST1_TAC(SPECL[(--`x:bool`--),(--`y:bool`--)]DISJ_SYM) THEN
REWRITE_TAC[]
);

val COMM_ADD = prove(
(--`COMM $+`--),

REWRITE_TAC[COMM_DEF] THEN
REPEAT GEN_TAC THEN
SUBST1_TAC(SPECL[(--`x:num`--),(--`y:num`--)]ADD_SYM) THEN
REWRITE_TAC[]
);
(* ======================================================================== *)
val COMM_CONJ = prove(
(--`COMM $/\`--),

REWRITE_TAC[COMM_DEF] THEN
REPEAT GEN_TAC THEN
SUBST1_TAC(SPECL[(--`x:bool`--),(--`y:bool`--)]CONJ_SYM) THEN
REWRITE_TAC[]
);


val FCOMM_CONJ_PRED = prove(
(--`!(P: 'a -> bool). FCOMM $/\ (\x l'. P x /\ l') `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[CONJ_ASSOC]
);
(* ======================================================================== *)

val FCOMM_DISJ_PRED = prove(
(--`!(P: 'a -> bool). FCOMM $\/ (\x l'. P x \/ l') `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[DISJ_ASSOC]
);
(* ======================================================================== *)

val FCOMM_CONJ_F = prove(
(--`FCOMM $/\ ((\x l'. F):'a -> bool -> bool)`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_F_CONJ = prove(
(--`FCOMM ((\ l' x. F):bool -> 'a ->  bool) $/\ `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_DISJ_T = prove(
(--`FCOMM $\/ ((\x l'. T):'a -> bool -> bool)`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_T_DISJ = prove(
(--`FCOMM ((\ l' x. T):bool -> 'a ->  bool) $\/ `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[]
);
(* ======================================================================== *)

val FCOMM_ADD_SUC = prove(
(--`FCOMM $+ ((\x n. SUC n):'a -> num -> num)`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[ADD]
);
(* ======================================================================== *)

val FCOMM_SUC_ADD = prove(
(--`FCOMM ((\ n x. SUC n):num -> 'a ->  num) $+ `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[ADD_CLAUSES]
);
(* ======================================================================== *)

val FCOMM_APPEND_FILT = prove(
(--`!(P:'a->bool). FCOMM APPEND (\x l'. (P x) => (CONS x l') | l')`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REPEAT STRIP_TAC THEN
COND_CASES_TAC THEN
REWRITE_TAC[APPEND]
);
(* ======================================================================== *)

val FCOMM_FILT_APPEND = prove(
(--`!(P:'a->bool). FCOMM (\l' x. (P x) => (SNOC x l') | l') APPEND `--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REPEAT STRIP_TAC THEN
COND_CASES_TAC THEN
REWRITE_TAC[APPEND_SNOC,SNOC_APPEND]
);

(* ======================================================================== *)

val FCOMM_APPEND_CONS = prove(
(--`!f: 'a ->'b. FCOMM APPEND (\x l'. CONS (f x) l')`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[APPEND]
);

val FCOMM_SNOC_APPEND = prove(
(--`!f: 'a->'b. FCOMM (\l' x. SNOC (f x) l') APPEND`--),

REWRITE_TAC[FCOMM_DEF] THEN
BETA_TAC THEN
REWRITE_TAC[APPEND_SNOC]
);
(* ======================================================================== *)
val FCOMM_IDEQ_FOLDR_REVERSE = prove(
(--`!(f:'a->'a->'a) (g:'a->'a->'a)  .
     FCOMM g f ==>
      (!e. (!h. f h e = g e h) ==>
       (!l. FOLDR f e l = FOLDL g e l))
`--),
 REWRITE_TAC[FCOMM_DEF] THEN
 REPEAT GEN_TAC THEN
 REPEAT DISCH_TAC THEN
 GEN_TAC THEN DISCH_TAC THEN
 ListConv1.LIST_INDUCT_TAC THEN
 ASM_REWRITE_TAC[FOLDR,FOLDL] THEN
 SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--)) THEN
 ListConv1.SNOC_INDUCT_TAC THEN
 REWRITE_TAC[FOLDR,FOLDL,SNOC,FOLDR_SNOC,FOLDL_SNOC,
             ASSUME (--`!h. (f:'a->'a->'a) h e = g e h`--)] THEN
 POP_ASSUM (ASSUME_TAC o GSYM) THEN
 ASM_REWRITE_TAC[]
);
(* ======================================================================== *)

val COMM_FCOMM_FOLDR_REVERSE = prove(
(--`!(f:'a->'a->'a) .
     COMM f ==>
      (! (g:'a->'a->'a).
         FCOMM f g ==>
            (!e. (!h. g h e = f e h) ==>
                  (!l. FOLDR f e (REVERSE l) = FOLDR g e l)))
`--),

 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_IDEQ_FOLDR_REVERSE THEN
 ASM_REWRITE_TAC[] THEN
 SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--)) THEN
 ListConv1.SNOC_INDUCT_TAC THEN
 ASM_REWRITE_TAC[FOLDR,FOLDL,REVERSE, FOLDL_SNOC, FOLDR_SNOC, REVERSE_SNOC] THEN
 GEN_TAC THEN
 REWRITE_TAC[ SPEC (--`FOLDL (f:'a->'a->'a) e l`--)
       (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (f:'a->'a->'a)`--)))]
);

(* ======================================================================== *)

val COMM_FCOMM_FOLDL_REVERSE = prove(
(--`!(g:'a->'a->'a) .
     COMM g ==>
      (! (f:'a->'a->'a).
         FCOMM f g ==>
            (!e. (!h. g h e = f e h) ==>
                  (!l. FOLDL f e (REVERSE l) = FOLDL g e l)))
`--),

 REPEAT STRIP_TAC THEN
 IMP_RES_TAC FCOMM_IDEQ_FOLDR_REVERSE THEN
 POP_ASSUM (ASSUME_TAC o GSYM) THEN
 ASM_REWRITE_TAC[] THEN
 SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--)) THEN
 ListConv1.SNOC_INDUCT_TAC THEN
 ASM_REWRITE_TAC[FOLDR,FOLDL,REVERSE, FOLDL_SNOC, FOLDR_SNOC, REVERSE_SNOC] THEN
 GEN_TAC THEN
 REWRITE_TAC[ SPEC (--`FOLDL (g:'a->'a->'a) e l`--)
       (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (g:'a->'a->'a)`--)))]
);


(* ======================================================================== *)
(*  AUXILIARY DEFINITIONS                                                   *)
(* ======================================================================== *)

fun get_operator tm = fst (strip_comb tm);
fun get_arglist tm = snd (strip_comb tm);

fun get_def_lhs th =
       #Rand(dest_comb (#Rator (dest_comb 
                  (snd (strip_forall(snd (dest_thm th)))))));

fun get_def_rhs th =
       #Rand (dest_comb 
                  (snd (strip_forall(snd (dest_thm th)))));

(* Is a definition of the form ... = OP ... *)
fun is_fold_def s th =
     let val op1 =  #Name (dest_const (fst (strip_comb(get_def_rhs th))));
     in
       op1 = s
     end handle HOL_ERR _ => false;

(* Is th a definition of (string) op0 *)
fun is_X_def op0 th =
     let val op1 = #Name (dest_const op0);
         val op2 =  #Name (dest_const (fst (strip_comb(get_def_lhs th))));
     in
       op1 = op2
     end;

(* Is a theorem of the form |- !... .OP .... where the name of op is s *)
fun is_X_thm s th = 
    let val tm = snd (dest_thm th)
        val oper = get_operator (snd (strip_forall tm))
    in
       (#Name(dest_const oper)) = s
    end handle HOL_ERR _ => false;

fun filter_X_thm s = filter (is_X_thm s);


(* Get l from |- ... = FOLD{R/L} f e l *)
fun get_folddef_var th =
     let val foldtm = get_def_rhs th
          val vartm = #Rand(dest_comb foldtm)
      in
         vartm
      end;

(* Get (f, e) from |- ... = FOLD{R/L} f e l *)

fun get_folddef_fe th =
     let val foldtm = get_arglist (get_def_rhs th)
          val unit_tm = el 2 foldtm
          val fn_tm = el 1 foldtm
      in
         (fn_tm, unit_tm)
      end;

fun get_list_posn a l =
  let fun get_list_posn1 a [] n =
                 raise HOL_ERR{origin_structure = "",
                               origin_function = "get_list_posn",
                               message = ""}
       |   get_list_posn1 a (x :: xs) n =
                  if a = x 
                  then  n
                  else get_list_posn1 a xs (n + 1)
  in
     get_list_posn1 a l 1
  end;


fun get_subs_term folddef tm =
  let val v = get_folddef_var folddef;
      val tm_arglist = get_arglist tm;
      val thm_arglist = get_arglist (get_def_lhs folddef);
      val n = get_list_posn v thm_arglist
  in
    if tm_arglist = [] (* eg the term is NIL *)
    then
        get_operator tm (* return that term rather than destructing it *)
    else
        el n tm_arglist
  end ;
 

(*
fun is_list_ty ty = 
        (#Tyop (dest_type ty) = "list")
        handle _ => false;
*)

fun is_term_match t1 t2 =
     (match_term t1 t2; true) handle HOL_ERR _ => false;

(* Either returns an instantiated thm or fails if
   f and e do not match the f and e in theorem th
   which has the form |- !... .OP f e ... *)

fun check_fe_th f e th =
    let val tm = snd (dest_thm th)
        val args = get_arglist (snd (strip_forall tm));
        val fth = el 1 args
        val eth = el 2 args
        val tm1 = (--`(^f, ^e)`--)
        val tm2 = (--`(^fth, ^eth)`--)
    in
      INST_TY_TERM (match_term tm2 tm1) (SPEC_ALL th)
    end;

(* Either returns an instantiated thm or fails if
   f does not match the f in theorem th
   which has the form |- !... .OP f ... *)

fun check_f_th fpos f th =
    let val tm = snd (dest_thm th)
        val args = get_arglist (snd (strip_forall tm));
    in
      INST_TY_TERM (match_term (el fpos args) f) (SPEC_ALL th)
   end;

val check_monoid_th = check_fe_th;
val check_id_th = check_fe_th;

val check_assoc_th = check_f_th 1;
val check_comm_th = check_f_th 1;
val check_fcommr_th = check_f_th 2;
val check_fcomml_th = check_f_th 1;

(* Get the nth argument of a theorem of the form
   |- !... .OP a1 a2 ...
*)
fun get_fcomm_g n th =
    let val tm = snd (dest_thm th)
        val args = get_arglist (snd (strip_forall tm));
    in
        el n args
    end;

val get_fcomml_g = get_fcomm_g 1;
val get_fcommr_g = get_fcomm_g 2;


(* Filters out the elements of thl  which match according to check_fn 
   (which is expected to instantiate the theorems with the match)
*)

fun find_all_thms check_fn [] = []
 |  find_all_thms check_fn (x:: xs) =
        ((check_fn x) :: find_all_thms check_fn xs)
        handle HOL_ERR _ =>  find_all_thms check_fn xs (* No match *);
(*
Returns the first theorem that matches according to check_fn 
   (which is expected to instantiate the theorems with the match)
*)

fun find_thms check_fn [] = []
 |  find_thms check_fn (x:: xs) =
        [check_fn x]
        handle HOL_ERR _ =>  find_thms check_fn xs (* No match *);


(* Return a list containing 2 lists. The first holds an FCOMM theorem about
   some g, the second either an ID theorem about g with e.
   For each FCOMM theorem in the list given, it checks if there is a
   corresponding ID theorem. If so it stops. Otherwise it moves to the next
   FCOMM theorem.
*)
fun find_fcomm_id_thms get_fcomm_g e all_id_ths [] = []
 |  find_fcomm_id_thms get_fcomm_g  e all_id_ths (fcommth::xs) =
           let val g = get_fcomm_g fcommth;
               val idths = find_thms (check_fe_th g e) all_id_ths
           in
             if null idths
             then
                 find_fcomm_id_thms get_fcomm_g  e all_id_ths xs
             else
                [[fcommth], idths]
           end;

val find_fcomml_idl_thms = find_fcomm_id_thms get_fcomml_g;
val find_fcommr_idr_thms = find_fcomm_id_thms get_fcommr_g;
val find_fcommr_monoid_thms = find_fcomm_id_thms get_fcommr_g;
val find_fcomml_monoid_thms = find_fcomm_id_thms get_fcomml_g;

fun LIST_MATCH_MP [] th = th
 |  LIST_MATCH_MP (x :: thl) th = LIST_MATCH_MP thl (MATCH_MP th x);

fun chop_folddef_arg folddef =
  let val foldvar = get_folddef_var folddef;
  in
         GEN_ALL (CONV_RULE (ONCE_DEPTH_CONV ETA_CONV)
                 (ABS foldvar (SPEC_ALL folddef)))
  end;


(* f has form (\x l. g a b) : extract g *)

fun get_g_from_abs2 f =
        (fst (strip_comb (#Body (dest_abs (#Body (dest_abs f))))));


fun not_eq_nil l = not (null l);

(* Given a term (--`OP a b ... (OP2 x y ..) ...`--), this function returns the
    term (--`OP2`--) and the list of term args [(--`x`--),(--`y`--),...]
   It needs the fold definition argument to determine which argument of OP
   to extract : it is that in position l given definition
     OP a b ... l ... = FOLD{R/L} f e l
*)
fun get_subterm_constant folddef tm =
    let val subs_tm =  get_subs_term folddef tm;
    in
      strip_comb subs_tm
    end;

(* ======================================================================== *)
(*  MAIN PROOF DEFINITIONS                                                  *)
(* ======================================================================== *)

(* Rewrite with a definition (in terms of FOLD{R/L}) and higher_order
   theorems about FOLD, do BETA conversion, then rewrite backwards with a
   set of defintiions  (in terms of FOLD{R/L})
*)

fun PROVE_CONV  def1 def2s thms tm =
       ((REWRITE_CONV (def1 :: thms)) THENC
       (REDEPTH_CONV BETA_CONV) THENC
       (REWRITE_CONV (map GSYM def2s))) tm;

(* As above, but the higher_order theorems about FOLD have assumptions which
   are matched against the given list of auxiliary facts auxthms in the order
   given. Each theorem in auxthms is actually in a list so must be stripped
   out first.
*)
fun PROVE_LCONV mainthm auxthms def1 def2s tm  =
     let val auxthms1 = map hd auxthms
     in
        PROVE_CONV def1 def2s
                   [LIST_MATCH_MP auxthms1 mainthm]
                   tm
     end;

(* Rewrite back with same definition in terms of FOLD as originally used
*)
fun PROVE_CONV1 def thms tm  =
        PROVE_CONV  def [def] thms tm;

fun PROVE_LCONV1 mainthm auxthms def tm  =
        PROVE_LCONV mainthm auxthms def [def] tm;


fun PROVE_CHOP_LCONV mainthm auxthms def tm  =
        PROVE_LCONV mainthm auxthms def [chop_folddef_arg def] tm;

fun PROVE_BACK_CHOP_LCONV get_fcomm_g mainthm all_folddefs e auxthms
                          var_folddef tm =
 let fun folddef_match f e th =
     let val (f1, e1) = get_folddef_fe th;
         val tm1 = (--`(^f, ^e)`--)
         val tm2 = (--`(^f1, ^e1)`--)
     in
       is_term_match tm2 tm1
     end handle HOL_ERR _ => false; 

     fun find_folddef_match  g e thl =
         filter (folddef_match g e) thl;

     val [fcomm_thms, id_thms] = auxthms;
     val g = get_fcomm_g (hd fcomm_thms)
     val back_folddef = find_folddef_match g e all_folddefs
 in     
    PROVE_LCONV mainthm 
                   auxthms
                   var_folddef
                   ((chop_folddef_arg var_folddef) :: back_folddef) tm
 end;

(* ======================================================================== *)
(*                                                                          *)
(*                         APPEND                                           *)
(*                                                                          *)
(* ======================================================================== *)

fun PROVE_APPEND_CONV block 
        (check_fcomm_fn, get_fcomm_g_fn,
         var_pthm, monoid_pthm,assoc_pthm, fcomm_monoid_pthm,fcomm_id_pthm)
        (all_monoid_thms, all_fcomm_thms, all_comm_thms,
         all_assoc_thms, all_id_thms)
        var_folddef tm =
  let val instantiated_foldth = REWRITE_CONV [var_folddef] tm;
      val (f,e) = get_folddef_fe instantiated_foldth;
  in
   if is_var (snd (get_folddef_fe var_folddef)) andalso (not block)
   then PROVE_CONV1 var_folddef [var_pthm] tm
   else 
    let val monoid_thms = find_thms (check_monoid_th f e) all_monoid_thms;
        val not_monoid_nil = not_eq_nil monoid_thms;
    in
     if not_monoid_nil
     then
        PROVE_LCONV1 monoid_pthm [monoid_thms] var_folddef tm
     else
      let val assoc_thms = find_thms (check_assoc_th f) all_assoc_thms;
          val id_thms = find_thms (check_id_th f e) all_id_thms;
          val not_assoc_nil = not_eq_nil assoc_thms;
          val not_id_nil = not_eq_nil id_thms;
      in
       if not_assoc_nil andalso
          not_id_nil
       then
          PROVE_LCONV1 assoc_pthm [assoc_thms, id_thms] var_folddef tm
       else
        let val fcomm_thms = find_thms (check_fcomm_fn f) all_fcomm_thms;
            val fcomm_monoid_thms =
              find_fcomm_id_thms get_fcomm_g_fn e all_monoid_thms fcomm_thms;
            val not_fcomm_monoid_nil = not_eq_nil fcomm_monoid_thms;
        in
         if not_fcomm_monoid_nil
         then
            PROVE_LCONV1 fcomm_monoid_pthm 
                         fcomm_monoid_thms
                         var_folddef tm
         else
          let val fcomm_id_thms =
               find_fcomm_id_thms get_fcomm_g_fn e all_id_thms fcomm_thms;
              val not_fcomm_id_nil =  not_eq_nil fcomm_id_thms;
          in
           if not_fcomm_id_nil
           then
             PROVE_LCONV1 fcomm_id_pthm 
                          fcomm_id_thms var_folddef tm
           else 
            raise HOL_ERR
                   {message = "I do not know enough auxiliary information",
                    origin_function = "LIST_CONV: ",
                    origin_structure = ""}
          end
        end
      end
    end
  end;

(* ======================================================================== *)
(*                                                                          *)
(*                         FLAT                                             *)
(*                                                                          *)
(* ======================================================================== *)
fun PROVE_FLAT_CONV
  (check_fcomm_fn, get_fcomm_g_fn,
   monoid_pthm, assoc_pthm, fcomm_monoid_pthm, fcomm_id_pthm)
  all_folddefs
  (all_monoid_thms, all_fcomm_thms, all_comm_thms,
   all_assoc_thms, all_id_thms)
  var_folddef tm =

  let val instantiated_foldth = REWRITE_CONV [var_folddef] tm;
      val (f,e) = get_folddef_fe instantiated_foldth;

 in
  let val monoid_thms = find_thms (check_monoid_th f e) all_monoid_thms;
      val not_monoid_nil = not_eq_nil monoid_thms;
  in
   if not_monoid_nil
   then 
       PROVE_CHOP_LCONV monoid_pthm 
                        [monoid_thms] var_folddef tm
   else
    let val assoc_thms = find_thms (check_assoc_th f) all_assoc_thms;
        val id_thms = find_thms (check_id_th f e) all_id_thms;
        val not_assoc_nil = not_eq_nil assoc_thms;
        val not_id_nil = not_eq_nil id_thms;
    in
     if not_assoc_nil andalso
        not_id_nil
     then
        PROVE_CHOP_LCONV assoc_pthm 
                         [assoc_thms, id_thms] var_folddef tm
     else
      let val fcomm_thms = find_all_thms (check_fcomm_fn f) all_fcomm_thms;
          val fcomm_monoid_thms =
             find_fcomm_id_thms get_fcomm_g_fn e all_monoid_thms fcomm_thms;
          val not_fcomm_monoid_nil = not_eq_nil fcomm_monoid_thms;
      in
       if not_fcomm_monoid_nil
       then
         PROVE_BACK_CHOP_LCONV get_fcomm_g_fn fcomm_monoid_pthm 
                    all_folddefs e 
                    fcomm_monoid_thms var_folddef tm
       else
        let val fcomm_id_thms =
             find_fcomm_id_thms get_fcomm_g_fn e all_id_thms fcomm_thms;
            val not_fcomm_id_nil =  not_eq_nil fcomm_id_thms;
        in
         if not_fcomm_id_nil
         then
           PROVE_BACK_CHOP_LCONV get_fcomm_g_fn fcomm_id_pthm 
                   all_folddefs e 
                   fcomm_id_thms var_folddef tm
         else raise HOL_ERR{message = 
              "I do not know enough auxiliary information",
               origin_function = "LIST_CONV: ",
               origin_structure = ""}
       end
     end
    end
   end
  end;

(* ======================================================================== *)
(*                                                                          *)
(*                          CONS                                            *)
(*                                                                          *)
(* ======================================================================== *)

fun PROVE_CONS_CONV proofthms folddef tm =
        PROVE_CONV1 folddef proofthms tm;

(* ======================================================================== *)
(*                                                                          *)
(*                         SNOC                                             *)
(*                                                                          *)
(* ======================================================================== *)

fun PROVE_SNOC_CONV block proofthms folddef tm =
     if not block
     then
        raise HOL_ERR{message = 
              "Only the symmetrical form of this theorem can be proven",
               origin_function = "LIST_CONV: ",
               origin_structure = ""}
     else
        PROVE_CONV1 folddef proofthms tm;


(* ======================================================================== *)
(*                                                                          *)
(*                         REVERSE                                          *)
(*                                                                          *)
(* ======================================================================== *)
fun PROVE_REVERSE_CONV1 f e 
       (monoid_pthm, assoc_pthm)
       (all_monoid_thms, all_comm_thms, all_assoc_thms) folddef tm =

 let val monoid_thms = find_thms (check_monoid_th f e) all_monoid_thms;
     val comm_thms = find_thms (check_comm_th f) all_comm_thms;
     val not_monoid_nil = not_eq_nil monoid_thms
     val not_comm_nil = not_eq_nil comm_thms
 in
 if not_monoid_nil andalso
    not_comm_nil
 then 
     PROVE_LCONV1 monoid_pthm
                 [comm_thms,monoid_thms]folddef tm
 else
  let val assoc_thms = find_thms (check_assoc_th f) all_assoc_thms;
      val not_assoc_nil = not_eq_nil assoc_thms;
  in
   if not_assoc_nil andalso
      not_comm_nil
   then 
     PROVE_LCONV1 assoc_pthm [comm_thms,assoc_thms]folddef tm
   else raise HOL_ERR{message = 
            "I do not know enough auxiliary information",
             origin_function = "LIST_CONV: ",
             origin_structure = ""}
  end
 end;

fun PROVE_REVERSE_CONV 
      (m, monoid_pthm, assoc_pthm, split_monoid_pthm, split_assoc_pthm)
      (all_monoid_thms, all_fcomm_thms, all_comm_thms,
       all_assoc_thms, all_id_thms)
      folddef tm =

  let val instantiated_foldth = REWRITE_CONV [folddef] tm;
      val (f,e) = get_folddef_fe instantiated_foldth;
  in
  if not (is_term_match m f)
  then
    PROVE_REVERSE_CONV1 f e 
       (monoid_pthm, assoc_pthm)
       (all_monoid_thms, all_comm_thms, all_assoc_thms) folddef tm
  else
   let val g = get_g_from_abs2 f; (* get g from (\x l. g a b) *)
   in
    PROVE_REVERSE_CONV1 g e 
       (split_monoid_pthm, split_assoc_pthm)
       (all_monoid_thms, all_comm_thms, all_assoc_thms) folddef tm
   end
 end;

(* ======================================================================== *)
(* ======================================================================== *)

fun PROVE_LIST_CONV
    (block, fold_name,fold_pthm,fold_snoc_pthm,
            append_pthms,flat_pthms,reverse_pthms)
    all_folddefs auxthms var_folddef tm =
  let val (const,args) = get_subterm_constant var_folddef tm;
      val const_nm = #Name (dest_const const) handle HOL_ERR _ =>
                     raise HOL_ERR{message = "Inner operator not a constant",
                                   origin_function = "LIST_CONV: ",
                                   origin_structure = ""};
      val th =
         (case const_nm of
         "NIL" =>
             REWRITE_CONV[var_folddef, fold_pthm] tm |
         "CONS" =>
             PROVE_CONS_CONV [fold_pthm] var_folddef tm  |
         "SNOC" =>
             PROVE_SNOC_CONV block [fold_snoc_pthm,fold_pthm] var_folddef tm |
                  (* fold_pthm (eg FOLDR) is needed for NIL case *)
         "APPEND" =>
             PROVE_APPEND_CONV block append_pthms auxthms var_folddef tm |
         "FLAT" =>
             PROVE_FLAT_CONV flat_pthms all_folddefs auxthms var_folddef tm  |
         "REVERSE" =>
           PROVE_REVERSE_CONV reverse_pthms auxthms var_folddef tm |
          _ => raise HOL_ERR{message = "Inner operator unknown",
                                    origin_function = "LIST_CONV: ",
                                    origin_structure = ""})
  in
      if (get_def_lhs th  = get_def_rhs th) orelse
         is_fold_def fold_name th
      then raise HOL_ERR{message = "I cannot prove anything useful",
                        origin_function = "LIST_CONV: ",
                        origin_structure = ""}
      else th 
   end;

val foldl_thms = ref
[
APPEND_FOLDL,
MAP_FOLDL,
SUM_FOLDL,
FLAT_FOLDL,
LENGTH_FOLDL,
NULL_FOLDL,
FILTER_FOLDL,
REVERSE_FOLDL,
ALL_EL_FOLDL,
SOME_EL_FOLDL,
IS_EL_FOLDL,
SUFFIX_DEF,
AND_EL_FOLDL,
OR_EL_FOLDL,
FLAT_REVERSE_FOLDL
];

val foldr_thms = ref
[
APPEND_FOLDR,
MAP_FOLDR,
SUM_FOLDR,
FLAT_FOLDR,
LENGTH_FOLDR,
NULL_FOLDR,
FILTER_FOLDR,
REVERSE_FOLDR,
ALL_EL_FOLDR,
SOME_EL_FOLDR,
IS_EL_FOLDR,
PREFIX_FOLDR,
SNOC_FOLDR,
AND_EL_FOLDR,
OR_EL_FOLDR,
FLAT_REVERSE_FOLDR
];


val monoid_thms = ref
[
MONOID_CONJ_T,
MONOID_DISJ_F,
MONOID_APPEND_NIL,
MONOID_ADD_0 ,
MONOID_RAPPEND_NIL
];

val fcomm_thms = ref
[
FCOMM_APPEND_CONS,
FCOMM_SNOC_APPEND,
FCOMM_SUC_ADD,
FCOMM_ADD_SUC,
FCOMM_CONJ_PRED,
FCOMM_PRED_CONJ,
FCOMM_DISJ_PRED,
FCOMM_PRED_DISJ,
FCOMM_F_CONJ,
FCOMM_CONJ_F,
FCOMM_FILT_APPEND,
FCOMM_APPEND_FILT,
FCOMM_DISJ_T,
FCOMM_T_DISJ,
FCOMM_RAPPEND_SNOC,
FCOMM_CONS_RAPPEND
];

val comm_thms = ref
[
COMM_ADD,
COMM_CONJ,
COMM_DISJ,
COMM_CONST
];

val assoc_thms = ref
[
ASSOC_CONST
];

val left_id_thms = ref ([]:thm list);
val right_id_thms = ref ([]:thm list);


(*-------------------------------------------------------------------------*)

val PROVE_RIGHT_LIST_CONV =
       PROVE_LIST_CONV
          (false,
           "FOLDR",
           FOLDR,
           FOLDR_SNOC,
           (check_fcommr_th, get_fcomml_g,
            FOLDR_APPEND, MONOID_FOLDR_APPEND, ASSOC_FOLDR_APPEND,
            FCOMM_MONOID_FOLDR_APPEND, FCOMM_FOLDR_APPEND),
           (check_fcommr_th, get_fcomml_g,
            MONOID_FOLDR_FLAT,ASSOC_FOLDR_FLAT,
            FCOMM_MONOID_FOLDR_FLAT,FCOMM_FOLDR_FLAT),
           ((--`\(x:'a) (l:'b). h (g x:'c) l:'d`--),
            COMM_MONOID_FOLDR_REVERSE, COMM_ASSOC_FOLDR_REVERSE,
            COMM_MONOID_FOLDR_REVERSE2, COMM_ASSOC_FOLDR_REVERSE2));


val PROVE_LEFT_LIST_CONV =
       PROVE_LIST_CONV
          (true,
           "FOLDL",
           FOLDL,
           FOLDL_SNOC,
           (check_fcomml_th, get_fcommr_g,
            FOLDL_APPEND, MONOID_FOLDL_APPEND, ASSOC_FOLDL_APPEND,
            FCOMM_MONOID_FOLDL_APPEND, FCOMM_FOLDL_APPEND),
           (check_fcomml_th, get_fcommr_g,
            MONOID_FOLDL_FLAT,ASSOC_FOLDL_FLAT,
            FCOMM_MONOID_FOLDL_FLAT,FCOMM_FOLDL_FLAT),
           ((--`\(l:'a) (x:'b). h l (g x:'c):'d`--),
            COMM_MONOID_FOLDL_REVERSE, COMM_ASSOC_FOLDL_REVERSE,
            COMM_MONOID_FOLDL_REVERSE2, COMM_ASSOC_FOLDL_REVERSE2));



fun get_fold_def folddefs tm =
         let val op1 = get_operator tm;
             val folds = filter (is_X_def op1) folddefs;
         in
           hd folds
         end
   handle HOL_ERR _ =>
     raise HOL_ERR{message = "I do not know a suitable FOLD{R/L} definition \
                             \ or auxiliary theorem",
                        origin_function = "LIST_CONV: ",
                        origin_structure = ""};



fun X_LIST_CONV {Fold_thms = folddefs, Aux_thms = auxthms} tm =
   (let
        val user_foldr = filter (is_fold_def "FOLDR") folddefs;
        val user_monoid = filter_X_thm "MONOID" auxthms;
        val user_fcomm = filter_X_thm "FCOMM" auxthms;
        val user_comm =  filter_X_thm "COMM" auxthms;
        val user_assoc = filter_X_thm "ASSOC" auxthms;
        val user_left_id = filter_X_thm "LEFT_ID" auxthms;
    in
     let val all_foldr_defs =  user_foldr @ (!foldr_thms);
         val foldr = get_fold_def all_foldr_defs tm;
         val all_auxthms = 
          (user_monoid @ !monoid_thms, user_fcomm @ !fcomm_thms,
           user_comm @ !comm_thms, user_assoc @ !assoc_thms,
           user_left_id @ !left_id_thms);
     in
      PROVE_RIGHT_LIST_CONV all_foldr_defs all_auxthms foldr tm
     end
    handle HOL_ERR _ => 
    (let
        val user_foldl = filter (is_fold_def "FOLDL") folddefs;
        val user_right_id = filter_X_thm "RIGHT_ID" auxthms;

        val all_foldl_defs =  user_foldl @ (!foldl_thms);
        val foldl = get_fold_def all_foldl_defs tm;
        val all_auxthms = 
         (user_monoid @ !monoid_thms,  user_fcomm @ !fcomm_thms,
          user_comm @ !comm_thms,  user_assoc @ !assoc_thms,
          user_right_id @ !right_id_thms);
     in
      PROVE_LEFT_LIST_CONV all_foldl_defs all_auxthms foldl tm
     end)
    end);

val LIST_CONV = X_LIST_CONV {Fold_thms = [], Aux_thms = []};

(*---------------------------------------------------------------------------
 * PURE_LIST_CONV uses theorems supplied by a user to prove theorems about
 * lists.  The first argument is a list of definitions of constants in terms of
 * FOLDL or FOLDR. The second contains auxiliary information about the function
 * and unit in the fold definitions.
 *---------------------------------------------------------------------------*)


fun PURE_LIST_CONV {Fold_thms = folddefs, Aux_thms = auxthms} tm =
   (let val foldr = get_fold_def (filter (is_fold_def "FOLDR") folddefs) tm;
        val sorted_auxthms = 
              (filter_X_thm "MONOID" auxthms,
               filter_X_thm "FCOMM" auxthms,
               filter_X_thm "COMM" auxthms,
               filter_X_thm "ASSOC" auxthms,
               filter_X_thm "LEFT_ID" auxthms)
    in
     PROVE_RIGHT_LIST_CONV folddefs sorted_auxthms foldr tm
    end)
  handle HOL_ERR _ => 
   (let val foldl = get_fold_def (filter (is_fold_def "FOLDL") folddefs) tm;
        val sorted_auxthms = 
              (filter_X_thm "MONOID" auxthms,
               filter_X_thm "FCOMM" auxthms,
               filter_X_thm "COMM" auxthms,
               filter_X_thm "ASSOC" auxthms,
               filter_X_thm "RIGHT_ID" auxthms)
    in
       PROVE_LEFT_LIST_CONV folddefs sorted_auxthms foldl tm
    end)
   handle HOL_ERR{message = msg,
                        origin_function = func,
                        origin_structure = st} =>
     raise HOL_ERR{message = msg,
                        origin_function = "PURE_LIST_CONV: ",
                        origin_structure = st};

fun list_thm_database () =
    {Fold_thms = !foldr_thms @ !foldl_thms,
     Aux_thms = !monoid_thms @ !comm_thms @ !assoc_thms @
               !fcomm_thms @ !left_id_thms @ !right_id_thms
    };

fun set_list_thm_database {Fold_thms = fold_thms, Aux_thms = aux_thms} =
     (monoid_thms  := filter_X_thm "MONOID" aux_thms;
      fcomm_thms   := filter_X_thm "FCOMM" aux_thms;
      comm_thms    := filter_X_thm "COMM" aux_thms;
      assoc_thms   := filter_X_thm "ASSOC" aux_thms;
      left_id_thms := filter_X_thm "LEFT_ID" aux_thms;
      right_id_thms := filter_X_thm "RIGHT_ID" aux_thms;
      foldr_thms   := filter (is_fold_def "FOLDR") fold_thms;
      foldl_thms   := filter (is_fold_def "FOLDL") fold_thms
     );
 


end;  (* List_conv2 *)


(* Miscellaneous algebraic theorems of arithmetic - where should they go?
 *
 *val ASSOC_MULT = store_thm ("ASSOC_MULT",
 *    (--`ASSOC $*`--),
 *    REWRITE_TAC[ASSOC_DEF,MULT_ASSOC]);
 *
 *val RIGHT_ID_MULT_1 = store_thm ("RIGHT_ID_MULT_1",
 *    (--`RIGHT_ID $* 1`--),
 *    REWRITE_TAC[RIGHT_ID_DEF,MULT_CLAUSES]);
 *
 *val LEFT_ID_MULT_1 = store_thm ("LEFT_ID_MULT_1",
 *    (--`LEFT_ID $* 1`--),
 *    REWRITE_TAC[LEFT_ID_DEF,MULT_CLAUSES]);
 *
 *val MONOID_MULT_1 = store_thm ("MONOID_MULT_1",
 *    (--`MONOID $* 1`--),
 *    REWRITE_TAC[MONOID_DEF,ASSOC_MULT,LEFT_ID_MULT_1,RIGHT_ID_MULT_1]);
 **************************************************************************)


