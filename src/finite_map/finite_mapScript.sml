(* ====================================================================== *)
(* THEORY: finite_map						          *)
(* FILE:    finite_mapScript.sml					  *)
(* DESCRIPTION: A theory of finite maps					  *)
(*									  *) 
(* AUTHOR:  Graham Collins and Donald Syme				  *)
(*									  *) 
(* ====================================================================== *)
(* There is little documentation in this file but a discussion of this    *)
(* theory is available as:  						  *)
(*   									  *)
(* @inproceedings{P-Collins-FMAP,  					  *)
(*    author = {Graham Collins and Donald Syme},  			  *)
(*    editor = {E. Thomas Schubert and Phillip J. Windley   		  *)
(*              and Hames Alves-Foss},  				  *)
(*    booktitle={Higher Order Logic Theorem Proving and its Applications},*)
(*    publisher = {Springer-Verlag},  					  *)
(*    series = {Lecture Notes in Computer Science},  			  *)
(*    title = {A {T}heory of {F}inite {M}aps},  			  *)
(*    volume = {971},  							  *)
(*    year = {1995},  							  *)
(*    pages = {122--137}  						  *)
(* } 									  *)
(* 									  *)
(* Please email any comments to Graham Collins (grmc@dcs.gla.ac.uk)	  *)
(* =====================================================================  *)

structure finite_mapScript = 
struct

open HolKernel Parse basicHol90Lib 
     ind_defLib oneTheory sumTheory pairTheory numLib Num_induct;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;

(* Definition of a finite map *)

val _ = new_theory "finite_map";


(* The representation is the type 'a -> ('b + one) where only a finite
 number of the 'a map to a 'b and the rest map to one. *)


(* We define an notion of finiteness inductively. *)

val {rules=is_fmap_rules, induction=is_fmap_ind} =
 let val is_fmap = Term`is_fmap :('a -> 'b + one) -> bool`
     infix ----------------------------------------;
     fun (x ---------------------------------------- y) = (x,y)
  in
   indDefine "isfmap"

      [ ([],                                  [])
        ----------------------------------------
               `^is_fmap (\a. (INR one))`       ,

          
          ([`^is_fmap f`                   ],[])
        ----------------------------------------
        `^is_fmap (\x. (x = a) => INL b | f x)` ]  Prefix  (`^is_fmap f`,[])
   end;

val [is_fmap_empty, is_fmap_update] = is_fmap_rules;

val strong_is_fmap_ind = 
  ind_defLib.derive_strong_induction(is_fmap_rules, is_fmap_ind);

val is_fmap_RULE_INDUCT_TAC =
   ind_defLib.RULE_INDUCT_THEN is_fmap_ind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;


(* Existence Theorem *)

val EXISTENCE_THM = prove 
 (Term`?x:'a -> 'b + one. 
    (\f:'a -> 'b + one . is_fmap f) x `,
EXISTS_TAC (Term`\x:'a. (INR one):'b + one`) THEN
BETA_TAC THEN 
REWRITE_TAC [ is_fmap_empty ]);

val fmap_TY_DEF = 
    new_type_definition{name = "fmap",
                        pred =Term`\f:'a -> 'b + one . is_fmap f`,
                        inhab_thm = EXISTENCE_THM};

(* --------------------------------------------------------------------- *)
(* Define bijections  				 *)
(* --------------------------------------------------------------------- *)
val fmap_ISO_DEF =
    define_new_type_bijections {name  = "fmap_ISO_DEF",
				ABS = "fmap_ABS",
				REP = "fmap_REP",
				tyax = fmap_TY_DEF};

(* --------------------------------------------------------------------- *)
(* Prove that REP is one-to-one.					 *)
(* --------------------------------------------------------------------- *)
val fmap_REP_11 = prove_rep_fn_one_one fmap_ISO_DEF;

val fmap_REP_onto = prove_rep_fn_onto fmap_ISO_DEF;

val fmap_ABS_11 = prove_abs_fn_one_one fmap_ISO_DEF;

val fmap_ABS_onto = prove_abs_fn_onto fmap_ISO_DEF;

val (fmap_ABS_REP_THM,fmap_REP_ABS_THM)  = 
   let
       val thms = CONJUNCTS fmap_ISO_DEF;
       val [t1,t2] = map (GEN_ALL o SYM o SPEC_ALL) thms
   in
       (t1,t2)
   end;


(*CANCELLATION THEOREMS*)


val is_fmap_REP = prove (Term`!(f : ('a,'b) fmap). is_fmap (fmap_REP f)`,
REWRITE_TAC [BETA_RULE  fmap_REP_onto] THEN
GEN_TAC THEN
EXISTS_TAC (Term`f: ('a,'b) fmap`) THEN
REWRITE_TAC [fmap_REP_11]);

val REP_ABS_empty = prove (
Term`fmap_REP (fmap_ABS ((\a. INR one):'a -> 'b + one)) = (\a. INR one)`,
REWRITE_TAC [fmap_REP_ABS_THM] THEN
BETA_TAC THEN 
REWRITE_TAC [is_fmap_empty]);


val REP_ABS_update = prove (Term
 `!(f:('a,'b) fmap) x y. 
     fmap_REP (fmap_ABS (\a. (a = x) => INL y | fmap_REP f a))
      = 
     (\a. (a = x) => INL y | fmap_REP f a)`,
REPEAT GEN_TAC THEN
REWRITE_TAC [fmap_REP_ABS_THM] THEN
BETA_TAC THEN 
MATCH_MP_TAC  is_fmap_update THEN
REWRITE_TAC [is_fmap_REP]);

val is_fmap_REP_ABS = prove (Term
`!(f:'a -> 'b + one). is_fmap f ==> (fmap_REP (fmap_ABS f) = f)`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [fmap_REP_ABS_THM] THEN
BETA_TAC THEN
ASM_REWRITE_TAC []);



(*DEFINITIONS OF UPDATE, EMPTY, APPLY and DOMAIN*)

val FUPDATE_DEF = new_definition ("FUPDATE_DEF",
               Term`FUPDATE (f:('a,'b) fmap ) (x,y) 
                   = fmap_ABS (\a:'a. (a = x) => INL y | (fmap_REP f) a)`);

val FEMPTY_DEF = new_definition ("FEMPTY_DEF", 
               Term`FEMPTY :('a,'b) fmap  =
                   fmap_ABS (\a:'a. INR one)`);

val FAPPLY_DEF = new_definition ("FAPPLY_DEF", 
               Term`FAPPLY (f:('a,'b) fmap ) (x:'a) 
                      =  OUTL ((fmap_REP f) x)`);

val FDOM_DEF = new_definition ("FDOM_DEF", 
               Term`FDOM (f:('a,'b) fmap ) (x:'a) 
                      = ISL ((fmap_REP f) x)`);

val update_rep =Term`\(f:'a -> 'b + one) x y.
                           \a. 
                            (a = x) => INL y | f a`;

val empty_rep =Term`(\a. INR one):'a -> 'b + one`;



(* Now some theorems *)

val FAPPLY_FUPDATE = 
store_thm ("FAPPLY_FUPDATE",
Term`!(f:('a,'b) fmap) x y.
         FAPPLY (FUPDATE f (x,y)) x = y`,
REWRITE_TAC [FUPDATE_DEF, FAPPLY_DEF] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC [REP_ABS_update] THEN
BETA_TAC THEN
REWRITE_TAC [sumTheory.OUTL]);

val NOT_EQ_FAPPLY = 
store_thm ("NOT_EQ_FAPPLY",
Term`!(f:('a,'b) fmap) a x y . ~(a = x) ==> (FAPPLY (FUPDATE f (x,y)) a = FAPPLY f a)`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [FUPDATE_DEF, FAPPLY_DEF, REP_ABS_update] THEN
BETA_TAC THEN
ASM_REWRITE_TAC []);

val update_commutes_rep = (BETA_RULE o BETA_RULE) (prove (
Term`!(f:'a -> 'b + one) a b c d. 
   ~(a = c) ==> (^update_rep (^update_rep f a b) c d =
                    ^update_rep (^update_rep f c d) a b)`,
REPEAT STRIP_TAC THEN
BETA_TAC THEN 
MATCH_MP_TAC EQ_EXT THEN
GEN_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN BETA_TAC THEN
ASM_REWRITE_TAC []));


val FUPDATE_COMMUTES = store_thm ("FUPDATE_COMMUTES",
Term`!(f:('a,'b) fmap) a b c d. 
   ~(a = c) ==> (FUPDATE (FUPDATE f (a,b)) (c,d) =
                    FUPDATE (FUPDATE f (c,d)) (a,b))`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [FUPDATE_DEF, REP_ABS_update] THEN
BETA_TAC THEN 
AP_TERM_TAC THEN
MATCH_MP_TAC EQ_EXT THEN
GEN_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN BETA_TAC THEN
ASM_REWRITE_TAC []);

val update_same_rep = (BETA_RULE o BETA_RULE) (prove (
Term`!(f:'a -> 'b+one) a b c.
    ^update_rep (^update_rep f a b) a c = ^update_rep f a c`,
BETA_TAC THEN
REPEAT GEN_TAC THEN
MATCH_MP_TAC EQ_EXT THEN
GEN_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN BETA_TAC THEN
ASM_REWRITE_TAC []));

val FUPDATE_EQ =store_thm ("FUPDATE_EQ",
Term`!(f:('a,'b) fmap) a b c. 
     FUPDATE (FUPDATE f (a,b)) (a,c) =
                    FUPDATE f (a,c)`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [FUPDATE_DEF, REP_ABS_update] THEN
BETA_TAC THEN
AP_TERM_TAC THEN
MATCH_MP_TAC EQ_EXT THEN
GEN_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN BETA_TAC THEN
ASM_REWRITE_TAC []);

val lemma1 = prove (
Term`~((ISL :'b + one -> bool) ((INR :one -> 'b + one) (one :one)))`,
REWRITE_TAC [sumTheory.ISL]);

val FDOM_FEMPTY = 
store_thm ("FDOM_FEMPTY",
Term`!a. FDOM (FEMPTY:('a,'b) fmap) a = F`,
GEN_TAC THEN
REWRITE_TAC [FDOM_DEF, FEMPTY_DEF, REP_ABS_empty,
             sumTheory.ISL]);

val dom_update_rep = BETA_RULE (prove(
Term`!f a b x. ISL (^update_rep (f:'a -> 'b+one ) a b x) = ((x = a) 
    \/  ISL (f x))`,
REPEAT GEN_TAC THEN 
BETA_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN
ASM_REWRITE_TAC [sumTheory.ISL]));


val FDOM_FUPDATE = 
store_thm("FDOM_FUPDATE",
Term`!f a b x. FDOM (FUPDATE (f:('a,'b) fmap ) (a,b)) x = ((x = a) 
    \/  FDOM f x)`,
REPEAT GEN_TAC THEN
REWRITE_TAC [FDOM_DEF,FUPDATE_DEF, REP_ABS_update] THEN
BETA_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = a`) THEN
ASM_REWRITE_TAC [sumTheory.ISL]);

val FAPPLY_FUPDATE_THM = store_thm("FAPPLY_FUPDATE_THM",
Term`!(f:('a,'b) fmap)  a b x.FAPPLY(FUPDATE f (a,b)) x = ((x=a) => b | FAPPLY f x)`,
REPEAT STRIP_TAC THEN 
COND_CASES_TAC THEN
ASM_REWRITE_TAC [FAPPLY_FUPDATE] THEN
IMP_RES_TAC NOT_EQ_FAPPLY THEN
ASM_REWRITE_TAC []);


val not_eq_empty_update_rep = BETA_RULE (prove (
Term`!(f:'a -> 'b + one) a b. 
   ~(^empty_rep = ^update_rep f a b)`,
REPEAT GEN_TAC THEN 
BETA_TAC THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
CONV_TAC  NOT_FORALL_CONV THEN
EXISTS_TAC (Term`a:'a`) THEN
BETA_TAC THEN
DISCH_THEN (fn th => REWRITE_TAC 
       [REWRITE_RULE [sumTheory.ISL]
               (REWRITE_RULE [th] lemma1)])));


val fmap_EQ_1 = prove (
Term`!(f:('a,'b) fmap) g.
    (f = g) ==> (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g)`,
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val NOT_EQ_FEMPTY_FUPDATE = 
store_thm ("NOT_EQ_FEMPTY_FUPDATE",
Term`!(f:('a,'b) fmap) a b. 
   ~(FEMPTY = FUPDATE f (a,b))`,
REPEAT STRIP_TAC THEN
IMP_RES_TAC fmap_EQ_1 THEN
UNDISCH_TAC (Term`FDOM (FEMPTY:('a,'b)fmap) = 
          FDOM (FUPDATE (f:('a,'b)fmap) (a,b))`) THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [] THEN
CONV_TAC  NOT_FORALL_CONV THEN
EXISTS_TAC (Term`a:'a`) THEN
REWRITE_TAC [FDOM_FEMPTY, FDOM_FUPDATE]);

val FDOM_EQ_FDOM_FUPDATE = store_thm("FDOM_EQ_FDOM_FUPDATE",
Term`!(f:('a,'b) fmap) x. FDOM f x ==> (!y. FDOM (FUPDATE f (x,y)) = FDOM f)`,
REPEAT STRIP_TAC THEN 
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
GEN_TAC THEN ASM_CASES_TAC (Term`(x':'a)=x`) THEN
ASM_REWRITE_TAC [FDOM_FUPDATE]);


(*A small lemma*)
val lemma2 = prove (
Term`!x y z. (x ==> (y /\ z)) ==> (x ==> y)`,
REPEAT STRIP_TAC THEN RES_TAC);


(*SIMPLE INDUCTION*)

val fmap_SIMPLE_INDUCT = store_thm ("fmap_SIMPLE_INDUCT",
Term`!P. P FEMPTY /\
       (!f. P f ==> (!x y.  P(FUPDATE f (x,y)))) ==>
       !f:('a,'b) fmap. P f`,
REWRITE_TAC [FUPDATE_DEF, FEMPTY_DEF] THEN
GEN_TAC THEN STRIP_TAC THEN
GEN_TAC THEN
CHOOSE_TAC (SPEC (Term`f:('a,'b)fmap`) fmap_ABS_onto) THEN
ASM_REWRITE_TAC [] THEN
ASSUM_LIST (fn ths => ASSUME_TAC (CONJUNCT2 (BETA_RULE (el 1 ths)))) THEN
UNDISCH_TAC  (Term`is_fmap (r:'a -> 'b + one)`) THEN
SPEC_TAC (Term`r:'a -> 'b + one`,Term`r:'a -> 'b + one`) THEN
ind_defLib.RULE_INDUCT_THEN strong_is_fmap_ind ASSUME_TAC ASSUME_TAC THENL
[
 ASM_REWRITE_TAC[],
 IMP_RES_TAC is_fmap_REP_ABS THEN
 RES_TAC THEN
 ASSUM_LIST (fn ths => REWRITE_TAC [REWRITE_RULE [el 3 ths] (el 2 ths)])
]
);

val FUPDATE_ABSORB_THM = prove (
Term`!(f:('a,'b) fmap) x y. (FDOM f x)  /\ (FAPPLY f x = y) ==> (FUPDATE f (x,y) = f)`,

INDUCT_THEN  fmap_SIMPLE_INDUCT STRIP_ASSUME_TAC THEN
REWRITE_TAC [FDOM_FEMPTY] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = x'`) THENL
[  ASM_REWRITE_TAC [FUPDATE_EQ] THEN
   ASM_CASES_TAC (Term`(y:'b) = y'`) THEN
   ASM_REWRITE_TAC [] THEN
   ASSUM_LIST 
   (fn ths => ASSUME_TAC (
     REWRITE_RULE [el 2 ths, FAPPLY_FUPDATE, el 1 ths] (el 3 ths))) THEN
   UNDISCH_TAC (Term`F`) THEN
   REWRITE_TAC [],
   IMP_RES_TAC FUPDATE_COMMUTES THEN
   ASM_REWRITE_TAC [] THEN
   ASSUM_LIST (fn ths => ASSUME_TAC (
     REWRITE_RULE [
       MATCH_MP NOT_EQ_FAPPLY (NOT_EQ_SYM (el 2 ths))]
        (el 3 ths))) THEN
   ASSUM_LIST (fn ths => ASSUME_TAC (
     REWRITE_RULE [FDOM_FUPDATE, (NOT_EQ_SYM (el 3 ths))]
        (el 5 ths))) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []
]
);

val FDOM_FAPPLY = prove(
Term`!(f:('a,'b) fmap) x. FDOM f x ==> ?y. FAPPLY f x = y`,
INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
[REWRITE_TAC [FDOM_FEMPTY],
 REWRITE_TAC [FDOM_FUPDATE] THEN
 REPEAT GEN_TAC THEN
 ASM_CASES_TAC (Term`(x':'a)=x`) THEN
 ASM_REWRITE_TAC [] THENL 
 [
  EXISTS_TAC (Term`y:'b`) THEN
  REWRITE_TAC [FAPPLY_FUPDATE],
  IMP_RES_TAC NOT_EQ_FAPPLY THEN
  DISCH_TAC THEN RES_TAC THEN
  EXISTS_TAC (Term`y':'b`) THEN
  ASM_REWRITE_TAC []
 ]
]);

val FDOM_FUPDATE_ABSORB = prove (
Term`!(f:('a,'b) fmap) x. (FDOM f x)  ==> (?y. FUPDATE f (x,y) = f)`,
REPEAT STRIP_TAC THEN
IMP_RES_TAC FDOM_FAPPLY THEN
EXISTS_TAC (Term`y:'b`) THEN
MATCH_MP_TAC FUPDATE_ABSORB_THM THEN
ASM_REWRITE_TAC []
);

val FDOM_F_FEMPTY = 
store_thm ("FDOM_F_FEMPTY1",
Term`!f. (!a. ~(FDOM (f:('a,'b) fmap) a)) = (f = FEMPTY)`,
INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
[REWRITE_TAC [FDOM_FEMPTY],
 GEN_TAC THEN GEN_TAC THEN
 REWRITE_TAC [NOT_EQ_SYM (SPECL [Term`f:('a,'b)fmap`,Term`x:'a`,Term`y:'b`] NOT_EQ_FEMPTY_FUPDATE)] THEN
 CONV_TAC NOT_FORALL_CONV THEN
 EXISTS_TAC (Term`x:'a`) THEN
 REWRITE_TAC [FDOM_FUPDATE]
]);

(* ===================================================================== *)
(* Cardinality                                                           *)
(* ===================================================================== *)
(*
Define cardinality by copying the prrofs in the sets library. To simplfy
this we define cardinality as a function over the domain FDOM f 
of the finite map. We need to define deletion from the domain. *)

val FDOMDEL_DEF = new_definition ("FDOMDEL_DEF",
Term`FDOMDEL (d:'a->bool) x a = d a /\ (~(a = x))`);


val FDOMDEL_COMM = prove (
Term`!(s:'a->bool) x y. FDOMDEL (FDOMDEL s x) y = FDOMDEL (FDOMDEL s y) x`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [FDOMDEL_DEF] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []);

val FDOM_FDOM_DEL = prove (
Term`!(f:('a,'b)fmap) x.
     ~(FDOM f x) ==> (!y. (FDOMDEL (FDOM (FUPDATE f (x,y))) x) = FDOM f)`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [FDOMDEL_DEF, FDOM_FUPDATE] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x':'a)=x`) THEN
ASM_REWRITE_TAC []);

val FDOMDEL_FEMPTY = prove(
Term`!x. FDOMDEL (FDOM (FEMPTY:('a,'b)fmap)) x = (FDOM (FEMPTY:('a,'b)fmap))`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [FDOMDEL_DEF, FDOM_FEMPTY]);

(* --------------------------------------------------------------------- *)
(* card_rel_def: defining equations for a relation `R s n`, which means  *)
(* that the finite s has cardinality n.                                  *)
(* --------------------------------------------------------------------- *)

val card_rel_def = 
Term`(!s. R s 0 = (s = (FDOM (FEMPTY:('a,'b)fmap)))) /\
    (!s n. R s (SUC n) = ?x:'a. (s x) /\ R (FDOMDEL s x) n)`;

(* --------------------------------------------------------------------- *)
(* Prove that such a relation exists.                                    *)
(* --------------------------------------------------------------------- *)


val CARD_REL_EXISTS = 
    prove_rec_fn_exists (prim_recTheory.num_Axiom) card_rel_def ;


val CARD_REL_DEL_LEMMA = TAC_PROOF((strip_conj card_rel_def,
Term`!(n:num) (s:'a -> bool) (x:'a). 
    s x ==> 
    R (FDOMDEL s x) n  ==> 
    (!y:'a. s y ==> R (FDOMDEL s y) n)`),
   Num_induct.INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN 
    ASM_REWRITE_TAC [] THEN 
    CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN 
    ASM_REWRITE_TAC [FDOMDEL_DEF, FDOM_FEMPTY] THEN
    STRIP_TAC THEN GEN_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o 
        REWRITE_RULE [DE_MORGAN_THM] o (SPEC (Term`y:'a`))) THEN
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    let val th = (SPEC (Term`y:'a = x'`) EXCLUDED_MIDDLE) 
    in
    DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th 
    end THENL
    [
     CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
     PURE_ONCE_REWRITE_TAC [FDOMDEL_COMM] THEN
     EXISTS_TAC (Term`x:'a`) THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC (Term`FDOMDEL (s:'a->bool)  x x'`) THEN
     ASM_REWRITE_TAC [FDOMDEL_DEF] THEN
     DISCH_THEN(fn th => REWRITE_TAC [NOT_EQ_SYM th]),
   
     let val th = (SPEC (Term`x:'a = y`) EXCLUDED_MIDDLE) 
     in
     DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th 
     end THENL
     [EXISTS_TAC (Term`x':'a`) THEN ASM_REWRITE_TAC [],
      EXISTS_TAC (Term`x:'a`) THEN ASM_REWRITE_TAC [FDOMDEL_DEF] THEN
      RES_THEN (TRY o IMP_RES_THEN ASSUME_TAC) THEN
      PURE_ONCE_REWRITE_TAC [FDOMDEL_COMM] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [FDOMDEL_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN FIRST_ASSUM ACCEPT_TAC]]]);



(* --------------------------------------------------------------------- *)
(* So `R s` specifies a unique number.                                   *)
(* --------------------------------------------------------------------- *)

val CARD_REL_UNIQUE = TAC_PROOF((strip_conj card_rel_def,
Term`!n:num. !s:'a->bool. R s n ==> (!m. R s m ==> (n = m))`),
   Num_induct.INDUCT_TAC THEN ASM_REWRITE_TAC [] THENL
   [GEN_TAC THEN STRIP_TAC THEN Num_induct.INDUCT_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THENL
    [STRIP_TAC THEN REFL_TAC, 
     ASM_REWRITE_TAC[numTheory.NOT_SUC,FDOM_FEMPTY]],
    GEN_TAC THEN STRIP_TAC THEN Num_induct.INDUCT_TAC THENL
    [ASM_REWRITE_TAC [numTheory.NOT_SUC] THEN
      CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
      CONV_TAC NOT_FORALL_CONV THEN
      EXISTS_TAC (Term`x:'a`) THEN
      ASM_REWRITE_TAC [FDOM_FEMPTY],
      ASM_REWRITE_TAC [prim_recTheory.INV_SUC_EQ] THEN STRIP_TAC THEN 
      IMP_RES_TAC CARD_REL_DEL_LEMMA THEN RES_TAC]]);


(* --------------------------------------------------------------------- *)
(* Now, ?n. R s n if s is finite.                                        *)
(* --------------------------------------------------------------------- *)

val CARD_REL_EXISTS_LEMMA = TAC_PROOF((strip_conj card_rel_def,
Term`!f:('a,'b)fmap. ?n:num. R (FDOM f) n`),
  INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
  [EXISTS_TAC (Term`0`) THEN ASM_REWRITE_TAC[],
   FIRST_ASSUM (fn th => fn g => CHOOSE_THEN ASSUME_TAC th g) THEN
   GEN_TAC THEN GEN_TAC THEN
   ASM_CASES_TAC (Term`FDOM (f:('a,'b)fmap) x`) THENL
   [
    IMP_RES_TAC FDOM_EQ_FDOM_FUPDATE THEN
    EXISTS_TAC (Term`n:num`) THEN ASM_REWRITE_TAC [],
    IMP_RES_TAC FDOM_FDOM_DEL THEN
    EXISTS_TAC (Term`SUC n`) THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (Term`x:'a`) THEN 
    ASM_REWRITE_TAC [FDOM_FUPDATE] ]]);     


(* --------------------------------------------------------------------- *)
(* So (@n. R s n) = m iff R s m        (\s.@n.R s n defines a function) *)
(* Proof modified for Version 12 IMP_RES_THEN            [TFM 91.01.23] *)
(* --------------------------------------------------------------------- *)

val CARD_REL_THM = 
    TAC_PROOF
    ((Dsyntax.strip_conj card_rel_def, 
     (Term`!m (f:('a,'b)fmap). (((@n:num. R (FDOM f) n) = m) = R (FDOM f) m)`)),
     REPEAT STRIP_TAC THEN 
     STRIP_ASSUME_TAC (SPEC (Term`f:('a,'b)fmap`) CARD_REL_EXISTS_LEMMA) THEN 
     EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
      EXISTS_TAC (Term`n:num`) THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
      STRIP_TAC THEN
      IMP_RES_THEN ASSUME_TAC CARD_REL_UNIQUE THEN
      CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      CONV_TAC SELECT_CONV THEN
      EXISTS_TAC (Term`n:num`) THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);


(* --------------------------------------------------------------------- *)
(* Now, prove the existence of the required cardinality function.       *)
(* --------------------------------------------------------------------- *)

val DOM_CARD_EXISTS = TAC_PROOF(([],
(Term`?CARD.
       (CARD (FDOM (FEMPTY:('a,'b)fmap)) = 0) /\ 
       (!(f:('a,'b)fmap) x y. 
           CARD(FDOM (FUPDATE f (x,y))) = (FDOM f x => CARD (FDOM f) | 
                                                    SUC(CARD (FDOM f))))`)),
     STRIP_ASSUME_TAC CARD_REL_EXISTS THEN
     EXISTS_TAC (Term`\s:'a->bool. @n:num. R s n`) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [CARD_REL_THM],
      REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_TAC FDOM_EQ_FDOM_FUPDATE THEN ASM_REWRITE_TAC [],
       ASM_REWRITE_TAC [CARD_REL_THM] THEN
       EXISTS_TAC (Term`x:'a`) THEN
       IMP_RES_TAC FDOM_FDOM_DEL THEN 
       ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
       CONV_TAC SELECT_CONV THEN
       REWRITE_TAC [CARD_REL_EXISTS_LEMMA]
      ]]);


(* --------------------------------------------------------------------- *)
(* Finally lets make this a function over finite maps rather than domains*)
(* --------------------------------------------------------------------- *)

val CARD_EXISTS = TAC_PROOF(([],
(Term`?CARD.
       (CARD (FEMPTY:('a,'b)fmap) = 0) /\ 
       (!(f:('a,'b)fmap) x y. 
           CARD(FUPDATE f (x,y)) = (FDOM f x => CARD f | 
                                                    SUC(CARD f)))`)),
STRIP_ASSUME_TAC DOM_CARD_EXISTS THEN
EXISTS_TAC (Term`\(x:('a,'b)fmap). (CARD:('a -> bool) -> num)  (FDOM x)`) THEN
BETA_TAC THEN
ASM_REWRITE_TAC []);


(* --------------------------------------------------------------------- *)
(* Finally, introduce the CARD function via a constant specification.   *)
(* --------------------------------------------------------------------- *)

val FCARD_DEF = new_specification 
                 {name="FCARD_DEF", sat_thm=CARD_EXISTS,
                  consts=[{const_name="FCARD",fixity=Prefix}]};

(* --------------------------------------------------------------------- *)
(* Various cardinality results.                                         *)
(* --------------------------------------------------------------------- *)

val FCARD_FEMPTY = save_thm("FCARD_FEMPTY",CONJUNCT1 FCARD_DEF);

val FCARD_FUPDATE = save_thm("FCARD_FUPDATE",CONJUNCT2 FCARD_DEF);

val FCARD_0_FEMPTY_LEMMA = prove(
Term`!f: ('a,'b) fmap. (FCARD f = 0) ==> (f = FEMPTY)`,
INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
[
 REWRITE_TAC [FCARD_FEMPTY],
 GEN_TAC THEN GEN_TAC THEN 
 REWRITE_TAC [FCARD_FUPDATE] THEN
 ASM_CASES_TAC (Term`FDOM (f:('a,'b) fmap) x`) THEN
 ASM_REWRITE_TAC [] THENL
 [ DISCH_THEN (fn th =>
    FIRST_ASSUM (fn ass => SUBST_ALL_TAC (MATCH_MP ass th))) THEN
   POP_ASSUM (CHECK_ASSUME_TAC o (REWRITE_RULE [FDOM_FEMPTY])),
   REWRITE_TAC [numTheory.NOT_SUC]
 ]
]);

val FCARD_0_FEMPTY = store_thm("FCARD_0_FEMPTY",
Term`!f: ('a,'b) fmap. (FCARD f = 0) = (f = FEMPTY)`,
GEN_TAC THEN EQ_TAC THENL
[
 REWRITE_TAC [FCARD_0_FEMPTY_LEMMA],
 DISCH_THEN (fn th => ASM_REWRITE_TAC [th, FCARD_FEMPTY])
]);



(*-----------------------------------------------------

-----------------------------------------------------*)




val exist_map_no_x_rep = (BETA_RULE o BETA_RULE) (prove
(Term`!(f:'a->'b+one). is_fmap f ==>
(!x. ?f'. !y.
(is_fmap f') /\
(^update_rep f x y  = ^update_rep f' x y) /\
(!x'. (f' x' =  ((x' = x) => INR one | f x'))) /\
(FDOM (fmap_ABS f') = (FDOMDEL (FDOM (fmap_ABS f)) x)))`,
BETA_TAC THEN
ind_defLib.RULE_INDUCT_THEN strong_is_fmap_ind ASSUME_TAC ASSUME_TAC THENL
[
 GEN_TAC THEN
 EXISTS_TAC (Term`^empty_rep :'a->'b+one`) THEN
 STRIP_TAC THEN 
 REWRITE_TAC [SYM (FEMPTY_DEF), FDOM_FEMPTY, FDOMDEL_FEMPTY, is_fmap_empty] THEN
 GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []
 ,
 REPEAT GEN_TAC THEN BETA_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (Term`x:'a`)) THEN
 ASM_CASES_TAC (Term`(a:'a) = x`) THENL
 [
  EXISTS_TAC (Term`f':'a -> 'b + one`) THEN
  GEN_TAC THEN
  IMP_RES_TAC is_fmap_REP_ABS THEN
   CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
  REWRITE_TAC [FDOMDEL_DEF] THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [FDOMDEL_DEF] THEN
 
  POP_ASSUM (fn thm => REWRITE_TAC [REWRITE_RULE [thm, FUPDATE_DEF]
        (SPEC (Term`fmap_ABS (f:'a -> 'b + one)`) FDOM_FUPDATE)]) THEN
  ASM_REWRITE_TAC [update_same_rep]  THEN
  STRIP_TAC THENL
  [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [],
   GEN_TAC THEN ASM_CASES_TAC (Term`(x':'a) = x`) THEN
   ASM_REWRITE_TAC []]
  ,
  EXISTS_TAC (Term`^update_rep (f':'a -> 'b + one) a b`) THEN
  BETA_TAC THEN GEN_TAC THEN
  IMP_RES_TAC  update_commutes_rep THEN
  POP_ASSUM (fn thm => REWRITE_TAC [thm]) THEN
  REPEAT STRIP_TAC THENL
  [
   MATCH_MP_TAC is_fmap_update THEN ASM_REWRITE_TAC [],
   MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN BETA_TAC THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
   COND_CASES_TAC THEN REWRITE_TAC [],
   ASM_CASES_TAC (Term`(x':'a) = a`) THEN ASM_REWRITE_TAC [],
   CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
   ASSUM_LIST (fn ths => 
    REWRITE_TAC [REWRITE_RULE [
     MATCH_MP is_fmap_REP_ABS
     (CONJUNCT1 (SPEC (Term`y:'b`) (el 2 ths))),  FUPDATE_DEF]
        (SPEC (Term`fmap_ABS (f':'a -> 'b + one)`) FDOM_FUPDATE)]) THEN
   ASM_REWRITE_TAC [FDOMDEL_DEF] THEN 
   IMP_RES_TAC is_fmap_REP_ABS THEN
   POP_ASSUM (fn thm => REWRITE_TAC [REWRITE_RULE [thm, FUPDATE_DEF]
        (SPEC (Term`fmap_ABS (f:'a -> 'b + one)`) FDOM_FUPDATE)]) THEN
   GEN_TAC THEN 
   ASM_CASES_TAC (Term`(x':'a) = a`) THEN
   ASM_REWRITE_TAC []
  ]]
 ]
));



val conj_context_lemma = prove (
Term`!p q r. (p /\ r /\ (p ==> r ==> q)) ==> (p /\ q /\ r)`,
REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);

val lemma2 = prove (Term`!(x:('a,'b) fmap) y. (x = y) ==> (FCARD x = FCARD y)`,
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val CARD_DOM_SUC = prove
(Term`!n (f:('a,'b) fmap). (FCARD  f = SUC n) ==> 
   ?f' x y. (~FDOM f' x) /\ 
             (FCARD  f' = n) /\
             (f = FUPDATE f' (x,y)) `,
GEN_TAC THEN 
INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
[
 REWRITE_TAC [FCARD_FEMPTY, 
              NOT_EQ_SYM (SPEC (Term`n:num`) (numTheory.NOT_SUC)) ],
 REPEAT GEN_TAC THEN
 REWRITE_TAC [FCARD_FUPDATE] THEN
 COND_CASES_TAC THENL
[
 DISCH_TAC THEN
 STRIP_ASSUME_TAC 
  (REWRITE_RULE [fmap_ISO_DEF]
   (SPEC (Term`x:'a`)
     (MATCH_MP exist_map_no_x_rep 
        (SPEC (Term`f:('a,'b) fmap`) is_fmap_REP)))) THEN
 POP_ASSUM (STRIP_ASSUME_TAC o SPEC (Term`y:'b`)) THEN
 EXISTS_TAC (Term`(fmap_ABS f'):('a,'b) fmap`) THEN
 EXISTS_TAC (Term`x:'a`) THEN
 EXISTS_TAC (Term`y:'b`) THEN
 IMP_RES_TAC is_fmap_REP_ABS THEN 
 MATCH_MP_TAC conj_context_lemma THEN
 REPEAT CONJ_TAC THENL
 [ ASM_REWRITE_TAC [FDOM_DEF, sumTheory.ISL],
   ASM_REWRITE_TAC [FUPDATE_DEF],
   DISCH_TAC THEN 
   ASSUM_LIST (fn ass =>
   DISCH_THEN (fn th => 
   ASSUME_TAC (SYM
        (REWRITE_RULE (FCARD_FUPDATE::prim_recTheory.INV_SUC_EQ::ass) 
                      (MATCH_MP lemma2 th))))) THEN
 ASM_REWRITE_TAC []]
,
 DISCH_THEN (ASSUME_TAC o REWRITE_RULE [prim_recTheory.INV_SUC_EQ]) THEN
  EXISTS_TAC (Term`f:('a,'b) fmap`) THEN
 EXISTS_TAC (Term`x:'a`) THEN
 EXISTS_TAC (Term`y:'b`) THEN
 ASM_REWRITE_TAC [] 
]])
   ;



val card_induct =
let 
val thm1 =
   BETA_RULE (SPEC (Term`\i. (!f: ('a,'b) fmap. 
                     (FCARD f = i) ==> P f)`)  
                    (numTheory.INDUCTION));
val thm2 = 
          GEN_ALL
           (DISCH_ALL
            (GEN (Term`f1: ('a,'b) fmap`)
             (REWRITE_RULE []
              (SPECL [Term`FCARD (f1: ('a,'b) fmap)`,
                     Term`f1: ('a,'b) fmap`] (
               UNDISCH_ALL thm1)))))
in
 prove (
Term`!P.
     (P FEMPTY) /\
     (!n.
       (!f:('a,'b) fmap. (FCARD f = n) ==> P f) ==>
       (!f:('a,'b) fmap. (FCARD f = SUC n) ==> P f)) ==>
     (!f:('a,'b) fmap. P f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC thm2 THEN
  CONJ_TAC THENL
  [
   REWRITE_TAC [FCARD_0_FEMPTY] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [],
   ASM_REWRITE_TAC []
  ])
end;


val fmap_INDUCT = store_thm("fmap_INDUCT", 
Term`!P. P FEMPTY /\
       (!f. P f ==> (!x y.  (~FDOM f x) ==> P(FUPDATE f (x,y)))) ==>
       !f:('a,'b) fmap. P f`,
GEN_TAC  THEN STRIP_TAC THEN
MATCH_MP_TAC card_induct THEN
ASM_REWRITE_TAC [] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC  CARD_DOM_SUC THEN
RES_TAC THEN RES_TAC THEN
ASM_REWRITE_TAC []);


(*EQUALITY*)

(*We now need to prove a lemma *)

val FUPDATE_ABSORB_THM = prove (Term
`!(f:('a,'b) fmap) x y. 
   (FDOM f x)  /\ (FAPPLY f x = y) ==> (FUPDATE f (x,y) = f)`,

INDUCT_THEN  fmap_SIMPLE_INDUCT STRIP_ASSUME_TAC THEN
REWRITE_TAC [FDOM_FEMPTY] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x:'a) = x'`) THENL
[  ASM_REWRITE_TAC [FUPDATE_EQ] THEN
   ASM_CASES_TAC (Term`(y:'b) = y'`) THEN
   ASM_REWRITE_TAC [] THEN
   ASSUM_LIST 
   (fn ths => ASSUME_TAC (
     REWRITE_RULE [el 2 ths, FAPPLY_FUPDATE, el 1 ths] (el 3 ths))) THEN
   UNDISCH_TAC (Term`F`) THEN
   REWRITE_TAC [],
   IMP_RES_TAC FUPDATE_COMMUTES THEN
   ASM_REWRITE_TAC [] THEN
   ASSUM_LIST (fn ths => ASSUME_TAC (
     REWRITE_RULE [
       MATCH_MP NOT_EQ_FAPPLY (NOT_EQ_SYM (el 2 ths))]
        (el 3 ths))) THEN
   ASSUM_LIST (fn ths => ASSUME_TAC (
     REWRITE_RULE [FDOM_FUPDATE, (NOT_EQ_SYM (el 3 ths))]
        (el 5 ths))) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []
]
);


val update_eq_not_x = 
     prove (Term`!(f:('a,'b) fmap). 
(!x. ?f'.  !y.
(FUPDATE f (x,y)  = FUPDATE f' (x,y)) /\
(~FDOM f' x))`,
INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
[
 GEN_TAC THEN EXISTS_TAC (Term`FEMPTY : ('a,'b) fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY],
 GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
 POP_ASSUM (STRIP_ASSUME_TAC o (SPEC (Term`x':'a`))) THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THENL
 [ 
  EXISTS_TAC (Term`f':('a,'b) fmap`) THEN
  ASM_REWRITE_TAC [FUPDATE_EQ] THEN
  POP_ASSUM (fn th => ASM_REWRITE_TAC [SYM th]),
  EXISTS_TAC (Term`FUPDATE (f':('a,'b) fmap) (x,y)`) THEN 
  IMP_RES_TAC  FUPDATE_COMMUTES THEN
  POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [EQ_SYM_EQ])) THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE]
 ]
]);


val lemma9 = BETA_RULE (prove (
Term`!x y (f1:('a,'b)fmap) f2. (f1 = f2) ==>  
    (( \ (f:('a,'b)fmap).FUPDATE f (x,y)) f1 
          = ( \( f:('a,'b)fmap).FUPDATE f (x,y)) f2)`,
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN
ASM_REWRITE_TAC []));

val NOT_FDOM_FAPPLY_FEMPTY = store_thm ("NOT_FDOM_FAPPLY_FEMPTY",
Term`!(f:('a,'b)fmap) x. (~FDOM f x) ==> 
          (FAPPLY f x = FAPPLY FEMPTY x)`,
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[REWRITE_TAC [],
 REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC  THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THENL
 [ASM_REWRITE_TAC [FDOM_FUPDATE],
 IMP_RES_TAC NOT_EQ_FAPPLY THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE]
 ]
]);



val fmap_EQ_2 = prove (
Term`!(f:('a,'b) fmap) g.
    (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) ==> (f = g)`,
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[
 GEN_TAC THEN 
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
 PURE_REWRITE_TAC [FDOM_FEMPTY] THEN 
 PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ, FDOM_F_FEMPTY] THEN
 REWRITE_TAC [FDOM_F_FEMPTY] THEN
 STRIP_TAC THEN ASM_REWRITE_TAC [],

  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   STRIP_ASSUME_TAC (SPECL [Term`g:('a,'b)fmap`,Term`x:'a`] update_eq_not_x) THEN
   POP_ASSUM (ASSUME_TAC o (SPEC (Term`FAPPLY (g:('a,'b)fmap) x`))) THEN
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN 
   STRIP_TAC THEN
   ASSUM_LIST (fn ths => ASSUME_TAC 
        (REWRITE_RULE [FDOM_FUPDATE] (SPEC (Term`x:'a`) (el 2 ths)))) THEN
   ASSUM_LIST (fn ths => ONCE_REWRITE_TAC [SYM
        (REWRITE_RULE [el 1 ths]
           (SPECL [Term`g:('a,'b)fmap`,Term`x:'a`,
                  Term`FAPPLY (g:('a,'b)fmap) x`] 
                               FUPDATE_ABSORB_THM))]) THEN
   ASM_REWRITE_TAC [] THEN
   ASSUM_LIST (fn ths => REWRITE_TAC [
                   ONCE_REWRITE_RULE [EQ_SYM_EQ] (el 2 ths)]) THEN
   REWRITE_TAC [FAPPLY_FUPDATE] THEN
   MATCH_MP_TAC lemma9 THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  CONJ_TAC THENL
  [ 
    ASSUM_LIST (fn ths => ASSUME_TAC
     (CONV_RULE (DEPTH_CONV FUN_EQ_CONV)
      (SYM (CONJUNCT1 (MATCH_MP fmap_EQ_1 (CONJUNCT1 (el 4 ths))))))) THEN
    GEN_TAC THEN
    ASM_CASES_TAC (Term`(x':'a) = x`) THENL
    [ASM_REWRITE_TAC [],
     ASSUM_LIST (fn ths => REWRITE_TAC
          [REWRITE_RULE [FDOM_FUPDATE, el 1 ths ]
                         (SPEC (Term`x':'a`) (el 2 ths))]) THEN 
     ASSUM_LIST (fn ths => REWRITE_TAC
          [REWRITE_RULE [FDOM_FUPDATE, el 1 ths ]
                         (SPEC (Term`x':'a`) (el 5 ths))])
    ] ,

    ASSUM_LIST (fn ths => ASSUME_TAC
     (CONV_RULE (DEPTH_CONV FUN_EQ_CONV)
      (SYM (CONJUNCT2 (MATCH_MP fmap_EQ_1 (CONJUNCT1 (el 4 ths))))))) THEN
    GEN_TAC THEN
    ASM_CASES_TAC (Term`(x':'a) = x`) THENL
    [IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
     ASM_REWRITE_TAC [] THEN
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
     ASM_REWRITE_TAC [],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN
     POP_ASSUM (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] 
                           (SPEC (Term`y:'b`) th))) THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     ASM_REWRITE_TAC [] THEN 
     ASSUM_LIST (fn ths => REWRITE_TAC [
                   ONCE_REWRITE_RULE [FAPPLY_FUPDATE] 
                    (SPEC (Term`x:'a`) (el 4 ths))]) THEN
     ONCE_ASM_REWRITE_TAC [] THEN
     IMP_RES_TAC  NOT_EQ_FAPPLY THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     REWRITE_TAC []
    ]
  ]
 ]
);

val fmap_EQ = store_thm("fmap_EQ", 
Term`!(f:('a,'b) fmap) g.
    (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) = (f = g)`,
REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC [fmap_EQ_1, fmap_EQ_2]);

(*and now a more useful equality*)
val fmap_EQ_THM = store_thm("fmap_EQ_THM", 
Term`!(f:('a,'b) fmap) g.
    (FDOM f = FDOM g) /\ 
    (!x. FDOM f x ==> (FAPPLY f x = FAPPLY g x)) = (f = g)`,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[
 STRIP_TAC THEN 
 ASM_REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 MATCH_MP_TAC EQ_EXT THEN
 GEN_TAC THEN
 ASM_CASES_TAC (Term`FDOM (f:('a,'b) fmap) x`) THENL
 [RES_TAC,
  ASSUM_LIST (fn ths => ASSUME_TAC (REWRITE_RULE [el 3 ths] (el 1 ths))) THEN
  IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
  ASM_REWRITE_TAC []
 ],
 STRIP_TAC THEN ASM_REWRITE_TAC []
]
);



(*Additional theorems and definitions*)

 

(* Define a notion of submap *)

val SUBMAP_DEF = new_infix_definition ("SUBMAP_DEF",
 Term`!(f : ('a,'b) fmap) g. SUBMAP f g = 
              !x. (FDOM f x) ==> 
                 (FDOM g x /\
                  (FAPPLY f x = FAPPLY g x))`,500);

(*And prove a few theorems to illustrate this*)

val SUBMAP_FEMPTY = store_thm("SUBMAP_FEMPTY",
Term`!(f : ('a,'b) fmap). FEMPTY SUBMAP f`,
REWRITE_TAC [SUBMAP_DEF, FDOM_FEMPTY]);



val SUBMAP_REFL = store_thm("SUBMAP_REFL",
Term`!(f : ('a,'b) fmap). f SUBMAP  f`,
REWRITE_TAC [SUBMAP_DEF]);

val SUBMAP_ANTISYM = store_thm("SUBMAP_ANTISYM",
Term`!(f : ('a,'b) fmap) g. 
     (f SUBMAP g /\ g SUBMAP f) = (f = g)`,
GEN_TAC THEN GEN_TAC THEN EQ_TAC THENL
[
 REWRITE_TAC[SUBMAP_DEF, ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ_THM] THEN
 STRIP_TAC THEN CONJ_TAC THENL
 [
  MATCH_MP_TAC EQ_EXT THEN
  GEN_TAC THEN 
  EQ_TAC THEN STRIP_TAC THEN RES_TAC,
  GEN_TAC THEN STRIP_TAC THEN RES_TAC
 ],
 STRIP_TAC THEN ASM_REWRITE_TAC [SUBMAP_REFL]
]);

(*Restriction*)


val res_lemma = prove (
Term`!(f : ('a,'b) fmap) (r: 'a -> bool).
        ?res.
           (!x.(FDOM res x) = ((FDOM f x) /\ r x)) /\
           (!x.FAPPLY res x = 
               ((FDOM f x /\ r x) =>
                   (FAPPLY f x) | (FAPPLY FEMPTY x)))`,
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[
 GEN_TAC THEN
 EXISTS_TAC (Term`FEMPTY:('a,'b)fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY],
 REPEAT STRIP_TAC THEN
 ASSUM_LIST (fn ths => 
   STRIP_ASSUME_TAC (SPEC (Term`r:'a->bool`) (el 2 ths))) THEN
 ASM_CASES_TAC (Term`(r:'a -> bool) x`) THENL
 [
  EXISTS_TAC (Term`FUPDATE (res:('a,'b)fmap) (x,y)`) THEN
  CONJ_TAC THEN GEN_TAC THENL
  [
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN  ASM_REWRITE_TAC [FDOM_FUPDATE],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE]
   ]
  ],
  EXISTS_TAC (Term`res:('a,'b)fmap`) THEN
  CONJ_TAC THEN GEN_TAC  THENL
  [
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN  ASM_REWRITE_TAC [FDOM_FUPDATE],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE]
   ]
  ]
 ]
]);

val res_exists = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) res_lemma;

val DRESTRICT_DEF = 
   new_specification {name = "DRESTRICT_DEF",
                      consts = [{fixity = Prefix, 
                                 const_name = "DRESTRICT"}],
                      sat_thm = res_exists};


val DRESTRICT_FEMPTY = 
store_thm ("DRESTRICT_FEMPTY",
Term`!r. DRESTRICT (FEMPTY:('a,'b)fmap) r = FEMPTY`,
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [DRESTRICT_DEF, FDOM_FEMPTY]);

val DRESTRICT_FUPDATE = 
store_thm("DRESTRICT_FUPDATE",
Term`!(f:('a,'b)fmap) r x y. 
     DRESTRICT (FUPDATE f (x,y)) r = 
            (r x => (FUPDATE (DRESTRICT f r) (x,y)) 
                                | DRESTRICT f r)`,
REPEAT STRIP_TAC THEN
COND_CASES_TAC THEN
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x':'a) = x`) THEN
ASM_REWRITE_TAC [FAPPLY_FUPDATE] THEN
TRY (IMP_RES_TAC NOT_EQ_FAPPLY) THEN
ASM_REWRITE_TAC [DRESTRICT_DEF]);


val STRONG_DRESTRICT_FUPDATE = 
store_thm ("STRONG_DRESTRICT_FUPDATE",
Term`!(f:('a,'b)fmap) r x y.
  r x ==>
  (DRESTRICT (FUPDATE f (x,y)) r 
    = FUPDATE (DRESTRICT f (\v. ~(v=x) /\ r v)) (x,y))`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONJ_TAC THEN
MATCH_MP_TAC EQ_EXT THEN GEN_TAC THENL
[
 ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] THEN
 BETA_TAC THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC [],
 ASM_CASES_TAC (Term`(x':'a) = x`) THENL
 [ 
  ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE,DRESTRICT_DEF] THEN
  BETA_TAC,
  IMP_RES_TAC NOT_EQ_FAPPLY THEN
  ASM_REWRITE_TAC [DRESTRICT_FUPDATE, DRESTRICT_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE]
 ]
]);


val FDOM_DRESTRICT = store_thm ("FDOM_DRESTRICT",
Term`!(f:('a,'b)fmap) r x.
  ~(r x) ==> ~(FDOM (DRESTRICT f r) x)`,
REPEAT GEN_TAC THEN  STRIP_TAC THEN
ASM_REWRITE_TAC [DRESTRICT_DEF]);

val lemma = prove(Term`!(a:'a) b. (a = b) ==> (b = a)`,
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val NOT_FDOM_DRESTRICT = store_thm ("NOT_FDOM_DRESTRICT",
Term`!(f:('a,'b)fmap) x. ~(FDOM f x) ==> (DRESTRICT f (\a. ~(a = x)) = f)`,
STRIP_TAC THEN 
ASM_REWRITE_TAC [GSYM fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
ASM_REWRITE_TAC [DRESTRICT_DEF] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x':'a)=x`) THEN
BETA_TAC THEN
ASM_REWRITE_TAC  [ NOT_FDOM_FAPPLY_FEMPTY] THEN
ASM_CASES_TAC (Term`FDOM (f:('a,'b)fmap) x'`) THEN
ASM_REWRITE_TAC  [] THEN
MATCH_MP_TAC lemma THEN
MATCH_MP_TAC  NOT_FDOM_FAPPLY_FEMPTY THEN
ASM_REWRITE_TAC  [ NOT_FDOM_FAPPLY_FEMPTY]
);


val DRESTRICT_SUBMAP = store_thm("DRESTRICT_SUBMAP",
Term`!(f:('a,'b)fmap) r.
       (DRESTRICT f r) SUBMAP f`,
INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
[
 REWRITE_TAC [DRESTRICT_FEMPTY, SUBMAP_FEMPTY],
 REPEAT STRIP_TAC THEN 
 REWRITE_TAC [DRESTRICT_FUPDATE] THEN
 COND_CASES_TAC THEN 
 UNDISCH_TAC (Term`!r. DRESTRICT (f:('a,'b)fmap) r SUBMAP f`) THEN
 REWRITE_TAC [SUBMAP_DEF] THENL
 [
  STRIP_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
  ASM_CASES_TAC (Term`x':'a = x`) THENL
  [
   ASM_REWRITE_TAC [FAPPLY_FUPDATE],
   ASM_REWRITE_TAC [] THEN
   IMP_RES_TAC NOT_EQ_FAPPLY THEN
   ASM_REWRITE_TAC []
  ],
   STRIP_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
  ASM_CASES_TAC (Term`x':'a = x`) THENL
  [
    POP_ASSUM SUBST_ALL_TAC THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC [] THEN
    RES_TAC THEN
    RES_TAC,
    DISCH_TAC THEN
    ASM_REWRITE_TAC [] THEN
    IMP_RES_TAC NOT_EQ_FAPPLY THEN
    RES_TAC THEN
    ASM_REWRITE_TAC [] 
  ]
]]);
    
val DRESTRICT_DRESTRICT = store_thm ("DRESTRICT_DRESTRICT",
Term`!(f:('a,'b)fmap) P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (\x. P x /\ Q x)`,
MATCH_MP_TAC (
BETA_RULE (
SPEC (Term`\(f:('a,'b)fmap). !P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (\x. P x /\ Q x)`)
fmap_INDUCT)) THEN
REWRITE_TAC [DRESTRICT_FEMPTY, DRESTRICT_FUPDATE] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(P:'a-> bool) x`) THEN
ASM_CASES_TAC (Term`(Q:'a-> bool) x`) THEN
BETA_TAC THEN
ASM_REWRITE_TAC [DRESTRICT_FUPDATE]);

val DRESTRICT_IS_FEMPTY = store_thm ("DRESTRICT_IS_FEMPTY",
Term`!r. (!x. ~(r x)) ==> !(f:('a,'b)fmap). DRESTRICT  f  r = FEMPTY`,
GEN_TAC THEN DISCH_TAC THEN
MATCH_MP_TAC (
BETA_RULE (
SPEC (Term`\(f:('a,'b)fmap). DRESTRICT  f  r = FEMPTY`)
fmap_INDUCT)) THEN
ASM_REWRITE_TAC  [DRESTRICT_FEMPTY, DRESTRICT_FUPDATE] THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val FUPDATE_DRESTRICT = store_thm("FUPDATE_DRESTRICT",
Term`!(f:('a,'b)fmap) x y. FUPDATE f (x,y) = FUPDATE (DRESTRICT f (\v. ~(v = x))) (x,y)`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONJ_TAC THEN
MATCH_MP_TAC EQ_EXT THEN GEN_TAC THENL
[
 ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] THEN
 BETA_TAC THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC [],
 ASM_CASES_TAC (Term`(x':'a) = x`) THENL
 [ 
  ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE,DRESTRICT_DEF] THEN
  BETA_TAC,
  IMP_RES_TAC NOT_EQ_FAPPLY THEN
  ASM_REWRITE_TAC [DRESTRICT_FUPDATE, DRESTRICT_DEF] THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
  ASM_CASES_TAC (Term`FDOM (f:('a,'b)fmap) x'`) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
  ASM_REWRITE_TAC []
 ]
]);

val lemma = prove(Term`(\x':'a. (~(x' = x) /\ r x') /\ ~(x' = x)) = 
                     (\x'. ~(x' = x) /\ r x')`,
CONV_TAC FUN_EQ_CONV THEN
BETA_TAC THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC [] THEN
RES_TAC);


val STRONG_DRESTRICT_FUPDATE_THM = 
store_thm ("STRONG_DRESTRICT_FUPDATE_THM",
Term`!(f:('a,'b)fmap) r x y.
  (DRESTRICT (FUPDATE f (x,y)) r 
    = (r x => FUPDATE (DRESTRICT f (\v. ~(v=x) /\ r v)) (x,y) |
              (DRESTRICT f (\v. ~(v=x) /\ r v)) ))`,
REPEAT STRIP_TAC THEN 
ASM_CASES_TAC (Term`(r:'a -> bool) x`) THEN
ASM_REWRITE_TAC  [STRONG_DRESTRICT_FUPDATE] THEN
ONCE_REWRITE_TAC [FUPDATE_DRESTRICT] THEN
ASM_REWRITE_TAC  [DRESTRICT_FUPDATE, DRESTRICT_DRESTRICT] THEN
BETA_TAC THEN ASM_REWRITE_TAC  [lemma]);




(*----------------------------------------*)


val union_lemma = prove (
Term`!(f : ('a,'b) fmap) g.
        ?union.
           (!x.(FDOM union x) = ((FDOM f x) \/ (FDOM g x))) /\
           (!x.FAPPLY union x = 
               ((FDOM f x) =>
                   (FAPPLY f x) | (FAPPLY g x)))`,
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[GEN_TAC THEN
 EXISTS_TAC (Term`g:('a,'b)fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY] 
,
 REPEAT STRIP_TAC THEN
 ASSUM_LIST (fn ths => 
   STRIP_ASSUME_TAC (SPEC (Term`g:('a,'b)fmap`) (el 2 ths))) THEN
 EXISTS_TAC (Term`FUPDATE (union:('a,'b)fmap) (x,y)`) THEN
 ASM_REWRITE_TAC[FDOM_FUPDATE] THEN
 CONJ_TAC THEN GEN_TAC THENL
 [ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC[],
  ASM_CASES_TAC (Term`(x':'a) = x`) THENL  
  [ASM_REWRITE_TAC [FAPPLY_FUPDATE],
   IMP_RES_TAC NOT_EQ_FAPPLY THEN
   ASM_REWRITE_TAC []
  ]
 ]
]);


val union_exists = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) union_lemma;

val FUNION_DEF = 
   new_specification {name = "FUNION_DEF",
                      consts = [{fixity = Prefix, 
                                 const_name = "FUNION"}],
                      sat_thm = union_exists};


val FUNION_FEMPTY_1 = 
store_thm ("FUNION_FEMPTY_1",
Term`!g. FUNION (FEMPTY:('a,'b)fmap) g = g`,
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [FUNION_DEF, FDOM_FEMPTY]);

val FUNION_FEMPTY_2 = 
store_thm ("FUNION_FEMPTY_2",
Term`!f. FUNION f (FEMPTY:('a,'b)fmap)  = f`,
 REPEAT STRIP_TAC THEN
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
 REWRITE_TAC [FUNION_DEF, FDOM_FEMPTY] THEN
 STRIP_TAC THEN
 COND_CASES_TAC THENL
 [REWRITE_TAC[],
  IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
  ASM_REWRITE_TAC []
 ]
);

val FUNION_FUPDATE_1 =
store_thm ("FUNION_FUPDATE_1",
Term`!(f:('a,'b)fmap) g x y. 
     FUNION (FUPDATE f (x,y)) g =
        FUPDATE (FUNION f g) (x,y)`,
 REPEAT STRIP_TAC THEN
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
 REPEAT STRIP_TAC THENL
 [
   REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] THEN
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC[],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
    IMP_RES_TAC NOT_EQ_FAPPLY THEN
    ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
   ]
 ]);

val FUNION_FUPDATE_2 =
store_thm ("FUNION_FUPDATE_2",
Term`!(f:('a,'b)fmap) g x y. 
     FUNION f (FUPDATE g (x,y)) =
        (FDOM f x => FUNION f g 
                       | FUPDATE (FUNION f g) (x,y))`,
 REPEAT STRIP_TAC THEN
 COND_CASES_TAC THEN
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
 REPEAT STRIP_TAC THENL
 [
   REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] THEN
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC[],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
    IMP_RES_TAC NOT_EQ_FAPPLY THEN
    ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
   ], 
   REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] THEN
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN ASM_REWRITE_TAC[],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
    IMP_RES_TAC NOT_EQ_FAPPLY THEN
    ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
   ]
 ]);

val FDOM_FUNION = store_thm ("FDOM_FUNION",
Term`!(f:('a,'b)fmap) g x. 
  FDOM (FUNION f g) x = (FDOM f x) \/ (FDOM g x)`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [FUNION_DEF]);


val DRESTRICT_FUNION = store_thm ("DRESTRICT_FUNION",
Term`!(f:('a,'b)fmap) r q.
  DRESTRICT f (\x. (r x) \/ (q x)) = 
     FUNION (DRESTRICT f r) (DRESTRICT f q)`,
REPEAT GEN_TAC THEN
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
 REWRITE_TAC [DRESTRICT_DEF,FUNION_DEF] THEN
 BETA_TAC THEN REWRITE_TAC [LEFT_AND_OVER_OR ] THEN
 GEN_TAC THEN
 ASM_CASES_TAC (Term`FDOM (f:('a,'b)fmap) x`) THEN 
 ASM_REWRITE_TAC [] THEN
 ASM_CASES_TAC (Term`(r:'a->bool)x`) THEN 
 ASM_REWRITE_TAC []);

val DRESTRICT_TRUE = store_thm ("DRESTRICT_TRUE",
Term`!(f:('a,'b)fmap). DRESTRICT f (\x.T) = f`,
GEN_TAC THEN 
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [DRESTRICT_DEF] THEN
GEN_TAC THEN COND_CASES_TAC THENL
[REWRITE_TAC [] ,
 ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
 MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY THEN
 ASM_REWRITE_TAC []
]);
 



val lookup_DEF = new_definition ("lookup_DEF",
Term`!(f:('a,'b)fmap) x.FLOOKUP f x = (FDOM f x => INL (FAPPLY f x)|
                                     INR one)`);


(* Now lets define every_fmap *)

val FEVERY_DEF =
 new_definition ("FEVERY_DEF",
 Term`FEVERY P (f:('a,'b)fmap) =
       !x. FDOM f x ==> P (x,(FAPPLY f x))`); 

val FEVERY_FEMPTY = prove (
Term`!(P:('a # 'b)-> bool) . FEVERY P FEMPTY`,
STRIP_TAC THEN
REWRITE_TAC [FEVERY_DEF, FDOM_FEMPTY]);

val FEVERY_FUPDATE = prove (
Term`!P (f:('a,'b)fmap) x y.
     FEVERY P (FUPDATE f (x,y)) =
        P (x,y) /\ FEVERY P (DRESTRICT f (\v. ~(x = v)))`,
REPEAT GEN_TAC THEN
REWRITE_TAC [FEVERY_DEF, FDOM_FUPDATE] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL
[
 POP_ASSUM (fn th => 
     REWRITE_TAC [(REWRITE_RULE [FAPPLY_FUPDATE] (SPEC (Term`x:'a`) th))]) 
 ,
 REWRITE_TAC [DRESTRICT_DEF] THEN
 POP_ASSUM (fn th => STRIP_ASSUME_TAC (BETA_RULE 
                 (REWRITE_RULE [DRESTRICT_DEF] th))) THEN
 BETA_TAC THEN
 ASM_REWRITE_TAC [] THEN
 POP_ASSUM (ASSUME_TAC o NOT_EQ_SYM) THEN
 IMP_RES_TAC NOT_EQ_FAPPLY THEN
 POP_ASSUM (fn th => ASSUME_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] 
    (SPEC (Term`y:'b`) th))) THEN
 ONCE_ASM_REWRITE_TAC [] THEN
 FIRST_ASSUM MATCH_MP_TAC THEN
 ASM_REWRITE_TAC [] 
 ,
 ASM_REWRITE_TAC [FAPPLY_FUPDATE]
 ,
 ASSUM_LIST (fn ths => ASSUME_TAC (BETA_RULE (
          REWRITE_RULE [DRESTRICT_DEF] (SPEC (Term`x':'a`) (el 2 ths)))))
 THEN
 UNDISCH_TAC (Term`FDOM (f:('a,'b)fmap) x' /\ ~(x = x') ==>
          P
            (x',
             ((FDOM f x' /\ ~(x = x'))
              => (FAPPLY f x')
              | (FAPPLY FEMPTY x')))`)
 THEN
 ASM_CASES_TAC (Term`(x:'a)=x'`) THEN 
 ASM_REWRITE_TAC [FAPPLY_FUPDATE] THENL
 [POP_ASSUM (fn th => REWRITE_TAC [SYM th]) THEN
  ASM_REWRITE_TAC [],
  POP_ASSUM (ASSUME_TAC o NOT_EQ_SYM) THEN
  IMP_RES_TAC NOT_EQ_FAPPLY THEN
  ASM_REWRITE_TAC []
 ]
]);
  




(*----------------------------------------------------
More theorems
----------------------------------------------------*)


val FUPDATE_EXISTING = store_thm ("FUPDATE_EXISTING",
Term`!(f:('a,'b)fmap) v t. 
   (FDOM f v) /\ (FAPPLY f v = t)
    = (f = FUPDATE f (v,t))`,
REPEAT STRIP_TAC THEN
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
EQ_TAC THENL
[REPEAT STRIP_TAC THEN
 ASM_CASES_TAC (Term`(x:'a)=v`) THEN
 ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE] THEN
 IMP_RES_TAC NOT_EQ_FAPPLY THEN
 ASM_REWRITE_TAC[],
 REPEAT STRIP_TAC THEN 
 ONCE_ASM_REWRITE_TAC [] THEN
 REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE]
]);



(*Finiteness*)
val FINITE_FMAP = store_thm ("FINITE_FMAP",
Term`!(f:('a,'b)fmap). ?g. ?n. 
    !x. (FDOM f x) = (?i.  (i <  n) /\  (g i = x))`,
INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
[
 EXISTS_TAC (Term`\(x:num).(@(y:'a).F)`) THEN
 EXISTS_TAC (Term`0`) THEN
 REWRITE_TAC [FDOM_FEMPTY, prim_recTheory.NOT_LESS_0],
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (Term`\i:num.(i = n) => (x:'a) | g i`) THEN
 EXISTS_TAC (Term`SUC n`) THEN
 GEN_TAC THEN
 REWRITE_TAC [FDOM_FUPDATE] THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THEN
 ASM_REWRITE_TAC [] THENL
 [
  EXISTS_TAC (Term`n:num`) THEN
  BETA_TAC THEN
  REWRITE_TAC [prim_recTheory.LESS_SUC_REFL],
  EQ_TAC THEN STRIP_TAC THENL
  [
   EXISTS_TAC (Term`i:num`) THEN 
   IMP_RES_TAC (prim_recTheory.LESS_NOT_EQ) THEN
   BETA_TAC THEN ASM_REWRITE_TAC [prim_recTheory.LESS_THM],
   EXISTS_TAC (Term`i:num`) THEN 
   UNDISCH_TAC (Term`(\i:num. (i = n) => (x:'a) | (g i)) i = x'`) THEN
   BETA_TAC THEN
   IMP_RES_TAC (prim_recTheory.LESS_LEMMA1) THEN
   ASM_REWRITE_TAC [] THENL
   [
    DISCH_THEN (ASSUME_TAC o SYM) THEN RES_TAC,
    IMP_RES_TAC (prim_recTheory.LESS_NOT_EQ) THEN
    ASM_REWRITE_TAC []
   ]
  ]
 ]
]);



(*Completeness*)
(*Commented out since this is of theoretical interest but is of no
practical use

val rep_DEF = 
 new_definition("rep",
Term`!f:('a,'b)fmap. rep f = \x. (FDOM f x => INL (FAPPLY f x) | INR one)`)


val rep_empty = prove(Term`rep (FEMPTY:('a,'b)fmap) = (\x. INR one)`, 
REWRITE_TAC [rep_DEF,FDOM_FEMPTY]);

val rep_update = prove(
Term`!(f:('a,'b)fmap) a b.
      rep (FUPDATE  f (a,b)) = \x. (x=a => INL b | rep f x)`,
REPEAT GEN_TAC THEN
REWRITE_TAC[rep_DEF] THEN
MATCH_MP_TAC EQ_EXT THEN
GEN_TAC THEN BETA_TAC THEN
ASM_CASES_TAC (Term`(x:'a)=a`) THENL
[
 ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE],
 IMP_RES_TAC NOT_EQ_FAPPLY THEN
 ASM_REWRITE_TAC [FDOM_FUPDATE]
]);


val rep_onto = prove(
Term`!fn:'a -> ('b+one). is_fmap fn ==> (?fm. rep fm = fn)`,
is_fmap_RULE_INDUCT_TAC THENL
[EXISTS_TAC(Term`FEMPTY:('a,'b)fmap`) THEN
 REWRITE_TAC [rep_empty],
 GEN_TAC THEN GEN_TAC THEN
 EXISTS_TAC (Term`FUPDATE (fm:('a,'b)fmap) (a,b)`) THEN
 ASM_REWRITE_TAC [rep_update]
]);


val rep_one_one_lemma = prove(
Term`!(f:('a,'b)fmap) g. (rep f = rep g) ==> (FDOM f = FDOM g)`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [rep_DEF] THEN
BETA_TAC THEN
REPEAT STRIP_TAC THEN
POP_ASSUM (ASSUME_TAC o SPEC (Term`x:'a`)) THEN
UNDISCH_TAC  (Term`((FDOM (f:('a,'b)fmap)  x) => (INL (FAPPLY f x)) | (INR one)) =
          ((FDOM g x) => (INL (FAPPLY g x)) | (INR one))`) THEN
ASM_CASES_TAC(Term`FDOM (f:('a,'b)fmap) x`) THEN
ASM_CASES_TAC(Term`FDOM (g:('a,'b)fmap) x`) THEN
ASM_REWRITE_TAC [] THEN
DISCH_THEN (CHECK_ASSUME_TAC o REWRITE_RULE [definition "sum" "ISL"] o 
            AP_TERM (Term`(ISL:'b+one -> bool)`)));


val rep_ono_one = prove(
Term`!(f:('a,'b)fmap) g. (rep f = rep g) ==> (f = g)`,
REPEAT GEN_TAC THEN
DISCH_THEN (fn th => let val lm = MATCH_MP rep_one_one_lemma th in
                      ASSUME_TAC 
                           (CONV_RULE FUN_EQ_CONV 
                               (REWRITE_RULE [rep_DEF,lm] th)) THEN 
                      ASSUME_TAC lm
                     end) THEN
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ_THM] THEN
ASM_REWRITE_TAC [] THEN
GEN_TAC THEN 
DISCH_THEN (fn th => FIRST_ASSUM 
             (fn asm  => ASSUME_TAC (
                 REWRITE_RULE [th] (BETA_RULE (SPEC (Term`x:'a`) asm))))) THEN
POP_ASSUM (fn th =>
     ASM_REWRITE_TAC [ REWRITE_RULE [definition "sum" "OUTL"] (
            AP_TERM (Term`(OUTL:'b+one -> 'b)`) th)]));


val lemma2 = prove(
Term`!fm:('a,'b)fmap. is_fmap (rep fm)`,
INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
[REWRITE_TAC [rep_empty, is_fmap_empty],
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC is_fmap_update THEN
 ASM_REWRITE_TAC [rep_update] 
]);



*)

(*Composition*)

val f_o_f_lemma = prove (
Term`!(f : ('b,'c) fmap) (g : ('a,'b) fmap).
        ?comp.
           (!x.(FDOM comp x) = 
                      ((FDOM g x) /\ FDOM f (FAPPLY g x))) /\
           (!x.FDOM comp x ==> (FAPPLY comp x = 
               (FAPPLY f (FAPPLY g x))))`,
GEN_TAC THEN
INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
[
 EXISTS_TAC (Term`FEMPTY:('a,'c)fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY],
 REPEAT STRIP_TAC THEN
 (*ASSUM_LIST (fn ths => 
   STRIP_ASSUME_TAC (SPEC (Term`f: ('b,'c) fmap`) (el 2 ths))) THEN *)
 ASM_CASES_TAC (Term`FDOM (f:('b,'c) fmap) y`) THENL
 [
  EXISTS_TAC (Term`FUPDATE (comp:('a,'c)fmap) (x,(FAPPLY f (y:'b)))`) THEN
  CONJ_TAC THEN GEN_TAC THENL
  [
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE],
      IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE] 
   ],
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     IMP_RES_TAC (ISPEC (Term`comp:('a,'c)fmap`) NOT_EQ_FAPPLY)THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
     STRIP_TAC THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []
   ]
  ],
  EXISTS_TAC (Term`comp:('a,'c)fmap`) THEN
  CONJ_TAC THEN GEN_TAC  THENL
  [
   ASM_CASES_TAC (Term`(x':'a) = x`) THEN  
   ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE] THEN
   IMP_RES_TAC NOT_EQ_FAPPLY THEN 
   ASM_REWRITE_TAC [] ,
   ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     STRIP_TAC THEN
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     RES_TAC THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE]
   ]
  ]
 ]
]);


val f_o_f_exists = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) f_o_f_lemma;

val f_o_f_DEF = 
   new_specification {name = "f_o_f_DEF",
                      consts = [{fixity = Infix 500, 
                                 const_name = "f_o_f"}],
                      sat_thm = f_o_f_exists};

val fmap_EQ_TAC = 
  PURE_REWRITE_TAC [
    CONV_RULE (DEPTH_CONV FUN_EQ_CONV)
      (GSYM (fmap_EQ_THM))];

val f_o_f_FEMPTY_1 =
store_thm ("f_o_f_FEMPTY_1",
(Term`!(f:('a,'b)fmap). (FEMPTY:('b,'c)fmap) f_o_f f = FEMPTY`),
    GEN_TAC THEN fmap_EQ_TAC THEN
    REWRITE_TAC [f_o_f_DEF,FDOM_FEMPTY]
);

val f_o_f_FEMPTY_2 = 
save_thm("f_o_f_FEMPTY_2", prove((Term`!(f:('b,'c)fmap). f f_o_f (FEMPTY:('a,'b)fmap) = FEMPTY`),
    GEN_TAC THEN fmap_EQ_TAC THEN
    REWRITE_TAC [f_o_f_DEF,FDOM_FEMPTY]
));

val o_f_lemma = prove (
Term`!(f : 'b -> 'c) (g : ('a,'b) fmap).
        ?comp.
           (!x.(FDOM comp x) = 
                      (FDOM g x))  /\
           (!x.FDOM comp x ==> (FAPPLY comp x = 
               (f (FAPPLY g x))))`,
GEN_TAC THEN
INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
[
 EXISTS_TAC (Term`FEMPTY:('a,'c)fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY],
 REPEAT STRIP_TAC THEN
 EXISTS_TAC (Term`FUPDATE (comp:('a,'c)fmap) (x,(f (y:'b)))`) THEN
 CONJ_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
 ASM_CASES_TAC (Term`(x':'a) = x`) THENL
  [
   STRIP_TAC THEN
   ASM_REWRITE_TAC [FAPPLY_FUPDATE],
   IMP_RES_TAC NOT_EQ_FAPPLY THEN 
   IMP_RES_TAC (ISPEC (Term`comp:('a,'c)fmap`) NOT_EQ_FAPPLY) THEN 
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []
  ]
]);


val o_f_exists = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) o_f_lemma;

val o_f_DEF = 
   new_specification {name = "o_f_DEF",
                      consts = [{fixity = Infix 500, 
                                 const_name = "o_f"}],
                      sat_thm = o_f_exists};


val o_f_FDOM = store_thm("o_f_FDOM",
Term`!(f : 'b -> 'c) (g : ('a,'b) fmap).
       (!x. FDOM  g x = (FDOM (f o_f g) x))`,
REWRITE_TAC [o_f_DEF]);

val o_f_FAPPLY = store_thm("o_f_APPLY",
Term`!(f : 'b -> 'c) (g : ('a,'b) fmap).
       (!x. FDOM  g x ==> (FAPPLY (f o_f g) x = f (FAPPLY g x)))`,
REPEAT STRIP_TAC THEN
STRIP_ASSUME_TAC (SPECL [Term`f : 'b -> 'c`,Term`g : ('a,'b) fmap`] o_f_DEF) THEN
FIRST_ASSUM MATCH_MP_TAC THEN
ASM_REWRITE_TAC []);




(*Range*)

val FRANGE_DEF = 
new_definition("FRANGE_DEF",
Term`!(f:('a,'b)fmap) y. FRANGE f y = (?x.FDOM f x /\ (FAPPLY f x = y))`);

val FRANGE_FEMPTY = store_thm ("FRANGE_FEMPTY",
Term`!x. ~(FRANGE (FEMPTY:('a,'b)fmap) x)`,
REWRITE_TAC [FRANGE_DEF, FDOM_FEMPTY]);

val FRANGE_FUPDATE = store_thm ("FRANGE_FUPDATE",
Term`!(f:('a,'b)fmap)x y b. 
         FRANGE (FUPDATE f (x,y)) b = 
            (y = b) \/ FRANGE (DRESTRICT f (\a.~(a=x))) b`,
REPEAT GEN_TAC THEN
REWRITE_TAC [FRANGE_DEF,FDOM_FUPDATE,DRESTRICT_DEF] THEN
BETA_TAC THEN
EQ_TAC THEN STRIP_TAC  THENL
[
 UNDISCH_TAC  (Term`FAPPLY (FUPDATE (f:('a,'b)fmap) (x,y)) x' = b`) THEN
 ASM_REWRITE_TAC [FAPPLY_FUPDATE] THEN
 DISCH_TAC THEN ASM_REWRITE_TAC [],

 ASM_CASES_TAC (Term`(x':'a)=x`) THENL
 [
  UNDISCH_TAC  
    (Term`FAPPLY (FUPDATE (f:('a,'b)fmap) (x,y)) x' = b`) THEN
  ASM_REWRITE_TAC [FAPPLY_FUPDATE] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC [],
  DISJ2_TAC THEN
  EXISTS_TAC (Term`x':'a`) THEN
  ASM_REWRITE_TAC [] THEN
  IMP_RES_TAC NOT_EQ_FAPPLY THEN 
  POP_ASSUM (ASSUME_TAC o SPECL [Term`y:'b`,Term`f:('a,'b)fmap`] o
             ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  ASM_REWRITE_TAC []
 ],
 EXISTS_TAC (Term`x:'a`) THEN
 ASM_REWRITE_TAC [FAPPLY_FUPDATE],
  EXISTS_TAC (Term`x':'a`) THEN
  IMP_RES_TAC NOT_EQ_FAPPLY THEN 
  ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC   (Term`((FDOM (f:('a,'b)fmap) x' /\ ~(x' = x))
           => (FAPPLY f x')
           | (FAPPLY FEMPTY x')) =
          b`) THEN
  ASM_REWRITE_TAC []
]);
 
val SUBMAP_FRANGE = store_thm("SUBMAP_FRANGE",
Term`!(f : ('a,'b) fmap) g.
    f SUBMAP g ==> !x.  FRANGE f x ==> FRANGE g x`,
REPEAT GEN_TAC THEN
REWRITE_TAC [SUBMAP_DEF,FRANGE_DEF] THEN
REPEAT STRIP_TAC THEN
EXISTS_TAC (Term`x':'a`) THEN
RES_TAC THEN
POP_ASSUM SUBST_ALL_TAC THEN
ASM_REWRITE_TAC []);


(*Range restriction*)

val ranres_lemma = prove (
Term`!(f : ('a,'b) fmap) (r: 'b -> bool).
        ?res.
           (!x.(FDOM res x) = ((FDOM f x) /\ r (FAPPLY f x))) /\
           (!x.FAPPLY res x = 
               ((FDOM f x /\ r (FAPPLY f x)) =>
                   (FAPPLY f x) | (FAPPLY FEMPTY x)))`,
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[
 GEN_TAC THEN
 EXISTS_TAC (Term`FEMPTY:('a,'b)fmap`) THEN
 REWRITE_TAC [FDOM_FEMPTY],
 REPEAT STRIP_TAC THEN
 ASSUM_LIST (fn ths => 
   STRIP_ASSUME_TAC (SPEC (Term`r:'b->bool`) (el 2 ths))) THEN
 ASM_CASES_TAC (Term`(r:'b -> bool) y`) THENL
 [
  EXISTS_TAC (Term`FUPDATE (res:('a,'b)fmap) (x,y)`) THEN
  CONJ_TAC THEN GEN_TAC THEN
   (ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE]
   ])
  ,
  EXISTS_TAC (Term`res:('a,'b)fmap`) THEN
  CONJ_TAC THEN GEN_TAC  THEN
   (ASM_CASES_TAC (Term`(x':'a) = x`) THENL
   [
     ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY THEN 
     ASM_REWRITE_TAC [FDOM_FUPDATE]
   ])
 ]
]);

val FRANGE_exists = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) ranres_lemma;

val RRESTRICT_DEF = 
   new_specification {name = "RRESTRICT_DEF",
                      consts = [{fixity = Prefix, 
                                 const_name = "RRESTRICT"}],
                      sat_thm = FRANGE_exists};

val RRESTRICT_FEMPTY = 
store_thm ("RRESTRICT_FEMPTY",
Term`!r.RRESTRICT (FEMPTY:('a,'b)fmap) r = FEMPTY`,
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [RRESTRICT_DEF, FDOM_FEMPTY]);

val RRESTRICT_FUPDATE = 
store_thm ("RRESTRICT_FUPDATE",
Term`!(f:('a,'b)fmap) r x y. 
     RRESTRICT (FUPDATE f (x,y)) r = 
            (r y => (FUPDATE (RRESTRICT f r) (x,y)) 
                                | RRESTRICT 
                                     (DRESTRICT f (\a.~(a=x))) r)`,
REPEAT STRIP_TAC THEN
COND_CASES_TAC THENL
[
REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
ASM_REWRITE_TAC [FDOM_FUPDATE,RRESTRICT_DEF,DRESTRICT_DEF] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x':'a) = x`) THEN
ASM_REWRITE_TAC [FAPPLY_FUPDATE] THEN
TRY (IMP_RES_TAC NOT_EQ_FAPPLY) THEN
ASM_REWRITE_TAC [RRESTRICT_DEF],

REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] THEN
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
ASM_REWRITE_TAC [FDOM_FUPDATE,RRESTRICT_DEF,DRESTRICT_DEF] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC (Term`(x':'a) = x`) THEN
BETA_TAC THENL
[
ASM_REWRITE_TAC [FAPPLY_FUPDATE],

IMP_RES_TAC NOT_EQ_FAPPLY THEN
ASM_REWRITE_TAC [RRESTRICT_DEF] THEN
COND_CASES_TAC THEN ASM_REWRITE_TAC [],

ASM_REWRITE_TAC [FAPPLY_FUPDATE],

IMP_RES_TAC NOT_EQ_FAPPLY THEN
ASM_REWRITE_TAC [RRESTRICT_DEF] THEN
COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [DE_MORGAN_THM] ) THEN
ASM_REWRITE_TAC [] THEN
COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
POP_ASSUM (fn th => ASSUME_TAC 
      (REWRITE_RULE [CONJUNCT1 th] (CONJUNCT2 th) )) THEN
RES_TAC
]]);



(*Functions as finite maps*)

(*First we define a function to test if a predicate is
true for a finite number of elements*)



val {rules = FINITE_PRED_RULES, induction = FINITE_PRED_INDUCT} =
 let val FINITE_PRED  = Term`FINITE_PRED :('a -> bool) -> bool`
     infix -------------------------------------
     fun (x ------------------------------------- y) = (x,y)
  in
   indDefine "FINITE_PRED" 
        [ ([],                               [])
          -------------------------------------
                 `^FINITE_PRED  (\a. F)`       ,

          
          ([    `^FINITE_PRED  f`         ],[])
          -------------------------------------
          `^FINITE_PRED  (\x. (x = a) \/  f x)` ]  Prefix (`^FINITE_PRED  f`,[])
   end
 handle x => Raise x;

val [FINITE_PRED_EMPTY, FINITE_PRED_UPDATE] = FINITE_PRED_RULES;



val ffmap_lemma = prove (
Term`!(f:'a -> 'b) (P: 'a -> bool).
       FINITE_PRED P ==>
        ?ffmap.
           (!x.(FDOM ffmap x) = (P x)) /\
           (!x. P x  ==>  (FAPPLY ffmap x = f x))`,
GEN_TAC THEN
ind_defLib.RULE_INDUCT_THEN FINITE_PRED_INDUCT 
   STRIP_ASSUME_TAC STRIP_ASSUME_TAC THENL
[
 EXISTS_TAC (Term`FEMPTY:('a,'b)fmap`) THEN
 BETA_TAC THEN
 REWRITE_TAC [FDOM_FEMPTY],
 GEN_TAC THEN
 EXISTS_TAC (Term`FUPDATE (ffmap:('a,'b)fmap) (a,f a)`) THEN
 BETA_TAC THEN
 ASM_REWRITE_TAC [FDOM_FUPDATE] THEN
 STRIP_TAC THEN ASM_CASES_TAC (Term`(x:'a)=a`) THENL
 [
  ASM_REWRITE_TAC [FAPPLY_FUPDATE],
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  RES_TAC THEN
  IMP_RES_TAC NOT_EQ_FAPPLY THEN
  ASM_REWRITE_TAC []
 ]
]);


val ffmap_exists = CONV_RULE 
          (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC
           ONCE_DEPTH_CONV SKOLEM_CONV) ffmap_lemma;

val FUN_FMAP_DEF = 
   new_specification {name = "FUN_FMAP_DEF",
                      consts = [{fixity = Prefix, 
                                 const_name = "FUN_FMAP"}],
                      sat_thm = ffmap_exists} handle x => Raise x;


(*Composition of finite map and function*)

val f_o_DEF = new_infix_definition("f_o_DEF",
Term`f_o (f:('b,'c)fmap) (g:'a -> 'b)  
     = f f_o_f (FUN_FMAP g (\x. FDOM f (g x)))`,
500);

val FDOM_f_o = store_thm ("FDOM_f_o", 
Term`!(f : ('b, 'c)fmap)  (g : 'a -> 'b).
      FINITE_PRED (\x. FDOM f (g x)) ==> 
              (!x. FDOM (f f_o g) x =  (FDOM f (g x)))`,
REPEAT GEN_TAC THEN 
DISCH_THEN (fn th => STRIP_ASSUME_TAC (BETA_RULE 
   (SPEC (Term`g:'a->'b`)  (MATCH_MP FUN_FMAP_DEF th)))) THEN
ASM_REWRITE_TAC [f_o_DEF,f_o_f_DEF ] THEN GEN_TAC THEN 
EQ_TAC THEN
STRIP_TAC THEN
RES_TAC THEN
ASM_REWRITE_TAC []);


 val FAPPLY_f_o = store_thm ("FAPPLY_f_o", 
Term`!(f : ('b, 'c)fmap)  (g : 'a -> 'b).
      FINITE_PRED (\x. FDOM f (g x)) ==> 
           (!x.FDOM (f f_o g) x ==> 
             (FAPPLY (f f_o g) x =  (FAPPLY f (g x)))) `,
REPEAT GEN_TAC THEN 
DISCH_THEN (fn th => STRIP_ASSUME_TAC (BETA_RULE 
   (SPEC (Term`g:'a->'b`)  (MATCH_MP FUN_FMAP_DEF th))) THEN
    STRIP_ASSUME_TAC (MATCH_MP FDOM_f_o th)    ) THEN
GEN_TAC THEN 
DISCH_THEN (fn th => ASSUME_TAC (REWRITE_RULE [f_o_DEF] th) THEN
                     FIRST_ASSUM (fn asm => ASSUME_TAC
                           (EQ_MP (SPEC (Term`x:'a`) asm) th))) THEN
STRIP_ASSUME_TAC  f_o_f_DEF THEN
RES_TAC THEN
ASM_REWRITE_TAC [f_o_DEF]);


val FINITE_PRED_11 = store_thm("FINITE_PRED_11",
Term`!(g : 'a -> 'b). (!x y. (g x = g y) = (x = y)) ==>
   !(f : ('b, 'c)fmap) .
               FINITE_PRED (\x. FDOM f (g x))`,
GEN_TAC THEN DISCH_TAC THEN
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
[
 REWRITE_TAC [FDOM_FEMPTY, FINITE_PRED_EMPTY],
 REWRITE_TAC [FDOM_FUPDATE] THEN
 REPEAT STRIP_TAC THEN
 ASM_CASES_TAC (Term`?y. x = (g:'a -> 'b) y`) THENL
 [
  POP_ASSUM STRIP_ASSUME_TAC THEN
  IMP_RES_TAC FINITE_PRED_UPDATE THEN
  POP_ASSUM (ASSUME_TAC o BETA_RULE) THEN
  ASM_REWRITE_TAC [],
  POP_ASSUM (ASSUME_TAC o GSYM o (CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV))) THEN
  ASM_REWRITE_TAC [] 
 ]
]);
 

val _ = export_theory();


end;