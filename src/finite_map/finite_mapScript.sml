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
(*              and James Alves-Foss},  				  *)
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
(* interactive use:

 app load ["IndDefLib", "numLib", "NonRecSize", "oneTheory", "Q"];

 open IndDefLib oneTheory sumTheory pairTheory 
      numTheory prim_recTheory numLib;
*)


open HolKernel Parse boolLib IndDefLib numLib
     oneTheory sumTheory pairTheory numTheory prim_recTheory;

infixr -->;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->; 


val _ = new_theory "finite_map";

(*---------------------------------------------------------------------------
        Definition of a finite map

    The representation is the type 'a -> ('b + one) where only a finite
    number of the 'a map to a 'b and the rest map to one.  We define a
    notion of finiteness inductively.
 --------------------------------------------------------------------------- *)

val (rules,ind,cases) = 
 Hol_reln `is_fmap (\a. INR one) 
       /\ (!f a b. is_fmap f ==> is_fmap (\x. if x=a then INL b else f x))`;


val rule_list as [is_fmap_empty, is_fmap_update] = CONJUNCTS rules;

val is_fmap_RULE_INDUCT_TAC = IndDefRules.RULE_INDUCT_THEN ind STRIP_ASSUME_TAC;

val strong_ind = IndDefRules.derive_strong_induction(rule_list, ind);


(*---------------------------------------------------------------------------
        Existence theorem; type definition
 ---------------------------------------------------------------------------*)

val EXISTENCE_THM = Q.prove
(`?x:'a -> 'b + one. is_fmap x`,
EXISTS_TAC (Term`\x:'a. (INR one):'b + one`) 
 THEN REWRITE_TAC [is_fmap_empty]);

val fmap_TY_DEF = new_type_definition("fmap", EXISTENCE_THM);

val _ = add_infix_type
           {Prec = 50, 
            ParseName = SOME "|->", 
            Assoc = RIGHT,
            Name = "fmap"};

(* --------------------------------------------------------------------- *)
(* Define bijections                                                     *)
(* --------------------------------------------------------------------- *)

val fmap_ISO_DEF =
   define_new_type_bijections 
       {name = "fmap_ISO_DEF",
        ABS  = "fmap_ABS",
        REP  = "fmap_REP",
        tyax = fmap_TY_DEF};

(* --------------------------------------------------------------------- *)
(* Prove that REP is one-to-one.					 *)
(* --------------------------------------------------------------------- *)

val fmap_REP_11   = prove_rep_fn_one_one fmap_ISO_DEF
val fmap_REP_onto = prove_rep_fn_onto fmap_ISO_DEF
val fmap_ABS_11   = prove_abs_fn_one_one fmap_ISO_DEF
val fmap_ABS_onto = prove_abs_fn_onto fmap_ISO_DEF;

val (fmap_ABS_REP_THM,fmap_REP_ABS_THM)  =
 let val thms = CONJUNCTS fmap_ISO_DEF
     val [t1,t2] = map (GEN_ALL o SYM o SPEC_ALL) thms
 in (t1,t2)
  end;


(*---------------------------------------------------------------------------
        CANCELLATION THEOREMS
 ---------------------------------------------------------------------------*)

val is_fmap_REP = Q.prove 
(`!f:'a |-> 'b. is_fmap (fmap_REP f)`,
 REWRITE_TAC [fmap_REP_onto] 
  THEN GEN_TAC THEN Q.EXISTS_TAC `f` 
  THEN REWRITE_TAC [fmap_REP_11]);

val REP_ABS_empty = Q.prove 
(`fmap_REP (fmap_ABS ((\a. INR one):'a -> 'b + one)) = \a. INR one`,
 REWRITE_TAC [fmap_REP_ABS_THM] 
  THEN REWRITE_TAC [is_fmap_empty]);

val REP_ABS_update = Q.prove 
(`!(f:'a |-> 'b) x y.
     fmap_REP (fmap_ABS (\a. if a=x then INL y else fmap_REP f a))
         =
     \a. if a=x then INL y else fmap_REP f a`,
 REPEAT GEN_TAC 
   THEN REWRITE_TAC [fmap_REP_ABS_THM] 
   THEN MATCH_MP_TAC is_fmap_update 
   THEN REWRITE_TAC [is_fmap_REP]);

val is_fmap_REP_ABS = Q.prove 
(`!f:'a -> 'b + one. is_fmap f ==> (fmap_REP (fmap_ABS f) = f)`,
 REPEAT STRIP_TAC 
  THEN REWRITE_TAC [fmap_REP_ABS_THM]
  THEN ASM_REWRITE_TAC []);


(*---------------------------------------------------------------------------
        DEFINITIONS OF UPDATE, EMPTY, APPLY and DOMAIN
 ---------------------------------------------------------------------------*)

val FUPDATE_DEF = Q.new_definition 
("FUPDATE_DEF",
 `FUPDATE (f:'a |-> 'b) (x,y)
    = fmap_ABS (\a. if a=x then INL y else fmap_REP f a)`);

val FEMPTY_DEF = Q.new_definition 
("FEMPTY_DEF",
 `(FEMPTY:'a |-> 'b) = fmap_ABS (\a. INR one)`);

val FAPPLY_DEF = Q.new_definition 
("FAPPLY_DEF",
 `FAPPLY (f:'a |-> 'b) x = OUTL (fmap_REP f x)`);

val FDOM_DEF = Q.new_definition 
("FDOM_DEF",
 `FDOM (f:'a |-> 'b) x = ISL (fmap_REP f x)`);

val update_rep = Term`\(f:'a->'b+one) x y. \a. if a=x then INL y else f a`;

val empty_rep = Term`(\a. INR one):'a -> 'b + one`;



(*---------------------------------------------------------------------------
      Now some theorems
 --------------------------------------------------------------------------- *)

val FAPPLY_FUPDATE = Q.store_thm ("FAPPLY_FUPDATE",
`!(f:'a |-> 'b) x y. FAPPLY (FUPDATE f (x,y)) x = y`,
 REWRITE_TAC [FUPDATE_DEF, FAPPLY_DEF] 
   THEN REPEAT GEN_TAC 
    THEN REWRITE_TAC [REP_ABS_update] THEN BETA_TAC
    THEN REWRITE_TAC [sumTheory.OUTL]);

val NOT_EQ_FAPPLY = Q.store_thm ("NOT_EQ_FAPPLY",
`!(f:'a|-> 'b) a x y . ~(a=x) ==> (FAPPLY (FUPDATE f (x,y)) a = FAPPLY f a)`, 
REPEAT STRIP_TAC 
  THEN REWRITE_TAC [FUPDATE_DEF, FAPPLY_DEF, REP_ABS_update] THEN BETA_TAC
  THEN ASM_REWRITE_TAC []);

val update_commutes_rep = (BETA_RULE o BETA_RULE) (Q.prove 
(`!(f:'a -> 'b + one) a b c d.
     ~(a = c) 
        ==> 
 (^update_rep (^update_rep f a b) c d = ^update_rep (^update_rep f c d) a b)`,
REPEAT STRIP_TAC THEN BETA_TAC 
  THEN MATCH_MP_TAC EQ_EXT 
  THEN GEN_TAC 
  THEN Q.ASM_CASES_TAC `x = a` THEN BETA_TAC 
  THEN ASM_REWRITE_TAC []));


val FUPDATE_COMMUTES = Q.store_thm ("FUPDATE_COMMUTES",
`!(f:'a |-> 'b) a b c d.
   ~(a = c) 
     ==> 
  (FUPDATE (FUPDATE f (a,b)) (c,d) = FUPDATE (FUPDATE f (c,d)) (a,b))`,
REPEAT STRIP_TAC 
  THEN REWRITE_TAC [FUPDATE_DEF, REP_ABS_update] THEN BETA_TAC 
  THEN AP_TERM_TAC 
  THEN MATCH_MP_TAC EQ_EXT 
  THEN GEN_TAC 
  THEN Q.ASM_CASES_TAC `x = a` THEN BETA_TAC 
  THEN ASM_REWRITE_TAC []);

val update_same_rep = (BETA_RULE o BETA_RULE) (Q.prove 
(`!(f:'a -> 'b+one) a b c.
   ^update_rep (^update_rep f a b) a c = ^update_rep f a c`,
BETA_TAC THEN REPEAT GEN_TAC 
  THEN MATCH_MP_TAC EQ_EXT 
  THEN GEN_TAC 
  THEN Q.ASM_CASES_TAC `x = a` THEN BETA_TAC 
  THEN ASM_REWRITE_TAC []));

val FUPDATE_EQ = Q.store_thm ("FUPDATE_EQ",
`!(f:'a |-> 'b) a b c. FUPDATE (FUPDATE f (a,b)) (a,c) = FUPDATE f (a,c)`,
REPEAT STRIP_TAC 
  THEN REWRITE_TAC [FUPDATE_DEF, REP_ABS_update] THEN BETA_TAC 
  THEN AP_TERM_TAC 
  THEN MATCH_MP_TAC EQ_EXT 
  THEN GEN_TAC 
  THEN Q.ASM_CASES_TAC `x = a` THEN BETA_TAC 
  THEN ASM_REWRITE_TAC []);

val lemma1 = Q.prove
(`~((ISL :'b + one -> bool) ((INR :one -> 'b + one) one))`,
 REWRITE_TAC [sumTheory.ISL]);

val FDOM_FEMPTY = Q.store_thm ("FDOM_FEMPTY",
`!a. FDOM (FEMPTY:'a |-> 'b) a = F`,
GEN_TAC THEN REWRITE_TAC [FDOM_DEF, FEMPTY_DEF, REP_ABS_empty, sumTheory.ISL]);

val dom_update_rep = BETA_RULE (Q.prove
(`!f a b x. ISL(^update_rep (f:'a -> 'b+one ) a b x) = ((x=a) \/ ISL (f x))`,
REPEAT GEN_TAC THEN BETA_TAC 
  THEN Q.ASM_CASES_TAC `x = a` 
  THEN ASM_REWRITE_TAC [sumTheory.ISL]));

val FDOM_FUPDATE = Q.store_thm("FDOM_FUPDATE",
`!f a b x. FDOM (FUPDATE (f:'a |-> 'b) (a,b)) x = (x=a) \/ FDOM f x`,
REPEAT GEN_TAC 
  THEN REWRITE_TAC [FDOM_DEF,FUPDATE_DEF, REP_ABS_update] THEN BETA_TAC 
  THEN Q.ASM_CASES_TAC `x = a` 
  THEN ASM_REWRITE_TAC [sumTheory.ISL]);

val FAPPLY_FUPDATE_THM = Q.store_thm("FAPPLY_FUPDATE_THM",
`!(f:'a |-> 'b) a b x.
   FAPPLY(FUPDATE f (a,b)) x = if x=a then b else FAPPLY f x`,
REPEAT STRIP_TAC 
  THEN COND_CASES_TAC 
  THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] 
  THEN IMP_RES_TAC NOT_EQ_FAPPLY 
  THEN ASM_REWRITE_TAC []);

val not_eq_empty_update_rep = BETA_RULE (Q.prove 
(`!(f:'a -> 'b + one) a b. ~(^empty_rep = ^update_rep f a b)`,
REPEAT GEN_TAC THEN BETA_TAC 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN CONV_TAC NOT_FORALL_CONV 
  THEN Q.EXISTS_TAC `a` THEN BETA_TAC
  THEN DISCH_THEN (fn th => REWRITE_TAC [REWRITE_RULE [sumTheory.ISL]
                               (REWRITE_RULE [th] lemma1)])));

val fmap_EQ_1 = Q.prove 
(`!(f:'a |-> 'b) g. (f=g) ==> (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g)`,
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val NOT_EQ_FEMPTY_FUPDATE = Q.store_thm ("NOT_EQ_FEMPTY_FUPDATE",
`!(f:'a |-> 'b) a b. ~(FEMPTY = FUPDATE f (a,b))`,
REPEAT STRIP_TAC 
  THEN IMP_RES_TAC fmap_EQ_1 
  THEN UNDISCH_TAC (Term`FDOM (FEMPTY:('a,'b)fmap) =
          FDOM (FUPDATE (f:('a,'b)fmap) (a,b))`) 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN REWRITE_TAC [] 
  THEN CONV_TAC NOT_FORALL_CONV 
  THEN Q.EXISTS_TAC `a` 
  THEN REWRITE_TAC [FDOM_FEMPTY, FDOM_FUPDATE]);

val FDOM_EQ_FDOM_FUPDATE = Q.store_thm("FDOM_EQ_FDOM_FUPDATE",
`!(f:'a |-> 'b) x. FDOM f x ==> (!y. FDOM (FUPDATE f (x,y)) = FDOM f)`,
REPEAT STRIP_TAC 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN GEN_TAC THEN ASM_CASES_TAC (Term`(x':'a)=x`) 
  THEN ASM_REWRITE_TAC [FDOM_FUPDATE]);

val lemma2 = Q.prove 
(`!x y z. (x ==> (y /\ z)) ==> (x ==> y)`, REPEAT STRIP_TAC THEN RES_TAC);


(*---------------------------------------------------------------------------
       Simple induction
 ---------------------------------------------------------------------------*)

val fmap_SIMPLE_INDUCT = Q.store_thm ("fmap_SIMPLE_INDUCT",
`!P:('a |-> 'b) -> bool. 
     P FEMPTY /\ 
     (!f. P f ==> !x y. P (FUPDATE f (x,y)))
     ==> 
     !f. P f`,
REWRITE_TAC [FUPDATE_DEF, FEMPTY_DEF] 
  THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC 
  THEN CHOOSE_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) (Q.SPEC`f` fmap_ABS_onto)
  THEN Q.ID_SPEC_TAC `r`
  THEN HO_MATCH_MP_TAC strong_ind 
  THEN ASM_REWRITE_TAC []
  THEN Q.PAT_ASSUM `P x` (K ALL_TAC)
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN IMP_RES_THEN SUBST_ALL_TAC is_fmap_REP_ABS
  THEN ASM_REWRITE_TAC[]);

val FUPDATE_ABSORB_THM = Q.prove 
(`!(f:'a |-> 'b) x y. 
     FDOM f x /\ (FAPPLY f x = y) ==> (FUPDATE f (x,y) = f)`,
 INDUCT_THEN fmap_SIMPLE_INDUCT STRIP_ASSUME_TAC 
   THEN REWRITE_TAC [FDOM_FEMPTY] 
   THEN REPEAT STRIP_TAC 
   THEN Q.ASM_CASES_TAC `x = x'` THENL
   [ASM_REWRITE_TAC [FUPDATE_EQ] 
      THEN Q.ASM_CASES_TAC `y = y'` 
      THEN ASM_REWRITE_TAC [] 
      THEN ASSUM_LIST (fn ths => ASSUME_TAC (
           REWRITE_RULE [el 2 ths, FAPPLY_FUPDATE, el 1 ths] (el 3 ths))) 
      THEN MATCH_MP_TAC FALSITY THEN ASM_REWRITE_TAC[],
    IMP_RES_TAC FUPDATE_COMMUTES 
      THEN ASM_REWRITE_TAC []
      THEN ASSUM_LIST (fn ths => ASSUME_TAC 
            (REWRITE_RULE [MATCH_MP NOT_EQ_FAPPLY (NOT_EQ_SYM (el 2 ths))]
                  (el 3 ths))) 
      THEN ASSUM_LIST (fn ths => ASSUME_TAC 
            (REWRITE_RULE [FDOM_FUPDATE, (NOT_EQ_SYM (el 3 ths))] (el 5 ths)))
      THEN RES_TAC 
      THEN ASM_REWRITE_TAC []]);

val FDOM_FAPPLY = Q.prove
(`!(f:'a |-> 'b) x. FDOM f x ==> ?y. FAPPLY f x = y`,
 INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
 [REWRITE_TAC [FDOM_FEMPTY],
  REWRITE_TAC [FDOM_FUPDATE] 
    THEN REPEAT GEN_TAC 
    THEN Q.ASM_CASES_TAC `x' = x` 
    THEN ASM_REWRITE_TAC [] THENL
    [Q.EXISTS_TAC `y` THEN REWRITE_TAC [FAPPLY_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN DISCH_TAC THEN RES_TAC 
       THEN Q.EXISTS_TAC `y'` 
       THEN ASM_REWRITE_TAC []]]);

val FDOM_FUPDATE_ABSORB = Q.prove 
(`!(f:'a |-> 'b) x. FDOM f x ==> ?y. FUPDATE f (x,y) = f`,
 REPEAT STRIP_TAC 
   THEN IMP_RES_TAC FDOM_FAPPLY 
   THEN Q.EXISTS_TAC `y`
   THEN MATCH_MP_TAC FUPDATE_ABSORB_THM 
   THEN ASM_REWRITE_TAC []);

val FDOM_F_FEMPTY = Q.store_thm 
("FDOM_F_FEMPTY1",
 `!f:'a |-> 'b. (!a. ~FDOM f a) = (f = FEMPTY)`,
 INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
 [REWRITE_TAC [FDOM_FEMPTY],
  GEN_TAC THEN GEN_TAC
    THEN REWRITE_TAC [NOT_EQ_SYM(Q.SPECL[`f`,`x`,`y`] NOT_EQ_FEMPTY_FUPDATE)] 
    THEN CONV_TAC NOT_FORALL_CONV 
    THEN Q.EXISTS_TAC `x`
    THEN REWRITE_TAC [FDOM_FUPDATE]]);


(* ===================================================================== *)
(* Cardinality                                                           *)
(*                                                                       *)
(* Define cardinality by copying the proofs in the sets library. To      *)
(* simplify this we define cardinality as a function over the domain     *)
(* FDOM f of the finite map. We need to define deletion from the domain. *)
(* ===================================================================== *)

val FDOMDEL_DEF = Q.new_definition 
("FDOMDEL_DEF",
 `FDOMDEL (d:'a->bool) x a = d a /\ (~(a = x))`);


val FDOMDEL_COMM = Q.prove 
(`!(s:'a->bool) x y. FDOMDEL (FDOMDEL s x) y = FDOMDEL (FDOMDEL s y) x`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN REWRITE_TAC [FDOMDEL_DEF] 
  THEN REPEAT STRIP_TAC 
  THEN EQ_TAC 
  THEN STRIP_TAC 
  THEN ASM_REWRITE_TAC []);

val FDOM_FDOM_DEL = Q.prove 
(`!(f:'a |-> 'b) x.
     ~FDOM f x ==> !y. (FDOMDEL (FDOM (FUPDATE f (x,y))) x) = FDOM f`,
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN REWRITE_TAC [FDOMDEL_DEF, FDOM_FUPDATE] 
  THEN REPEAT STRIP_TAC 
  THEN Q.ASM_CASES_TAC `x' = x` 
  THEN ASM_REWRITE_TAC []);

val FDOMDEL_FEMPTY = Q.prove
(`!x. FDOMDEL (FDOM (FEMPTY:'a |-> 'b)) x = FDOM (FEMPTY:'a |-> 'b)`,
CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
 THEN REWRITE_TAC [FDOMDEL_DEF, FDOM_FEMPTY]);

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

val CARD_REL_EXISTS = prove_rec_fn_exists num_Axiom card_rel_def ;

val CARD_REL_DEL_LEMMA = TAC_PROOF
((strip_conj card_rel_def,
Term`!(n:num) (s:'a -> bool) (x:'a).
      s x ==> R (FDOMDEL s x) n
       ==>
      !y:'a. s y ==> R (FDOMDEL s y) n`),
 INDUCT_TAC THENL
 [REPEAT GEN_TAC THEN DISCH_TAC 
    THEN ASM_REWRITE_TAC [] 
    THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
    THEN ASM_REWRITE_TAC [FDOMDEL_DEF, FDOM_FEMPTY] 
    THEN STRIP_TAC THEN GEN_TAC 
    THEN FIRST_ASSUM (STRIP_ASSUME_TAC o
           REWRITE_RULE [DE_MORGAN_THM] o (SPEC (Term`y:'a`))) 
    THEN ASM_REWRITE_TAC [],
  ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC 
    THEN let val th = Q.SPEC `y:'a = x'` EXCLUDED_MIDDLE
         in DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th end THENL
    [CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
       THEN PURE_ONCE_REWRITE_TAC [FDOMDEL_COMM] 
       THEN Q.EXISTS_TAC `x` 
       THEN ASM_REWRITE_TAC[] 
       THEN Q.UNDISCH_TAC `FDOMDEL (s:'a->bool) x x'` 
       THEN ASM_REWRITE_TAC [FDOMDEL_DEF] 
       THEN DISCH_THEN(fn th => REWRITE_TAC [NOT_EQ_SYM th]),
     let val th = Q.SPEC `x = y` EXCLUDED_MIDDLE
     in DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th end THENL
     [Q.EXISTS_TAC `x'` THEN ASM_REWRITE_TAC [],
      Q.EXISTS_TAC `x` 
        THEN ASM_REWRITE_TAC [FDOMDEL_DEF] 
        THEN RES_THEN (TRY o IMP_RES_THEN ASSUME_TAC) 
        THEN PURE_ONCE_REWRITE_TAC [FDOMDEL_COMM] 
        THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [FDOMDEL_DEF] 
        THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) 
        THEN FIRST_ASSUM ACCEPT_TAC]]]);

(* --------------------------------------------------------------------- *)
(* So `R s` specifies a unique number.                                   *)
(* --------------------------------------------------------------------- *)

val CARD_REL_UNIQUE = TAC_PROOF
((strip_conj card_rel_def,
 Term`!n:num. !s:'a->bool. R s n ==> !m. R s m ==> (n = m)`),
 INDUCT_TAC THEN ASM_REWRITE_TAC [] THENL
   [GEN_TAC THEN STRIP_TAC 
       THEN INDUCT_TAC
       THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THENL
       [STRIP_TAC THEN REFL_TAC,
        ASM_REWRITE_TAC[NOT_SUC,FDOM_FEMPTY]],
    GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
    [ASM_REWRITE_TAC [NOT_SUC] 
       THEN CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) 
       THEN CONV_TAC NOT_FORALL_CONV 
       THEN Q.EXISTS_TAC `x`
       THEN ASM_REWRITE_TAC [FDOM_FEMPTY],
     ASM_REWRITE_TAC [INV_SUC_EQ] 
       THEN STRIP_TAC
       THEN IMP_RES_TAC CARD_REL_DEL_LEMMA 
       THEN RES_TAC]]);


(* --------------------------------------------------------------------- *)
(* Now, ?n. R s n if s is finite.                                        *)
(* --------------------------------------------------------------------- *)

val CARD_REL_EXISTS_LEMMA = TAC_PROOF
((strip_conj card_rel_def,
 Term`!f:'a |-> 'b. ?n:num. R (FDOM f) n`),
 INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
 [Q.EXISTS_TAC `0` THEN ASM_REWRITE_TAC[],
  FIRST_ASSUM (CHOOSE_THEN ASSUME_TAC)
    THEN GEN_TAC THEN GEN_TAC 
    THEN Q.ASM_CASES_TAC `FDOM (f:'a |-> 'b) x` THENL
    [IMP_RES_TAC FDOM_EQ_FDOM_FUPDATE 
       THEN Q.EXISTS_TAC `n` 
       THEN ASM_REWRITE_TAC [],
     IMP_RES_TAC FDOM_FDOM_DEL 
       THEN Q.EXISTS_TAC `SUC n`
       THEN ASM_REWRITE_TAC [] 
       THEN Q.EXISTS_TAC `x`
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]);


(* --------------------------------------------------------------------- *)
(* So (@n. R s n) = m iff R s m        (\s.@n.R s n defines a function) *)
(* Proof modified for Version 12 IMP_RES_THEN            [TFM 91.01.23] *)
(* --------------------------------------------------------------------- *)

val CARD_REL_THM = TAC_PROOF
((strip_conj card_rel_def,
  Term`!m (f:'a |-> 'b). (((@n:num. R (FDOM f) n) = m) = R (FDOM f) m)`),
  REPEAT STRIP_TAC 
   THEN STRIP_ASSUME_TAC (SPEC_ALL CARD_REL_EXISTS_LEMMA)
   THEN EQ_TAC THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV 
      THEN Q.EXISTS_TAC `n` 
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC 
      THEN IMP_RES_THEN ASSUME_TAC CARD_REL_UNIQUE 
      THEN CONV_TAC SYM_CONV 
      THEN FIRST_ASSUM MATCH_MP_TAC 
      THEN CONV_TAC SELECT_CONV 
      THEN Q.EXISTS_TAC `n` 
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);


(* --------------------------------------------------------------------- *)
(* Now, prove the existence of the required cardinality function.       *)
(* --------------------------------------------------------------------- *)

val FEMPTY = Term`FEMPTY : 'a |-> 'b`;
val fmap   = Term`f : 'a |-> 'b`;

val DOM_CARD_EXISTS = Q.prove
(`?CARD. (CARD (FDOM ^FEMPTY) = 0) /\
         (!^fmap x y.
           CARD(FDOM (FUPDATE f (x,y))) = 
            if FDOM f x then CARD (FDOM f) 
                        else SUC (CARD (FDOM f)))`,
 STRIP_ASSUME_TAC CARD_REL_EXISTS 
   THEN Q.EXISTS_TAC `\s. @n:num. R s n`
   THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) 
   THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [CARD_REL_THM],
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [IMP_RES_TAC FDOM_EQ_FDOM_FUPDATE THEN ASM_REWRITE_TAC [],
     ASM_REWRITE_TAC [CARD_REL_THM] 
       THEN Q.EXISTS_TAC `x` 
       THEN IMP_RES_TAC FDOM_FDOM_DEL 
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
       THEN CONV_TAC SELECT_CONV 
       THEN REWRITE_TAC [CARD_REL_EXISTS_LEMMA]]]);


(* ----------------------------------------------------------------------- *)
(* Finally let's make this a function over finite maps rather than domains *)
(* ----------------------------------------------------------------------- *)

val CARD_EXISTS = Q.prove
(`?CARD. (CARD ^FEMPTY = 0) /\
       (!^fmap x y.
           CARD(FUPDATE f (x,y)) = if FDOM f x then CARD f else SUC(CARD f))`,
 STRIP_ASSUME_TAC DOM_CARD_EXISTS 
   THEN Q.EXISTS_TAC `\x. CARD (FDOM x)`
   THEN BETA_TAC
   THEN ASM_REWRITE_TAC []);


(* --------------------------------------------------------------------- *)
(* Finally, introduce the CARD function via a constant specification.   *)
(* --------------------------------------------------------------------- *)

val FCARD_DEF = new_specification
                 {name="FCARD_DEF", sat_thm=CARD_EXISTS,
                  consts=[{const_name="FCARD",fixity=Prefix}]};

(* --------------------------------------------------------------------- *)
(* Basic cardinality results.                                            *)
(* --------------------------------------------------------------------- *)

val FCARD_FEMPTY = save_thm("FCARD_FEMPTY",CONJUNCT1 FCARD_DEF);

val FCARD_FUPDATE = save_thm("FCARD_FUPDATE",CONJUNCT2 FCARD_DEF);

val FCARD_0_FEMPTY_LEMMA = Q.prove
(`!^fmap. (FCARD f = 0) ==> (f = FEMPTY)`,
 INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
 [REWRITE_TAC [FCARD_FEMPTY],
  GEN_TAC THEN GEN_TAC 
    THEN REWRITE_TAC [FCARD_FUPDATE] 
    THEN Q.ASM_CASES_TAC `FDOM f x` 
    THEN ASM_REWRITE_TAC [] THENL
    [DISCH_THEN (fn th => FIRST_ASSUM (fn ass => 
                   SUBST_ALL_TAC (MATCH_MP ass th))) 
       THEN POP_ASSUM (CHECK_ASSUME_TAC o (REWRITE_RULE [FDOM_FEMPTY])),
     REWRITE_TAC [NOT_SUC]]]);


val FCARD_0_FEMPTY = Q.store_thm("FCARD_0_FEMPTY",
`!^fmap. (FCARD f = 0) = (f = FEMPTY)`,
GEN_TAC THEN EQ_TAC THENL
[REWRITE_TAC [FCARD_0_FEMPTY_LEMMA],
 DISCH_THEN (fn th => ASM_REWRITE_TAC [th, FCARD_FEMPTY])]);


(*---------------------------------------------------------------------------
         A more useful induction theorem
 ---------------------------------------------------------------------------*)

val exist_map_no_x_rep = (BETA_RULE o BETA_RULE) (Q.prove
(`!f:'a->'b+one. 
   is_fmap f 
    ==> !x. ?f'. !y. 
           is_fmap f' 
        /\ (^update_rep f x y  = ^update_rep f' x y)
        /\ (!x'. f' x' = (if x' = x then INR one else f x'))
        /\ (FDOM (fmap_ABS f') = FDOMDEL (FDOM (fmap_ABS f)) x)`,
 BETA_TAC 
  THEN HO_MATCH_MP_TAC strong_ind
  THEN CONJ_TAC THENL
  [GEN_TAC  
     THEN EXISTS_TAC empty_rep THEN BETA_TAC
     THEN REWRITE_TAC[SYM FEMPTY_DEF,FDOM_FEMPTY,FDOMDEL_FEMPTY,is_fmap_empty]
     THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[],
   BETA_TAC 
     THEN CONV_TAC (DEPTH_CONV FORALL_IMP_CONV)
     THEN GEN_TAC THEN STRIP_TAC
     THEN REPEAT GEN_TAC
     THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
     THEN Q.ASM_CASES_TAC `a = x` THENL
     [Q.EXISTS_TAC `f'` 
        THEN GEN_TAC 
        THEN IMP_RES_TAC is_fmap_REP_ABS
        THEN CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) 
        THEN REWRITE_TAC [FDOMDEL_DEF] 
        THEN ONCE_ASM_REWRITE_TAC [] 
        THEN REWRITE_TAC [FDOMDEL_DEF] 
        THEN POP_ASSUM (fn thm => REWRITE_TAC [REWRITE_RULE [thm, FUPDATE_DEF]
               (SPEC (Term`fmap_ABS (f:'a -> 'b + one)`) FDOM_FUPDATE)]) 
        THEN ASM_REWRITE_TAC [update_same_rep]  
        THEN STRIP_TAC THENL
        [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [],
         GEN_TAC THEN Q.ASM_CASES_TAC `x' = x`
         THEN ASM_REWRITE_TAC []],
      Q.EXISTS_TAC `^update_rep (f':'a -> 'b + one) a b`
         THEN BETA_TAC THEN GEN_TAC 
         THEN IMP_RES_TAC  update_commutes_rep 
         THEN POP_ASSUM (fn thm => REWRITE_TAC [thm]) 
         THEN REPEAT STRIP_TAC THENL
         [MATCH_MP_TAC is_fmap_update THEN ASM_REWRITE_TAC [],
          MATCH_MP_TAC EQ_EXT 
             THEN GEN_TAC THEN BETA_TAC 
             THEN COND_CASES_TAC 
             THEN ASM_REWRITE_TAC [] 
             THEN COND_CASES_TAC THEN REWRITE_TAC [],
          Q.ASM_CASES_TAC `x' = a` THEN ASM_REWRITE_TAC [],
          CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
             THEN ASSUM_LIST (fn ths => REWRITE_TAC 
                    [REWRITE_RULE [MATCH_MP is_fmap_REP_ABS
                             (CONJUNCT1 (SPEC (Term`y:'b`) (el 2 ths))),
                            FUPDATE_DEF] (Q.SPEC `fmap_ABS f'` FDOM_FUPDATE)])
             THEN ASM_REWRITE_TAC [FDOMDEL_DEF] 
             THEN IMP_RES_TAC is_fmap_REP_ABS 
             THEN POP_ASSUM (fn thm => REWRITE_TAC 
                               [REWRITE_RULE [thm, FUPDATE_DEF]
                                (Q.SPEC `fmap_ABS f` FDOM_FUPDATE)]) 
             THEN GEN_TAC 
             THEN Q.ASM_CASES_TAC `x' = a` 
             THEN ASM_REWRITE_TAC []]]]));

val conj_context_lemma = Q.prove 
(`!p q r. (p /\ r /\ (p ==> r ==> q)) ==> (p /\ q /\ r)`,
 REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);

val lemma2 = Q.prove 
(`!(x:'a |-> 'b) y. (x = y) ==> (FCARD x = FCARD y)`,
 REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val CARD_DOM_SUC = Q.prove
(`!n (f:'a |-> 'b). 
    (FCARD f = SUC n)
      ==>
    ?f' x y. ~FDOM f' x /\ (FCARD f' = n) /\ (f = FUPDATE f' (x,y))`,
 GEN_TAC 
  THEN INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
  [REWRITE_TAC [FCARD_FEMPTY, NOT_EQ_SYM (SPEC_ALL NOT_SUC)],
   REPEAT GEN_TAC 
     THEN REWRITE_TAC [FCARD_FUPDATE] 
     THEN COND_CASES_TAC THENL
     [DISCH_TAC 
       THEN STRIP_ASSUME_TAC
             (REWRITE_RULE [fmap_ISO_DEF]
               (Q.SPEC `x` 
                 (MATCH_MP exist_map_no_x_rep
                   (Q.SPEC `f` is_fmap_REP)))) 
       THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `y`)
       THEN Q.EXISTS_TAC `fmap_ABS f'` 
       THEN Q.EXISTS_TAC `x` 
       THEN Q.EXISTS_TAC `y`
       THEN IMP_RES_TAC is_fmap_REP_ABS 
       THEN MATCH_MP_TAC conj_context_lemma 
       THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC [FDOM_DEF, sumTheory.ISL],
        ASM_REWRITE_TAC [FUPDATE_DEF],
        DISCH_TAC 
           THEN ASSUM_LIST (fn ass =>
                DISCH_THEN (fn th =>
                  ASSUME_TAC 
                    (SYM (REWRITE_RULE (FCARD_FUPDATE::INV_SUC_EQ::ass)
                             (MATCH_MP lemma2 th)))))
           THEN ASM_REWRITE_TAC []],
      DISCH_THEN (ASSUME_TAC o REWRITE_RULE [INV_SUC_EQ])
         THEN Q.EXISTS_TAC `f`
         THEN Q.EXISTS_TAC `x` 
         THEN Q.EXISTS_TAC `y`
         THEN ASM_REWRITE_TAC []]]);


val card_induct =
 let val thm1 = BETA_RULE 
       (SPEC (Term`\i. (!f: ('a,'b) fmap. (FCARD f = i) ==> P f)`) INDUCTION)
     val thm2 = GEN_ALL (DISCH_ALL
       (GEN (Term`f1: ('a,'b) fmap`)
            (REWRITE_RULE []
                 (Q.SPECL [`FCARD (f1: ('a,'b) fmap)`,`f1: ('a,'b) fmap`] 
                      (UNDISCH_ALL thm1)))))
 in Q.prove 
 (`!P. P FEMPTY /\
       (!n. (!f:('a,'b) fmap. (FCARD f = n) ==> P f) ==>
            (!f:('a,'b) fmap. (FCARD f = SUC n) ==> P f)) 
       ==>
       !^fmap. P f`,
  REPEAT STRIP_TAC 
     THEN MATCH_MP_TAC thm2 
     THEN CONJ_TAC THENL
     [REWRITE_TAC [FCARD_0_FEMPTY] 
        THEN REPEAT STRIP_TAC 
        THEN ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []])
 end;


val fmap_INDUCT = Q.store_thm("fmap_INDUCT",
`!P. P FEMPTY /\
     (!f. P f ==> !x y. ~FDOM f x ==> P (FUPDATE f (x,y)))
       ==>
     !^fmap. P f`,
GEN_TAC THEN STRIP_TAC 
  THEN MATCH_MP_TAC card_induct 
  THEN ASM_REWRITE_TAC [] 
  THEN REPEAT STRIP_TAC 
  THEN IMP_RES_TAC  CARD_DOM_SUC 
  THEN RES_TAC THEN RES_TAC 
  THEN ASM_REWRITE_TAC []);


(*---------------------------------------------------------------------------
     Equality of finite maps
 ---------------------------------------------------------------------------*)

val FUPDATE_ABSORB_THM = Q.prove 
(`!(f:'a |-> 'b) x y.
    FDOM f x /\ (FAPPLY f x = y) ==> (FUPDATE f (x,y) = f)`,
 INDUCT_THEN fmap_SIMPLE_INDUCT STRIP_ASSUME_TAC 
   THEN REWRITE_TAC [FDOM_FEMPTY] 
   THEN REPEAT STRIP_TAC 
   THEN Q.ASM_CASES_TAC `x = x'` THENL
   [ASM_REWRITE_TAC [FUPDATE_EQ] 
      THEN ASM_CASES_TAC (Term`(y:'b) = y'`) 
      THEN ASM_REWRITE_TAC [] 
      THEN ASSUM_LIST (fn ths => ASSUME_TAC 
             (REWRITE_RULE [el 2 ths, FAPPLY_FUPDATE, el 1 ths] (el 3 ths)))
      THEN UNDISCH_TAC F 
      THEN REWRITE_TAC [],
    IMP_RES_TAC FUPDATE_COMMUTES 
      THEN ASM_REWRITE_TAC [] 
      THEN ASSUM_LIST (fn ths => ASSUME_TAC 
           (REWRITE_RULE [MATCH_MP NOT_EQ_FAPPLY (NOT_EQ_SYM (el 2 ths))]
                    (el 3 ths))) 
      THEN ASSUM_LIST (fn ths => ASSUME_TAC 
             (REWRITE_RULE [FDOM_FUPDATE,(NOT_EQ_SYM (el 3 ths))](el 5 ths)))
      THEN RES_TAC 
      THEN ASM_REWRITE_TAC []]);


val update_eq_not_x = Q.prove 
(`!(f:'a |-> 'b). 
      !x. ?f'. !y. (FUPDATE f (x,y) = FUPDATE f' (x,y)) /\ ~FDOM f' x`,
 INDUCT_THEN fmap_SIMPLE_INDUCT ASSUME_TAC THENL
 [GEN_TAC THEN Q.EXISTS_TAC `FEMPTY` 
   THEN REWRITE_TAC [FDOM_FEMPTY],
  NTAC 3 GEN_TAC
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC`x'`)
    THEN Q.ASM_CASES_TAC `x' = x` THENL
    [Q.EXISTS_TAC `f'`
       THEN ASM_REWRITE_TAC [FUPDATE_EQ] 
       THEN POP_ASSUM (fn th => ASM_REWRITE_TAC [SYM th]),
     Q.EXISTS_TAC `FUPDATE f' (x,y)`
       THEN IMP_RES_TAC FUPDATE_COMMUTES 
       THEN POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [EQ_SYM_EQ])) 
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]);


val lemma9 = BETA_RULE (Q.prove 
(`!x y (f1:('a,'b)fmap) f2. 
   (f1 = f2) ==>
    ((\f.FUPDATE f (x,y)) f1 = (\f. FUPDATE f (x,y)) f2)`,
 REPEAT STRIP_TAC 
   THEN AP_TERM_TAC 
   THEN ASM_REWRITE_TAC []));

val NOT_FDOM_FAPPLY_FEMPTY = Q.store_thm 
("NOT_FDOM_FAPPLY_FEMPTY",
 `!^fmap x. ~FDOM f x ==> (FAPPLY f x = FAPPLY FEMPTY x)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [REWRITE_TAC [],
  REPEAT GEN_TAC 
    THEN STRIP_TAC 
    THEN GEN_TAC 
    THEN Q.ASM_CASES_TAC `x' = x` THENL
    [ASM_REWRITE_TAC [FDOM_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]);

val fmap_EQ_2 = Q.prove 
(`!(f:'a |-> 'b) g. (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) ==> (f = g)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [GEN_TAC 
    THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
    THEN PURE_REWRITE_TAC [FDOM_FEMPTY] 
    THEN PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ, FDOM_F_FEMPTY] 
    THEN REWRITE_TAC [FDOM_F_FEMPTY] 
    THEN STRIP_TAC THEN ASM_REWRITE_TAC [],
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC 
    THEN STRIP_ASSUME_TAC (Q.SPECL [`g`,`x`] update_eq_not_x) 
    THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `FAPPLY g x`)
    THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
    THEN STRIP_TAC 
    THEN ASSUM_LIST (fn ths => ASSUME_TAC
        (REWRITE_RULE [FDOM_FUPDATE] (Q.SPEC `x` (el 2 ths)))) 
    THEN ASSUM_LIST (fn ths => ONCE_REWRITE_TAC 
           [SYM(REWRITE_RULE [el 1 ths]
                 (Q.SPECL [`g`, `x`,`FAPPLY g x`] FUPDATE_ABSORB_THM))]) 
    THEN ASM_REWRITE_TAC [] 
    THEN ASSUM_LIST (fn ths => REWRITE_TAC [
                   ONCE_REWRITE_RULE [EQ_SYM_EQ] (el 2 ths)]) 
    THEN REWRITE_TAC [FAPPLY_FUPDATE] 
    THEN MATCH_MP_TAC lemma9 
    THEN FIRST_ASSUM MATCH_MP_TAC 
    THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
    THEN CONJ_TAC THENL
    [ASSUM_LIST (fn ths => ASSUME_TAC
        (CONV_RULE (DEPTH_CONV FUN_EQ_CONV)
          (SYM (CONJUNCT1 (MATCH_MP fmap_EQ_1 (CONJUNCT1 (el 4 ths))))))) 
       THEN GEN_TAC 
       THEN Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [],
        ASSUM_LIST (fn ths => REWRITE_TAC
             [REWRITE_RULE [FDOM_FUPDATE, el 1 ths] (Q.SPEC `x'` (el 2 ths))]) 
          THEN ASSUM_LIST (fn ths => REWRITE_TAC
               [REWRITE_RULE[FDOM_FUPDATE,el 1 ths] (Q.SPEC`x'` (el 5 ths))])],
     ASSUM_LIST (fn ths => ASSUME_TAC (CONV_RULE (DEPTH_CONV FUN_EQ_CONV)
            (SYM (CONJUNCT2 (MATCH_MP fmap_EQ_1 (CONJUNCT1 (el 4 ths))))))) 
       THEN GEN_TAC 
       THEN Q.ASM_CASES_TAC `x' = x` THENL
       [IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY 
          THEN ASM_REWRITE_TAC [] 
          THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] 
          THEN MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY 
          THEN ASM_REWRITE_TAC [],
        IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN POP_ASSUM (fn th => 
                ASSUME_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ] (Q.SPEC `y` th)))
          THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) 
          THEN ASM_REWRITE_TAC [] 
          THEN ASSUM_LIST (fn ths => REWRITE_TAC [
                   ONCE_REWRITE_RULE[FAPPLY_FUPDATE] (Q.SPEC `x` (el 4 ths))])
          THEN ONCE_ASM_REWRITE_TAC [] 
          THEN IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) 
          THEN REWRITE_TAC []]]]);

val fmap_EQ = Q.store_thm
("fmap_EQ",
 `!(f:'a |-> 'b) g. (FDOM f = FDOM g) /\ (FAPPLY f = FAPPLY g) = (f = g)`,
 REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC [fmap_EQ_1, fmap_EQ_2]);

(*---------------------------------------------------------------------------
       A more useful equality
 ---------------------------------------------------------------------------*)

val fmap_EQ_THM = Q.store_thm
("fmap_EQ_THM",
 `!(f:'a |-> 'b) g.
    (FDOM f = FDOM g) /\ (!x. FDOM f x ==> (FAPPLY f x = FAPPLY g x)) 
                       = 
                    (f = g)`,
 REPEAT STRIP_TAC THEN EQ_TAC THENL
 [STRIP_TAC 
    THEN ASM_REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
    THEN MATCH_MP_TAC EQ_EXT 
    THEN GEN_TAC 
    THEN Q.ASM_CASES_TAC `FDOM f x` THENL
    [RES_TAC,
     ASSUM_LIST (fn ths => ASSUME_TAC (REWRITE_RULE [el 3 ths] (el 1 ths))) 
        THEN IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY 
        THEN ASM_REWRITE_TAC []],
  STRIP_TAC THEN ASM_REWRITE_TAC []]);


(*---------------------------------------------------------------------------
           Submaps
 ---------------------------------------------------------------------------*)

val SUBMAP_DEF = new_infixr_definition 
("SUBMAP_DEF",
 Term`!^fmap g. 
         SUBMAP f g =
          !x. FDOM f x ==> FDOM g x /\ (FAPPLY f x = FAPPLY g x)`, 450);


val SUBMAP_FEMPTY = Q.store_thm
("SUBMAP_FEMPTY",
 `!(f : ('a,'b) fmap). FEMPTY SUBMAP f`,
 REWRITE_TAC [SUBMAP_DEF, FDOM_FEMPTY]);

val SUBMAP_REFL = Q.store_thm
("SUBMAP_REFL",
 `!(f:('a,'b) fmap). f SUBMAP  f`,
 REWRITE_TAC [SUBMAP_DEF]);

val SUBMAP_ANTISYM = Q.store_thm
("SUBMAP_ANTISYM",
 `!(f:('a,'b) fmap) g. (f SUBMAP g /\ g SUBMAP f) = (f = g)`,
 GEN_TAC THEN GEN_TAC THEN EQ_TAC THENL
 [REWRITE_TAC[SUBMAP_DEF, ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ_THM] 
    THEN STRIP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC EQ_EXT 
       THEN GEN_TAC 
       THEN EQ_TAC 
       THEN STRIP_TAC 
       THEN RES_TAC,
     GEN_TAC THEN STRIP_TAC THEN RES_TAC],
  STRIP_TAC THEN ASM_REWRITE_TAC [SUBMAP_REFL]]);


(*---------------------------------------------------------------------------
    Restriction
 ---------------------------------------------------------------------------*)

val res_lemma = Q.prove 
(`!^fmap (r:'a -> bool).
     ?res. (!x. FDOM res x = FDOM f x /\ r x)
       /\  (!x. FAPPLY res x = 
                 if FDOM f x /\ r x then FAPPLY f x else FAPPLY FEMPTY x)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [GEN_TAC 
    THEN Q.EXISTS_TAC `FEMPTY`
    THEN REWRITE_TAC [FDOM_FEMPTY],
  REPEAT STRIP_TAC 
    THEN ASSUM_LIST (fn ths => STRIP_ASSUME_TAC (Q.SPEC `r` (el 2 ths))) 
    THEN ASM_CASES_TAC (Term`(r:'a -> bool) x`) THENL
    [Q.EXISTS_TAC `FUPDATE res (x,y)`
      THEN CONJ_TAC THEN GEN_TAC THENL
      [Q.ASM_CASES_TAC `x' = x` 
          THEN ASM_REWRITE_TAC [FDOM_FUPDATE],
       Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY 
           THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]],
     Q.EXISTS_TAC `res`
       THEN CONJ_TAC THEN GEN_TAC THENL
       [Q.ASM_CASES_TAC `x' = x` 
           THEN ASM_REWRITE_TAC [FDOM_FUPDATE],
        Q.ASM_CASES_TAC `x' = x` THENL
        [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
         IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]]]);


val DRESTRICT_DEF =
  new_specification 
    {name = "DRESTRICT_DEF",
     consts = [{fixity = Prefix, const_name="DRESTRICT"}],
     sat_thm = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) res_lemma};


val DRESTRICT_FEMPTY = Q.store_thm 
("DRESTRICT_FEMPTY",
 `!r. DRESTRICT ^FEMPTY r = FEMPTY`,
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REWRITE_TAC [DRESTRICT_DEF, FDOM_FEMPTY]);

val DRESTRICT_FUPDATE = Q.store_thm
("DRESTRICT_FUPDATE",
 `!^fmap r x y.
     DRESTRICT (FUPDATE f (x,y)) r =
        if r x then FUPDATE (DRESTRICT f r) (x,y) else DRESTRICT f r`,
 REPEAT STRIP_TAC 
   THEN COND_CASES_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] 
   THEN REPEAT STRIP_TAC 
   THEN Q.ASM_CASES_TAC `x' = x`
   THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] 
   THEN TRY (IMP_RES_TAC NOT_EQ_FAPPLY) 
   THEN ASM_REWRITE_TAC [DRESTRICT_DEF]);


val STRONG_DRESTRICT_FUPDATE = Q.store_thm 
("STRONG_DRESTRICT_FUPDATE",
 `!^fmap r x y.
      r x ==> (DRESTRICT (FUPDATE f (x,y)) r
                 = 
               FUPDATE (DRESTRICT f (\v. ~(v=x) /\ r v)) (x,y))`,
 REPEAT STRIP_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONJ_TAC 
   THEN MATCH_MP_TAC EQ_EXT 
   THEN GEN_TAC THENL
   [ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] 
      THEN BETA_TAC 
      THEN Q.ASM_CASES_TAC `x' = x`
      THEN ASM_REWRITE_TAC [],
    Q.ASM_CASES_TAC `x' = x` THENL
    [ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE,DRESTRICT_DEF] 
       THEN BETA_TAC,
     IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN ASM_REWRITE_TAC [DRESTRICT_FUPDATE, DRESTRICT_DEF] 
       THEN BETA_TAC 
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]);


val FDOM_DRESTRICT = Q.store_thm 
("FDOM_DRESTRICT",
 `!^fmap r x. ~r x ==> ~FDOM (DRESTRICT f r) x`,
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [DRESTRICT_DEF]);

val lemma = Q.prove
(`!(a:'a) b. (a = b) ==> (b = a)`,
 REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val NOT_FDOM_DRESTRICT = Q.store_thm
("NOT_FDOM_DRESTRICT",
 `!^fmap x. ~(FDOM f x) ==> (DRESTRICT f (\a. ~(a = x)) = f)`,
 STRIP_TAC 
  THEN ASM_REWRITE_TAC [GSYM fmap_EQ] 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN ASM_REWRITE_TAC [DRESTRICT_DEF] 
  THEN REPEAT STRIP_TAC 
  THEN Q.ASM_CASES_TAC `x' = x` 
  THEN BETA_TAC 
  THEN ASM_REWRITE_TAC [NOT_FDOM_FAPPLY_FEMPTY] 
  THEN Q.ASM_CASES_TAC `FDOM f x'`
  THEN ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC lemma 
  THEN MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY 
  THEN ASM_REWRITE_TAC [NOT_FDOM_FAPPLY_FEMPTY]);


val DRESTRICT_SUBMAP = Q.store_thm
("DRESTRICT_SUBMAP",
 `!^fmap r. (DRESTRICT f r) SUBMAP f`,
 INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
 [REWRITE_TAC [DRESTRICT_FEMPTY, SUBMAP_FEMPTY],
  REPEAT STRIP_TAC 
    THEN REWRITE_TAC [DRESTRICT_FUPDATE] 
    THEN COND_CASES_TAC 
    THEN Q.UNDISCH_TAC `!r. (DRESTRICT f r) SUBMAP f`
    THEN REWRITE_TAC [SUBMAP_DEF] THENL
    [STRIP_TAC THEN GEN_TAC 
       THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
       THEN Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FAPPLY_FUPDATE],
        ASM_REWRITE_TAC [] 
          THEN IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN ASM_REWRITE_TAC []],
     STRIP_TAC THEN GEN_TAC 
        THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
        THEN Q.ASM_CASES_TAC `x' = x` THENL
        [POP_ASSUM SUBST_ALL_TAC 
           THEN DISCH_TAC 
           THEN ASM_REWRITE_TAC [] 
           THEN RES_TAC 
           THEN RES_TAC,
         DISCH_TAC 
           THEN ASM_REWRITE_TAC [] 
           THEN IMP_RES_TAC NOT_EQ_FAPPLY 
           THEN RES_TAC 
           THEN ASM_REWRITE_TAC []]]]);

val DRESTRICT_DRESTRICT = Q.store_thm 
("DRESTRICT_DRESTRICT",
 `!^fmap P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (\x. P x /\ Q x)`,
 HO_MATCH_MP_TAC fmap_INDUCT
   THEN REWRITE_TAC [DRESTRICT_FEMPTY, DRESTRICT_FUPDATE] 
   THEN REPEAT STRIP_TAC 
   THEN Q.ASM_CASES_TAC `P x`
   THEN ASM_CASES_TAC (Term`(Q:'a-> bool) x`) 
   THEN BETA_TAC 
   THEN ASM_REWRITE_TAC [DRESTRICT_FUPDATE]);

val DRESTRICT_IS_FEMPTY = Q.store_thm 
("DRESTRICT_IS_FEMPTY",
 `!r. (!x. ~r x) ==> !^fmap. DRESTRICT f r = FEMPTY`,
 GEN_TAC THEN DISCH_TAC 
   THEN HO_MATCH_MP_TAC fmap_INDUCT
   THEN ASM_REWRITE_TAC  [DRESTRICT_FEMPTY, DRESTRICT_FUPDATE] 
   THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);

val FUPDATE_DRESTRICT = Q.store_thm
("FUPDATE_DRESTRICT",
 `!^fmap x y. FUPDATE f (x,y) = FUPDATE (DRESTRICT f (\v. ~(v = x))) (x,y)`,
 REPEAT STRIP_TAC 
    THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
    THEN CONJ_TAC 
    THEN MATCH_MP_TAC EQ_EXT 
    THEN GEN_TAC THENL
    [ASM_REWRITE_TAC [FDOM_FUPDATE,DRESTRICT_DEF] 
       THEN BETA_TAC 
       THEN Q.ASM_CASES_TAC `x' = x`
       THEN ASM_REWRITE_TAC [],
     Q.ASM_CASES_TAC `x' = x` THENL
     [ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE,DRESTRICT_DEF] 
        THEN BETA_TAC,
      IMP_RES_TAC NOT_EQ_FAPPLY 
        THEN ASM_REWRITE_TAC [DRESTRICT_FUPDATE, DRESTRICT_DEF] 
        THEN BETA_TAC 
        THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
        THEN Q.ASM_CASES_TAC `FDOM f x'`
        THEN ASM_REWRITE_TAC [] 
        THEN MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY 
        THEN ASM_REWRITE_TAC []]]);

val lemma = Q.prove
(`(\x':'a. (~(x' = x) /\ r x') /\ ~(x' = x)) = (\x'. ~(x' = x) /\ r x')`,
 CONV_TAC FUN_EQ_CONV 
   THEN BETA_TAC 
   THEN GEN_TAC 
   THEN EQ_TAC 
   THEN REPEAT STRIP_TAC 
   THEN ASM_REWRITE_TAC [] 
   THEN RES_TAC);


val STRONG_DRESTRICT_FUPDATE_THM = Q.store_thm 
("STRONG_DRESTRICT_FUPDATE_THM",
 `!^fmap r x y.
  DRESTRICT (FUPDATE f (x,y)) r
     = 
  if r x then FUPDATE (DRESTRICT f (\v. ~(v=x) /\ r v)) (x,y)
         else DRESTRICT f (\v. ~(v=x) /\ r v)`,
 REPEAT STRIP_TAC 
   THEN Q.ASM_CASES_TAC `r x` 
   THEN ASM_REWRITE_TAC [STRONG_DRESTRICT_FUPDATE] 
   THEN ONCE_REWRITE_TAC [FUPDATE_DRESTRICT] 
   THEN ASM_REWRITE_TAC [DRESTRICT_FUPDATE, DRESTRICT_DRESTRICT] 
   THEN BETA_TAC 
   THEN ASM_REWRITE_TAC [lemma]);


(*---------------------------------------------------------------------------
     Union of finite maps
 ---------------------------------------------------------------------------*)

val union_lemma = Q.prove 
(`!^fmap g.
     ?union.
       (!x. FDOM union x = FDOM f x \/ FDOM g x) /\
       (!x. FAPPLY union x = if FDOM f x then FAPPLY f x else FAPPLY g x)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [GEN_TAC 
    THEN Q.EXISTS_TAC `g`
    THEN REWRITE_TAC [FDOM_FEMPTY],
  REPEAT STRIP_TAC 
    THEN ASSUM_LIST (fn ths => STRIP_ASSUME_TAC (Q.SPEC `g` (el 2 ths))) 
    THEN Q.EXISTS_TAC `FUPDATE union (x,y)`
    THEN ASM_REWRITE_TAC[FDOM_FUPDATE] 
    THEN CONJ_TAC THEN GEN_TAC THENL
    [Q.ASM_CASES_TAC `x' = x` THEN ASM_REWRITE_TAC[],
     Q.ASM_CASES_TAC `x' = x` THENL
     [ASM_REWRITE_TAC [FAPPLY_FUPDATE],
      IMP_RES_TAC NOT_EQ_FAPPLY 
         THEN ASM_REWRITE_TAC []]]]);


val FUNION_DEF =
  new_specification 
     {name = "FUNION_DEF",
      consts = [{fixity = Prefix, const_name = "FUNION"}],
      sat_thm = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) union_lemma}


val FUNION_FEMPTY_1 = Q.store_thm
("FUNION_FEMPTY_1",
 `!g. FUNION ^FEMPTY g = g`,
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
    THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
    THEN REWRITE_TAC [FUNION_DEF, FDOM_FEMPTY]);

val FUNION_FEMPTY_2 = Q.store_thm 
("FUNION_FEMPTY_2",
 `!f. FUNION f ^FEMPTY = f`,
 REPEAT STRIP_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REWRITE_TAC [FUNION_DEF, FDOM_FEMPTY] 
   THEN STRIP_TAC 
   THEN COND_CASES_TAC THENL
   [REWRITE_TAC[],
    IMP_RES_TAC NOT_FDOM_FAPPLY_FEMPTY THEN ASM_REWRITE_TAC []]);

val FUNION_FUPDATE_1 = Q.store_thm 
("FUNION_FUPDATE_1",
 `!^fmap g x y.
     FUNION (FUPDATE f (x,y)) g = FUPDATE (FUNION f g) (x,y)`,
 REPEAT STRIP_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
      THEN Q.ASM_CASES_TAC `x' = x` 
      THEN ASM_REWRITE_TAC[],
    Q.ASM_CASES_TAC `x' = x` THENL
    [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE]]]);

val FUNION_FUPDATE_2 = Q.store_thm 
("FUNION_FUPDATE_2",
 `!^fmap g x y.
     FUNION f (FUPDATE g (x,y)) = 
        if FDOM f x then FUNION f g 
                    else FUPDATE (FUNION f g) (x,y)`,
 REPEAT STRIP_TAC 
   THEN COND_CASES_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
      THEN Q.ASM_CASES_TAC `x' = x`
      THEN ASM_REWRITE_TAC[],
    Q.ASM_CASES_TAC `x' = x` THENL
    [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE]],
    REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE] 
      THEN Q.ASM_CASES_TAC `x' = x` THEN ASM_REWRITE_TAC[],
    Q.ASM_CASES_TAC `x' = x` THENL
    [ASM_REWRITE_TAC [FUNION_DEF, FAPPLY_FUPDATE, FDOM_FUPDATE],
     IMP_RES_TAC NOT_EQ_FAPPLY 
        THEN ASM_REWRITE_TAC [FUNION_DEF, FDOM_FUPDATE]]]);

val FDOM_FUNION = Q.store_thm
("FDOM_FUNION",
 `!^fmap g x. FDOM (FUNION f g) x = FDOM f x \/ FDOM g x`,
 REPEAT STRIP_TAC THEN REWRITE_TAC [FUNION_DEF]);


val DRESTRICT_FUNION = Q.store_thm
("DRESTRICT_FUNION",
 `!^fmap r q. 
     DRESTRICT f (\x. r x \/ q x) = FUNION (DRESTRICT f r) (DRESTRICT f q)`,
 REPEAT GEN_TAC 
  THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN REWRITE_TAC [DRESTRICT_DEF,FUNION_DEF] 
  THEN BETA_TAC 
  THEN REWRITE_TAC [LEFT_AND_OVER_OR] 
  THEN GEN_TAC 
  THEN Q.ASM_CASES_TAC `FDOM f x`
  THEN ASM_REWRITE_TAC [] 
  THEN Q.ASM_CASES_TAC `r x`
  THEN ASM_REWRITE_TAC []);


val DRESTRICT_TRUE = Q.store_thm
("DRESTRICT_TRUE",
 `!^fmap. DRESTRICT f (\x.T) = f`,
 GEN_TAC 
  THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
  THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
  THEN REWRITE_TAC [DRESTRICT_DEF] 
  THEN GEN_TAC THEN COND_CASES_TAC THENL
  [REWRITE_TAC [] ,
   ONCE_REWRITE_TAC [EQ_SYM_EQ] 
     THEN MATCH_MP_TAC NOT_FDOM_FAPPLY_FEMPTY 
     THEN ASM_REWRITE_TAC []]);


(*---------------------------------------------------------------------------
    "assoc" for finite maps
 ---------------------------------------------------------------------------*)

val lookup_DEF = Q.new_definition 
("lookup_DEF",
 `FLOOKUP ^fmap x = if FDOM f x then INL (FAPPLY f x)
                                else INR one`);


(*---------------------------------------------------------------------------
       Universal quantifier on finite maps
 ---------------------------------------------------------------------------*)

val FEVERY_DEF = Q.new_definition 
("FEVERY_DEF",
 `FEVERY P ^fmap = !x. FDOM f x ==> P (x, FAPPLY f x)`);

val FEVERY_FEMPTY = Q.prove 
(`!P:'a#'b -> bool. FEVERY P FEMPTY`,
 STRIP_TAC 
   THEN REWRITE_TAC [FEVERY_DEF, FDOM_FEMPTY]);

val FEVERY_FUPDATE = Q.prove
(`!P ^fmap x y. 
     FEVERY P (FUPDATE f (x,y)) 
        =
     P (x,y) /\ FEVERY P (DRESTRICT f (\v. ~(x = v)))`,
 REPEAT GEN_TAC 
   THEN REWRITE_TAC [FEVERY_DEF, FDOM_FUPDATE] 
   THEN EQ_TAC 
   THEN REPEAT STRIP_TAC THENL
   [POP_ASSUM(fn th => REWRITE_TAC
               [REWRITE_RULE[FAPPLY_FUPDATE](Q.SPEC `x` th)]),
    REWRITE_TAC [DRESTRICT_DEF] 
      THEN POP_ASSUM (fn th => STRIP_ASSUME_TAC (BETA_RULE
                  (REWRITE_RULE [DRESTRICT_DEF] th)))
      THEN BETA_TAC 
      THEN ASM_REWRITE_TAC [] 
      THEN POP_ASSUM (ASSUME_TAC o NOT_EQ_SYM) 
      THEN IMP_RES_TAC NOT_EQ_FAPPLY 
      THEN POP_ASSUM (fn th => ASSUME_TAC 
            (ONCE_REWRITE_RULE [EQ_SYM_EQ] (Q.SPEC `y` th)))
      THEN ONCE_ASM_REWRITE_TAC [] 
      THEN FIRST_ASSUM MATCH_MP_TAC 
      THEN ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [FAPPLY_FUPDATE],
    ASSUM_LIST (fn ths => ASSUME_TAC (BETA_RULE
           (REWRITE_RULE [DRESTRICT_DEF] (Q.SPEC `x'` (el 2 ths)))))
      THEN Q.PAT_ASSUM `a ==> b` MP_TAC
      THEN Q.ASM_CASES_TAC `x = x'`
      THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] THENL
      [POP_ASSUM (fn th => REWRITE_TAC [SYM th]) THEN ASM_REWRITE_TAC [],
       POP_ASSUM (ASSUME_TAC o NOT_EQ_SYM) 
         THEN IMP_RES_TAC NOT_EQ_FAPPLY 
         THEN ASM_REWRITE_TAC []]]);


val FUPDATE_EXISTING = Q.store_thm 
("FUPDATE_EXISTING",
 `!^fmap v t. FDOM f v /\ (FAPPLY f v = t) = (f = FUPDATE f (v,t))`,
 REPEAT STRIP_TAC 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN EQ_TAC THENL
   [REPEAT STRIP_TAC 
      THEN Q.ASM_CASES_TAC `x = v`
      THEN ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE] 
      THEN IMP_RES_TAC NOT_EQ_FAPPLY 
      THEN ASM_REWRITE_TAC[],
    REPEAT STRIP_TAC 
      THEN ONCE_ASM_REWRITE_TAC [] 
      THEN REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE]]);


(*---------------------------------------------------------------------------
          Finiteness
 ---------------------------------------------------------------------------*)

val FINITE_FMAP = Q.store_thm 
("FINITE_FMAP",
 `!^fmap. 
     ?g. ?n. !x. FDOM f x = ?i. i < n /\ (g i = x)`,
 INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
 [Q.EXISTS_TAC `\x. @y:'a.F` 
    THEN Q.EXISTS_TAC `0` 
    THEN REWRITE_TAC [FDOM_FEMPTY, prim_recTheory.NOT_LESS_0],
  REPEAT STRIP_TAC 
    THEN Q.EXISTS_TAC `\i. if i=n then x:'a else g i`
    THEN Q.EXISTS_TAC `SUC n`
    THEN GEN_TAC 
    THEN REWRITE_TAC [FDOM_FUPDATE] 
    THEN Q.ASM_CASES_TAC `x' = x`
    THEN ASM_REWRITE_TAC [] THENL
    [Q.EXISTS_TAC `n`
       THEN BETA_TAC 
       THEN REWRITE_TAC [LESS_SUC_REFL],
     EQ_TAC THEN STRIP_TAC THENL
     [Q.EXISTS_TAC `i` 
        THEN IMP_RES_TAC LESS_NOT_EQ
        THEN BETA_TAC 
        THEN ASM_REWRITE_TAC [LESS_THM],
      Q.EXISTS_TAC `i`
        THEN Q.UNDISCH_TAC `(\i:num. if i=n then x else g i) i = x'`
        THEN BETA_TAC 
        THEN IMP_RES_TAC LESS_LEMMA1
        THEN ASM_REWRITE_TAC [] THENL
        [DISCH_THEN (ASSUME_TAC o SYM) THEN RES_TAC,
         IMP_RES_TAC LESS_NOT_EQ THEN ASM_REWRITE_TAC []]]]]);



(*---------------------------------------------------------------------------
          Completeness
 ---------------------------------------------------------------------------*)


val rep_DEF = Q.new_definition
("rep",
 `!^fmap. rep f = \x. if FDOM f x then INL (FAPPLY f x) else INR one`);

val rep_empty = Q.prove
(`rep ^FEMPTY = \x. INR one`,
 REWRITE_TAC [rep_DEF,FDOM_FEMPTY]);

val rep_update = Q.prove
(`!^fmap a b. rep (FUPDATE f (a,b)) = \x. if x=a then INL b else rep f x`,
 REPEAT GEN_TAC 
   THEN REWRITE_TAC[rep_DEF] 
   THEN MATCH_MP_TAC EQ_EXT 
   THEN GEN_TAC THEN BETA_TAC 
   THEN Q.ASM_CASES_TAC `x = a` THENL
   [ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE],
    IMP_RES_TAC NOT_EQ_FAPPLY 
      THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]);

val rep_onto = Q.prove
(`!fn:'a -> 'b+one. is_fmap fn ==> ?fm. rep fm = fn`,
 HO_MATCH_MP_TAC ind 
   THEN CONJ_TAC THENL
 [Q.EXISTS_TAC `FEMPTY` THEN REWRITE_TAC [rep_empty],
  REPEAT STRIP_TAC
    THEN Q.EXISTS_TAC `FUPDATE fm (a,b)`
    THEN ASM_REWRITE_TAC [rep_update]]);

val rep_one_one_lemma = Q.prove
(`!^fmap g. (rep f = rep g) ==> (FDOM f = FDOM g)`,
 CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REWRITE_TAC [rep_DEF] 
   THEN BETA_TAC 
   THEN REPEAT STRIP_TAC 
   THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
   THEN POP_ASSUM MP_TAC
   THEN REPEAT COND_CASES_TAC
   THEN ASM_REWRITE_TAC[sum_distinct, GSYM sum_distinct]);

val rep_one_one = Q.prove
(`!^fmap g. (rep f = rep g) ==> (f = g)`,
 REPEAT GEN_TAC 
   THEN DISCH_THEN (fn th => 
     let val lm = MATCH_MP rep_one_one_lemma th 
     in ASSUME_TAC (CONV_RULE FUN_EQ_CONV (REWRITE_RULE [rep_DEF,lm] th))
          THEN ASSUME_TAC lm
     end) 
   THEN REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ_THM] 
   THEN ASM_REWRITE_TAC [] 
   THEN GEN_TAC 
   THEN DISCH_THEN (fn th => FIRST_ASSUM (fn asm => 
         MP_TAC (REWRITE_RULE [th] (BETA_RULE (Q.SPEC `x` asm)))))
   THEN REWRITE_TAC [INR_INL_11]);

val lemma2 = Q.prove
(`!fm:('a,'b)fmap. is_fmap (rep fm)`,
 INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
 [REWRITE_TAC [rep_empty, is_fmap_empty],
  REPEAT STRIP_TAC 
   THEN IMP_RES_TAC is_fmap_update 
   THEN ASM_REWRITE_TAC [rep_update]]);


(*---------------------------------------------------------------------------
      Composition of finite maps
 ---------------------------------------------------------------------------*)

val f_o_f_lemma = Q.prove 
(`!f:'b |-> 'c. 
  !g:'a |-> 'b.
     ?comp. (!x. FDOM comp x = FDOM g x /\ FDOM f (FAPPLY g x))
       /\   (!x. FDOM comp x ==> (FAPPLY comp x = (FAPPLY f (FAPPLY g x))))`,
 GEN_TAC 
  THEN INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
  [Q.EXISTS_TAC `FEMPTY` THEN REWRITE_TAC [FDOM_FEMPTY],
   REPEAT STRIP_TAC 
    THEN Q.ASM_CASES_TAC `FDOM f y` THENL
    [Q.EXISTS_TAC `FUPDATE comp (x, FAPPLY f y)` 
      THEN CONJ_TAC THEN GEN_TAC THENL
      [Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE]],
       Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN IMP_RES_TAC (Q.ISPEC `comp:'a|->'c` NOT_EQ_FAPPLY)
          THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
          THEN STRIP_TAC 
          THEN FIRST_ASSUM MATCH_MP_TAC 
          THEN ASM_REWRITE_TAC []]],
     Q.EXISTS_TAC `comp` 
       THEN CONJ_TAC THEN GEN_TAC THENL
       [Q.ASM_CASES_TAC `x' = x` 
         THEN ASM_REWRITE_TAC [FDOM_FUPDATE,FAPPLY_FUPDATE] 
         THEN IMP_RES_TAC NOT_EQ_FAPPLY 
         THEN ASM_REWRITE_TAC [],
        Q.ASM_CASES_TAC `x' = x` THENL
        [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
         STRIP_TAC 
           THEN IMP_RES_TAC NOT_EQ_FAPPLY 
           THEN RES_TAC 
           THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]]]);


val f_o_f_DEF =
  new_specification 
    {name = "f_o_f_DEF",
     consts = [{fixity = Infixl 500, const_name = "f_o_f"}],
     sat_thm = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) f_o_f_lemma};

val fmap_EQ_TAC =
  PURE_REWRITE_TAC 
   [CONV_RULE(DEPTH_CONV FUN_EQ_CONV) (GSYM fmap_EQ_THM)];

val f_o_f_FEMPTY_1 = Q.store_thm 
("f_o_f_FEMPTY_1",
 `!^fmap. (FEMPTY:('b,'c)fmap) f_o_f f = FEMPTY`,
 GEN_TAC THEN fmap_EQ_TAC 
   THEN REWRITE_TAC [f_o_f_DEF,FDOM_FEMPTY]);

val f_o_f_FEMPTY_2 = Q.store_thm
("f_o_f_FEMPTY_2", 
 `!f:'b|->'c. f f_o_f (FEMPTY:('a,'b)fmap) = FEMPTY`,
    GEN_TAC THEN fmap_EQ_TAC 
      THEN REWRITE_TAC [f_o_f_DEF,FDOM_FEMPTY]);

val o_f_lemma = Q.prove 
(`!f:'b->'c.
  !g:'a|->'b.
    ?comp. (!x. FDOM comp x = FDOM g x) 
      /\   (!x. FDOM comp x ==> (FAPPLY comp x = f (FAPPLY g x)))`,
 GEN_TAC 
  THEN INDUCT_THEN fmap_INDUCT STRIP_ASSUME_TAC THENL
  [Q.EXISTS_TAC `FEMPTY` THEN REWRITE_TAC [FDOM_FEMPTY],
   REPEAT STRIP_TAC 
     THEN Q.EXISTS_TAC `FUPDATE comp (x, f y)`
     THEN CONJ_TAC 
     THEN GEN_TAC 
     THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
     THEN Q.ASM_CASES_TAC `x' = x` THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE],
      IMP_RES_TAC NOT_EQ_FAPPLY 
        THEN IMP_RES_TAC (Q.ISPEC `comp:'a|->'c` NOT_EQ_FAPPLY)
        THEN ASM_REWRITE_TAC [] 
        THEN STRIP_TAC 
        THEN FIRST_ASSUM MATCH_MP_TAC 
        THEN ASM_REWRITE_TAC []]]);

val o_f_DEF =
   new_specification 
     {name = "o_f_DEF",
      consts = [{fixity = Infixl 500, const_name = "o_f"}],
      sat_thm = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) o_f_lemma};


val o_f_FDOM = Q.store_thm
("o_f_FDOM",
 `!f:'b -> 'c. !g:'a |->'b. !x. FDOM  g x = FDOM (f o_f g) x`,
REWRITE_TAC [o_f_DEF]);

val o_f_FAPPLY = Q.store_thm
("o_f_APPLY",
 `!f:'b->'c. !g:('a,'b) fmap. 
   !x. FDOM  g x ==> (FAPPLY (f o_f g) x = f (FAPPLY g x))`,
 REPEAT STRIP_TAC 
  THEN STRIP_ASSUME_TAC (Q.SPECL [`f:'b -> 'c`, `g:('a,'b) fmap`] o_f_DEF)
  THEN FIRST_ASSUM MATCH_MP_TAC 
  THEN ASM_REWRITE_TAC []);


(*---------------------------------------------------------------------------
          Range of a finite map
 ---------------------------------------------------------------------------*)

val FRANGE_DEF = Q.new_definition
("FRANGE_DEF",
 `FRANGE ^fmap y = ?x. FDOM f x /\ (FAPPLY f x = y)`);

val FRANGE_FEMPTY = Q.store_thm 
("FRANGE_FEMPTY",
 `!x. ~FRANGE ^FEMPTY x`,
 REWRITE_TAC [FRANGE_DEF, FDOM_FEMPTY]);

val FRANGE_FUPDATE = Q.store_thm 
("FRANGE_FUPDATE",
 `!^fmap x y b.
     FRANGE (FUPDATE f (x,y)) b 
       =
     (y = b) \/ FRANGE (DRESTRICT f (\a. ~(a = x))) b`,
 REPEAT GEN_TAC 
   THEN REWRITE_TAC [FRANGE_DEF,FDOM_FUPDATE,DRESTRICT_DEF] 
   THEN BETA_TAC 
   THEN EQ_TAC THEN STRIP_TAC THENL
   [Q.PAT_ASSUM `p = q` MP_TAC
      THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] 
      THEN DISCH_TAC THEN ASM_REWRITE_TAC [],
    Q.ASM_CASES_TAC `x' = x` THENL
    [Q.PAT_ASSUM `FAPPLY p q = z` MP_TAC
       THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] 
       THEN DISCH_TAC THEN ASM_REWRITE_TAC [],
     DISJ2_TAC 
       THEN Q.EXISTS_TAC `x'` 
       THEN ASM_REWRITE_TAC [] 
       THEN IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN POP_ASSUM (ASSUME_TAC o Q.SPECL [`y:'b`, `f:('a,'b)fmap`]
                        o ONCE_REWRITE_RULE [EQ_SYM_EQ]) 
       THEN ASM_REWRITE_TAC []],
    Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE],
    Q.EXISTS_TAC `x'`
       THEN IMP_RES_TAC NOT_EQ_FAPPLY 
       THEN ASM_REWRITE_TAC [] 
       THEN Q.PAT_ASSUM `p = q` MP_TAC
       THEN ASM_REWRITE_TAC []]);

val SUBMAP_FRANGE = Q.store_thm
("SUBMAP_FRANGE",
 `!^fmap g. f SUBMAP g ==> !x. FRANGE f x ==> FRANGE g x`,
 REPEAT GEN_TAC 
   THEN REWRITE_TAC [SUBMAP_DEF,FRANGE_DEF] 
   THEN REPEAT STRIP_TAC 
   THEN Q.EXISTS_TAC `x'`
   THEN RES_TAC 
   THEN POP_ASSUM SUBST_ALL_TAC 
   THEN ASM_REWRITE_TAC []);


(*---------------------------------------------------------------------------
        Range restriction
 ---------------------------------------------------------------------------*)

val ranres_lemma = Q.prove 
(`!^fmap (r:'b -> bool).
    ?res. (!x. FDOM res x = FDOM f x /\ r (FAPPLY f x))
      /\  (!x. FAPPLY res x =
                 if FDOM f x /\ r (FAPPLY f x)
                   then FAPPLY f x
                   else FAPPLY FEMPTY x)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [GEN_TAC 
    THEN Q.EXISTS_TAC `FEMPTY`
    THEN REWRITE_TAC [FDOM_FEMPTY],
  REPEAT STRIP_TAC 
    THEN ASSUM_LIST(fn ths => STRIP_ASSUME_TAC(Q.SPEC `r:'b->bool` (el 2 ths)))
    THEN Q.ASM_CASES_TAC `r y` THENL
    [Q.EXISTS_TAC `FUPDATE res (x,y)`
       THEN CONJ_TAC THEN GEN_TAC 
       THEN Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE],
        ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE]],
     Q.EXISTS_TAC `res`
       THEN CONJ_TAC THEN GEN_TAC
       THEN Q.ASM_CASES_TAC `x' = x` THENL
       [ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE],
        ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE],
        IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE]]]]);

val ranres_lemma = Q.prove 
(`!^fmap (r:'b -> bool).
    ?res. (!x. FDOM res x = FDOM f x /\ r (FAPPLY f x))
      /\  (!x. FAPPLY res x =
                 if FDOM f x /\ r (FAPPLY f x)
                   then FAPPLY f x
                   else FAPPLY FEMPTY x)`,
 INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
 [GEN_TAC 
    THEN Q.EXISTS_TAC `FEMPTY`
    THEN REWRITE_TAC [FDOM_FEMPTY],
  REPEAT STRIP_TAC 
    THEN ASSUM_LIST(fn ths => STRIP_ASSUME_TAC(Q.SPEC `r:'b->bool` (el 2 ths)))
    THEN Q.ASM_CASES_TAC `r y` THENL
    [Q.EXISTS_TAC `FUPDATE res (x,y)`, Q.EXISTS_TAC `res`]
    THEN CONJ_TAC THEN GEN_TAC 
    THEN Q.ASM_CASES_TAC `x' = x` THEN
    ((ASM_REWRITE_TAC [FDOM_FUPDATE, FAPPLY_FUPDATE] THEN NO_TAC)
       ORELSE 
     (IMP_RES_TAC NOT_EQ_FAPPLY THEN ASM_REWRITE_TAC [FDOM_FUPDATE]))]);


val RRESTRICT_DEF =
   new_specification 
     {name = "RRESTRICT_DEF",
      consts = [{fixity = Prefix, const_name = "RRESTRICT"}],
      sat_thm = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) ranres_lemma};

val RRESTRICT_FEMPTY = Q.store_thm 
("RRESTRICT_FEMPTY",
 `!r.RRESTRICT ^FEMPTY r = FEMPTY`,
 REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
   THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
   THEN REWRITE_TAC [RRESTRICT_DEF, FDOM_FEMPTY]);

val RRESTRICT_FUPDATE = Q.store_thm
("RRESTRICT_FUPDATE",
`!^fmap r x y.
    RRESTRICT (FUPDATE f (x,y)) r =
      if r y then FUPDATE (RRESTRICT f r) (x,y)
             else RRESTRICT (DRESTRICT f (\a. ~(a = x))) r`,
 REPEAT STRIP_TAC 
   THEN COND_CASES_TAC THENL
   [REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
      THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
      THEN ASM_REWRITE_TAC [FDOM_FUPDATE,RRESTRICT_DEF,DRESTRICT_DEF] 
      THEN REPEAT STRIP_TAC 
      THEN Q.ASM_CASES_TAC `x' = x`
      THEN ASM_REWRITE_TAC [FAPPLY_FUPDATE] 
      THEN TRY (IMP_RES_TAC NOT_EQ_FAPPLY) 
      THEN ASM_REWRITE_TAC [RRESTRICT_DEF],
    REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] fmap_EQ] 
      THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) 
      THEN ASM_REWRITE_TAC [FDOM_FUPDATE,RRESTRICT_DEF,DRESTRICT_DEF] 
      THEN REPEAT STRIP_TAC 
      THEN Q.ASM_CASES_TAC `x' = x`
      THEN BETA_TAC THENL
      [ASM_REWRITE_TAC [FAPPLY_FUPDATE],
       IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN ASM_REWRITE_TAC [RRESTRICT_DEF] 
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [],
       ASM_REWRITE_TAC [FAPPLY_FUPDATE],
       IMP_RES_TAC NOT_EQ_FAPPLY 
          THEN ASM_REWRITE_TAC [RRESTRICT_DEF] 
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] 
          THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [DE_MORGAN_THM])
          THEN ASM_REWRITE_TAC [] 
          THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] 
          THEN POP_ASSUM (fn th => ASSUME_TAC
                 (REWRITE_RULE [CONJUNCT1 th] (CONJUNCT2 th))) 
          THEN RES_TAC]]);


(*---------------------------------------------------------------------------
       Functions as finite maps.

   We first define a function to test if a predicate is true for a finite
   number of elements. We should actually be able to take this from
   pred_setTheory.
 ---------------------------------------------------------------------------*)

val (rules,FINITE_PRED_INDUCT,cases) = 
 Hol_reln `FINITE_PRED (\a. F)
      /\  (!f a. FINITE_PRED f ==> FINITE_PRED (\x. (x=a) \/ f x))`;

val rules_list as [FINITE_PRED_EMPTY, FINITE_PRED_UPDATE] = CONJUNCTS rules;

val ffmap_lemma = Q.prove 
(`!(f:'a -> 'b) (P: 'a -> bool).
     FINITE_PRED P ==>
        ?ffmap. (!x. FDOM ffmap x = P x) 
           /\   (!x. P x ==> (FAPPLY ffmap x = f x))`,
 GEN_TAC 
   THEN HO_MATCH_MP_TAC FINITE_PRED_INDUCT 
   THEN CONJ_TAC THENL
   [Q.EXISTS_TAC `FEMPTY`
     THEN BETA_TAC 
     THEN REWRITE_TAC [FDOM_FEMPTY],
    REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `FUPDATE ffmap (a, f a)`
      THEN BETA_TAC 
      THEN ASM_REWRITE_TAC [FDOM_FUPDATE] 
      THEN STRIP_TAC 
      THEN Q.ASM_CASES_TAC `x = a` THENL
      [ASM_REWRITE_TAC [FAPPLY_FUPDATE],
       ASM_REWRITE_TAC [] 
         THEN DISCH_TAC 
         THEN RES_TAC 
         THEN IMP_RES_TAC NOT_EQ_FAPPLY 
         THEN ASM_REWRITE_TAC []]]);


val FUN_FMAP_DEF =
   new_specification 
     {name = "FUN_FMAP_DEF",
      consts = [{fixity = Prefix, const_name = "FUN_FMAP"}],
      sat_thm = CONV_RULE
                  (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC
                   ONCE_DEPTH_CONV SKOLEM_CONV) ffmap_lemma};


(*---------------------------------------------------------------------------
         Composition of finite map and function
 ---------------------------------------------------------------------------*)

val f_o_DEF = new_infixl_definition
("f_o_DEF",
Term`f_o (f:('b,'c)fmap) (g:'a->'b) 
      = f f_o_f (FUN_FMAP g (\x. FDOM f (g x)))`, 500);

val FDOM_f_o = Q.store_thm 
("FDOM_f_o",
 `!(f:'b|->'c)  (g:'a->'b).
     FINITE_PRED (\x. FDOM f (g x)) 
       ==>
     !x. FDOM (f f_o g) x = FDOM f (g x)`,
 REPEAT GEN_TAC 
   THEN DISCH_THEN (fn th => STRIP_ASSUME_TAC 
          (BETA_RULE (Q.SPEC `g` (MATCH_MP FUN_FMAP_DEF th)))) 
   THEN ASM_REWRITE_TAC [f_o_DEF,f_o_f_DEF ] 
   THEN GEN_TAC 
   THEN EQ_TAC 
   THEN STRIP_TAC 
   THEN RES_TAC 
   THEN ASM_REWRITE_TAC []);


val FAPPLY_f_o = Q.store_thm 
("FAPPLY_f_o",
 `!(f:'b |-> 'c)  (g:'a-> 'b).
    FINITE_PRED (\x. FDOM f (g x)) 
      ==>
    !x. FDOM (f f_o g) x ==> (FAPPLY (f f_o g) x = FAPPLY f (g x))`,
 REPEAT GEN_TAC 
    THEN DISCH_THEN (fn th => STRIP_ASSUME_TAC 
            (BETA_RULE (Q.SPEC `g` (MATCH_MP FUN_FMAP_DEF th)))
    THEN STRIP_ASSUME_TAC (MATCH_MP FDOM_f_o th)) 
    THEN GEN_TAC 
    THEN DISCH_THEN (fn th => ASSUME_TAC (REWRITE_RULE [f_o_DEF] th) 
            THEN FIRST_ASSUM(fn asm => ASSUME_TAC(EQ_MP (Q.SPEC `x` asm) th)))
    THEN STRIP_ASSUME_TAC f_o_f_DEF 
    THEN RES_TAC 
    THEN ASM_REWRITE_TAC [f_o_DEF]);


val FINITE_PRED_11 = Q.store_thm
("FINITE_PRED_11",
 `!(g:'a -> 'b). 
      (!x y. (g x = g y) = (x = y)) 
        ==>
      !f:'b|->'c. FINITE_PRED (\x. FDOM f (g x))`,
 GEN_TAC 
   THEN DISCH_TAC 
   THEN INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL
   [REWRITE_TAC [FDOM_FEMPTY, FINITE_PRED_EMPTY],
    REWRITE_TAC [FDOM_FUPDATE] 
       THEN REPEAT STRIP_TAC 
       THEN Q.ASM_CASES_TAC `?y. x = g y` THENL
       [POP_ASSUM STRIP_ASSUME_TAC 
          THEN IMP_RES_TAC FINITE_PRED_UPDATE 
          THEN POP_ASSUM (ASSUME_TAC o BETA_RULE) 
          THEN ASM_REWRITE_TAC [],
        POP_ASSUM (ASSUME_TAC o GSYM o CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV))
          THEN ASM_REWRITE_TAC []]]);


val _ = export_theory();


end;
