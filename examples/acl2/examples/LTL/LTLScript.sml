(*****************************************************************************)
(* Create "LTLTheory"                                                        *)
(*                                                                           *)
(* References:                                                               *)
(*                                                                           *)
(*  - Sandip Ray, John Matthews, Mark Tuttle, "Certifying Compositional      *)
(*    Model Checking Algorithms in ACL2".                                    *)
(*                                                                           *)
(*  - Edmund M. Clarke, Jr., Orna Grumberg, Doron A. Peled, "Model           *)
(*    Checking", The MIT Press, 1999.                                        *)
(*                                                                           *)
(*****************************************************************************)

(*  Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)
map load 
 ["pred_setLib","stringLib","finite_mapTheory"];
open
 pred_setTheory stringLib finite_mapTheory;
quietdec := false;                                   (* Restore output       *)
*)

(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)



(******************************************************************************
* Start a new theory called LTL
******************************************************************************)

val _ = new_theory "LTL";

(******************************************************************************
* Syntax
******************************************************************************)

(******************************************************************************
* LTL formulas are polymorphic: have type ``:'prop formula``
******************************************************************************)
val formula_def =
 Hol_datatype
  `formula = TRUE
           | FALSE
           | ATOMIC     of 'prop 
           | NOT        of formula
           | AND        of formula => formula
           | OR         of formula => formula
           | SOMETIMES  of formula
           | ALWAYS     of formula
           | NEXT       of formula
           | UNTIL      of formula => formula
           | WEAK_UNTIL of formula => formula`;

(******************************************************************************
* Semantics
******************************************************************************)

(******************************************************************************
* A Kripke structure is a 4-tuple (S,R,L,S0) represented as a record:
* 
*  - S  : 'state set              a set of states
*  - R  : ('state # 'state) set   a transition relation
*  - L  : 'state -> 'prop set     maps a state to the true propositions in it
*  - S0 : 'state set              a subset of S, the initial states
*
* The type parameters are: ``: ('state,'prop)model``
* N.B. terms that follow are not contrained to use type variables 'state
* and 'prop, but may use 'a, 'b etc or whatever typechecking assigns.
******************************************************************************)

(******************************************************************************
* Annoyance fix: stop ``I`` and ``S`` parsing to the identity and S-combinators
******************************************************************************)
val _ = hide "I";
val _ = hide "S";


(******************************************************************************
* A Kripke structure has type ``: ('prop,'state)model``
******************************************************************************)
val model_def =
 Hol_datatype
  `model = 
    <| S: 'state set;
       R: ('state # 'state) set;
       L: 'state -> 'prop set;
       S0:'state set |>`;

(******************************************************************************
* Requirements for a model to be a well-formed Kripke structure
* (Note: the transition relation is not required to be total)
******************************************************************************)
val MODEL_def =
 Define
  `MODEL M =
    M.S0 SUBSET M.S /\ (!s s'. (s,s') IN M.R ==> s IN M.S /\ s' IN M.S)`;

(******************************************************************************
* PATH M s p is true iff p is a path of model M starting from s
******************************************************************************)
val PATH_def = 
 Define 
  `PATH M s p = (p 0 = s) /\ !i. M.R(p(i),p(i+1))`;

(******************************************************************************
* SUFFIX p in is the ith suffix of p
******************************************************************************)
val SUFFIX_def = 
 Define 
  `SUFFIX p i = \j. p(i+j)`;

(******************************************************************************
* SEM M p f defines the truth of formula f in path p of model M
******************************************************************************)
val SEM_def =
 Define
  `(SEM M p TRUE = T)
   /\
   (SEM M p FALSE = F)
   /\
   (SEM M p (ATOMIC a) = M.L (p 0) a)
   /\
   (SEM M p (NOT f) = ~(SEM M p f))
   /\
   (SEM M p (AND f1 f2) = SEM M p f1 /\ SEM M p f2)
   /\
   (SEM M p (OR f1 f2) = SEM M p f1 \/ SEM M p f2)
   /\
   (SEM M p (SOMETIMES f) = ?i. SEM M (SUFFIX p i) f)
   /\
   (SEM M p (ALWAYS f) = !i. SEM M (SUFFIX p i) f)
   /\
   (SEM M p (NEXT f) = SEM M (SUFFIX p 1) f)
   /\
   (SEM M p (UNTIL f1 f2) =
      ?i. SEM M (SUFFIX p i) f2 /\ !j. j < i ==> SEM M (SUFFIX p j) f1)
   /\
   (SEM M p (WEAK_UNTIL f1 f2) = 
     (?i. SEM M (SUFFIX p i) f2 /\ !j. j < i ==> SEM M (SUFFIX p j) f1)
     \/ 
     !i. SEM M (SUFFIX p i) f1)`;

(* M |= f *)
val SAT_def =
 Define
  `SAT M f = !p. (p 0) IN M.S0 /\ PATH M (p 0) p ==> SEM M p f`;

(* Definition of a bisimulation *)
val BISIM_def =
 Define
  `BISIM M M' B =
    !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
           ==>
           (M.L s = M'.L s')
           /\
           (!s1. s1 IN M.S /\ M.R(s,s1) 
                 ==> 
                 ?s1'. s1' IN M'.S /\ M'.R(s',s1') /\ B(s1,s1'))
           /\
           (!s1'. s1' IN M'.S /\ M'.R(s',s1') 
                 ==> 
                 ?s1. s1 IN M.S /\ M.R(s,s1) /\ B(s1,s1'))`;

(* Definition of bisimulation equivalent *)
val BISIM_EQ_def =
 Define
  `BISIM_EQ M M' = 
    ?B. BISIM M M' B
        /\ 
        (!s0. s0 IN M.S0 ==> ?s0'. s0' IN M'.S0 /\ B(s0,s0'))
        /\ 
        (!s0'. s0' IN M'.S0 ==> ?s0. s0 IN M.S0 /\ B(s0,s0'))`;

(* Preparation for Lemma 1, p 10 of Ray et al. 
   Lemma 31, p 172 of Clarke et al. 
*)
val Lemma1a =
 prove
  (``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B
      ==>
      !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s') 
      ==> !p. PATH M s p ==> ?p'. PATH M' s' p' /\ !i. B(p i, p' i)``,
   RW_TAC std_ss [IN_DEF,PATH_def]
    THEN Q.EXISTS_TAC `PRIM_REC s' (\t n. @t'. M'.R(t,t') /\ B(p(n+1),t'))`    
    THEN SIMP_TAC std_ss [prim_recTheory.PRIM_REC_THM,GSYM FORALL_AND_THM]
    THEN Induct
    THEN FULL_SIMP_TAC pure_ss [DECIDE ``n + 1 = SUC n``,PATH_def]
    THEN RW_TAC pure_ss [prim_recTheory.PRIM_REC_THM]
    THEN FULL_SIMP_TAC pure_ss 
          (map (SIMP_RULE std_ss [IN_DEF]) [MODEL_def,BISIM_def,PATH_def])
    THEN METIS_TAC[]);

(* My original proof
val Lemma1b =
 prove
  (``MODEL M /\ MODEL M' /\ BISIM M M' B
     ==>
     !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s') 
            ==> !p'. PATH M' s' p' ==> ?p. PATH M s p /\ !i. B(p i, p' i)``,
   RW_TAC std_ss [IN_DEF]
    THEN Q.EXISTS_TAC `PRIM_REC s (\t n. @t'. M.R(t,t') /\ B(t',p'(n+1)))`    
    THEN SIMP_TAC std_ss 
          [PATH_def,prim_recTheory.PRIM_REC_THM,GSYM FORALL_AND_THM]
    THEN Induct
    THEN FULL_SIMP_TAC pure_ss [DECIDE ``n + 1 = SUC n``,PATH_def]
    THEN RW_TAC pure_ss [prim_recTheory.PRIM_REC_THM]
    THEN FULL_SIMP_TAC pure_ss 
          (map (SIMP_RULE std_ss [IN_DEF]) [MODEL_def,BISIM_def,PATH_def])
    THEN METIS_TAC[]);
*)

(* Matt's proof by symmetry *)
val BISIM_SYM =
 store_thm
  ("BISIM_SYM",
   ``!M M' B. BISIM M M' B ==> BISIM M' M (\(x,y). B(y,x))``,
   RW_TAC std_ss [BISIM_def]
    THEN METIS_TAC[]);

val Lemma1b =
 prove
  (``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B
       ==>
       !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s') 
              ==> !p'. PATH M' s' p' ==> ?p. PATH M s p /\ !i. B(p i, p' i)``,
    METIS_TAC
     [BISIM_SYM,
       pairLib.GEN_BETA_RULE
        (ISPECL
          [``M':('a, 'c) model``, ``M:('a, 'b) model``, 
           ``\(x,y). (B:'b # 'c -> bool)(y,x)``]
          Lemma1a)]);

(* Lemma 1, p 10 of Ray et al. Lemma 31, p 172 of Clarke et al. *)
val Lemma1 = 
 time store_thm
  ("Lemma1",
    ``!M M' B.
       MODEL M /\ MODEL M' /\ BISIM M M' B
        ==>
        !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
               ==> 
               (!p. PATH M s p ==> ?p'. PATH M' s' p' /\ !i. B(p i, p' i))
               /\
               (!p'. PATH M' s' p' ==> ?p. PATH M s p /\ !i. B(p i, p' i))``,
   METIS_TAC[Lemma1a,Lemma1b]);

(* Preparation for Lemma  2, p 10 of Ray et al. 
   Lemma 32, p 172 of Clarke et al. 
*)
val BISIM_SUFFIX =
 store_thm
  ("BISIM_SUFFIX",
   ``!p p'. (!i. B(p i, p' i)) ==> !n. (!i. B(SUFFIX p n i,SUFFIX p' n i))``,
   RW_TAC std_ss [SUFFIX_def]
    THEN Induct_on `n`
    THEN RW_TAC arith_ss []);

val PATH_SUFFIX =
 store_thm
  ("PATH_SUFFIX",
   ``!M p. PATH M s p ==> !n. PATH M (p n) (SUFFIX p n)``,
   RW_TAC std_ss [PATH_def,SUFFIX_def]
    THEN METIS_TAC[arithmeticTheory.ADD_ASSOC]);

val PATH_SUFFIX_IN =
 store_thm
  ("PATH_SUFFIX_IN",
   ``!M s p. MODEL M /\ M.S s /\ PATH M s p ==> !n i. M.S (SUFFIX p n i)``,
   RW_TAC std_ss [MODEL_def,PATH_def,SUFFIX_def,IN_DEF]
    THEN Induct_on `n` THEN Induct_on `i`
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC arith_ss [DECIDE ``n + 1 = SUC n``]
    THEN METIS_TAC[]);

(* Lemma  2, p 10 of Ray et al. Lemma 32, p 172 of Clarke et al. *)
(* runtime: 4978.813s,    gctime: 743.494s,     systime: 9.298s. *)
val Lemma2 =
  time store_thm
  ("Lemma2",
   ``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B
       ==>
       !f s s'. s IN M.S /\ s' IN M'.S /\ B(s,s') 
                ==>  !p p'. PATH M s p /\ PATH M' s' p' /\ (!i. B(p i, p' i))
                            ==> (SEM M p f = SEM M' p' f)``,
   REPEAT GEN_TAC
    THEN SIMP_TAC std_ss [IN_DEF]
    THEN STRIP_TAC
    THEN Induct
    THEN RW_TAC std_ss [SEM_def]
    THEN METIS_TAC
          [IN_DEF,MODEL_def,BISIM_def,PATH_def,BISIM_SUFFIX,
           PATH_SUFFIX,PATH_SUFFIX_IN]);

(* Theorem 1, p 10 of Ray et al. Theorem 14, p 175 of Clarke et al. *)
val Theorem1 =
 time store_thm
  ("Theorem1",
   ``!M M'. MODEL M /\ MODEL M' /\ BISIM_EQ M M' ==> !f. SAT M f = SAT M' f``,
   RW_TAC std_ss [BISIM_EQ_def,SAT_def,IN_DEF]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN RES_TAC
    THENL
     [`s0 IN M.S /\ (p 0) IN M'.S` 
       by METIS_TAC[IN_DEF,pred_setTheory.SUBSET_DEF,MODEL_def]
       THEN `!p'. PATH M' (p 0) p' ==> ?p. PATH M s0 p /\ !i. B (p i,p' i)` 
        by METIS_TAC[Lemma1]
       THEN RES_TAC
       THEN `SEM M p' f` by METIS_TAC[PATH_def]
       THEN METIS_TAC[Lemma2,IN_DEF],
      `s0' IN M'.S /\ (p 0) IN M.S` 
        by METIS_TAC[IN_DEF,pred_setTheory.SUBSET_DEF,MODEL_def]
       THEN `?p'. PATH M' s0' p' /\ !i. B (p i,p' i)` by METIS_TAC[Lemma1]
       THEN RES_TAC
       THEN `SEM M' p' f` by METIS_TAC[PATH_def]
       THEN METIS_TAC[Lemma2,IN_DEF]]);

val _ = export_theory();
