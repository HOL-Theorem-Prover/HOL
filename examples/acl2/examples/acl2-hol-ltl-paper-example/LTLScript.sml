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

(* Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)
map load
 ["pred_setLib","stringLib","finite_mapTheory"];
open
 pred_setTheory pred_setLib stringLib finite_mapTheory;
quietdec := false;                                   (* Restore output       *)
*)

(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory pred_setLib;

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
  `formula = TRUE  (* one value satisfying ltl-constantp *)
           | FALSE (* one value satisfying ltl-constantp *)
           | ATOMIC     of 'prop (* in ACL2: a symbol satisfying ltl-variablep *)
           | NOT        of formula (* ~ *)
           | AND        of formula => formula (* & *)
           | OR         of formula => formula (* + *)
           | SOMETIMES  of formula (* F *)
           | ALWAYS     of formula (* G *)
           | NEXT       of formula (* X *)
           | UNTIL      of formula => formula (* U *)
           | WEAK_UNTIL of formula => formula`; (* W *)

val Atoms_def =
 Define
  `(Atoms TRUE = {})
   /\
   (Atoms FALSE = {})
   /\
   (Atoms (ATOMIC a) = {a})
   /\
   (Atoms (NOT f) = Atoms f)
   /\
   (Atoms (AND f1 f2) = Atoms f1 UNION Atoms f2)
   /\
   (Atoms (OR f1 f2) = Atoms f1 UNION Atoms f2)
   /\
   (Atoms (SOMETIMES f) = Atoms f)
   /\
   (Atoms (ALWAYS f) = Atoms f)
   /\
   (Atoms (NEXT f) = Atoms f)
   /\
   (Atoms (UNTIL f1 f2) = Atoms f1 UNION Atoms f2)
   /\
   (Atoms (WEAK_UNTIL f1 f2) = Atoms f1 UNION Atoms f2)`;

(******************************************************************************
* Semantics
******************************************************************************)

(******************************************************************************
* A Kripke structure is a 4-tuple (S,S0,R,L) represented as a record:
*
*  - S  : 'state set              a set of states
*  - S0 : 'state set              a subset of S thare the initial states
*  - R  : ('state # 'state) set   a transition relation
*  - L  : 'state -> 'prop set     maps a state to the true propositions in it
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
* A Kripke structure has type ``: ('prop,'state)model`` (Clarke et al. p13)
******************************************************************************)
val model_def =
 Hol_datatype
  `model =
    <| S: 'state set; 
      (* set of all states *)
       S0:'state set ;
      (* initial states *)
       R: ('state # 'state) set; 
      (* transition relation *)
       L: 'state -> 'prop set
      (* maps a state to the set of propositions true in that state *)
    |>`; 

(******************************************************************************
* Requirements for a model to be a well-formed Kripke structure
* (Note: the transition relation is here not required to be total)
******************************************************************************)
val MODEL_def =
 Define
  `MODEL M =
    M.S0 SUBSET M.S /\ (!s s'. s IN M.S /\ (s,s') IN M.R ==> s' IN M.S)`;

(* record: ACL2 finite function as a "normalized" alist, where *)
(* an alist is ((key0 . val0) (key1 . val1) ... (keyn . valn)) *)

(* See circuit-modelp in ACL2, which recognizes valid Kripke structures:

(defun circuit-modelp (m)
  (and ; Well-formed state: range of a state is contained in {T, NIL}
       (only-evaluations-p (states m) (variables m))
       ; Every well-formed state is in (states m)
       (all-evaluations-p (states m) (variables m))
       ; Only known props are mapped by a state
       (strict-evaluation-list-p (variables m) (states m))
       ; Every prop mapped to T by a state is in its labels
       (only-all-truths-p (states m) m (variables m))
       ; (Converse of the above:)
       ; Every prop in the labels of a state is mapped to T by the state
       (only-truth-p (states m) m)
       ; Every prop in the labels of a state is in the variables of the model
       (label-subset-vars (states m) m (variables m))
       ; For every state, all of its next states are legal states
       (transition-subset-p (states m) (states m) (transition m))
       ; Every initial state is a states
       (subset (initial-states m) (states m))
       ; There is at least one state
       (consp (states m))
       ; Same test as the transition-subset-p test above!
       (next-states-in-states m (states m))))
*)

(******************************************************************************
* PATH M s p is true iff p is a path of model M starting from s
******************************************************************************)
val PATH_def =
 Define
  `PATH M s p = (p 0 = s) /\ !i. M.R(p(i),p(i+1))`;

val PATH_LEMMA =
 store_thm
  ("PATH_LEMMA",
   ``!M s p. s IN M.S /\ PATH M s p /\ MODEL M ==> !n. (p n) IN M.S``,
   RW_TAC std_ss [PATH_def,MODEL_def,IN_DEF, pred_setTheory.SUBSET_DEF]
    THEN Induct_on `n`
    THEN METIS_TAC[DECIDE``SUC n = n+1``]);

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
  `BISIM M M' B Vars=
    !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
           ==>
           (!a. (a IN Vars ==> (M.L s a = M'.L s' a)))           (* 1 *)
           /\
           (!s1. s1 IN M.S /\ M.R(s,s1)
                 ==>
                 ?s1'. s1' IN M'.S /\ M'.R(s',s1') /\ B(s1,s1')) (* 2 *)
           /\
           (!s1'. s1' IN M'.S /\ M'.R(s',s1')
                 ==>
                 ?s1. s1 IN M.S /\ M.R(s,s1) /\ B(s1,s1'))`;     (* 3 *)

(*
Notes on correspondence to ACL2.

B corresponds to \(s,s'). (circuit-bisim s M s' M' vars) for our
particular M, M', and (somehow) vars

1. By c-bisimilar-states-have-labels-equal

2. Witness s1' as (c-bisimilar-transition-witness-m->n s s1 M s' M' vars)
   and this works by theorems
   c-bisimilar-witness-member-of-states-m->n
   (says that s1' is IN M'.S)
   and
   c-bisimilar-witness-produces-bisimilar-states-m->n
   (says that B(s1,s1'))

3. Witness s1 as (c-bisimilar-transition-witness-n->m s M s' s1' M' vars)
   and this works by theorems
   c-bisimilar-witness-member-of-states-n->m
   (says that s1 is IN M.S)
   and
   c-bisimilar-witness-produces-bisimilar-states-n->m
   (says that B(s1,s1'))

Here is what we called BISIM0: A particular bisimilarity relation:

(defun c-bisim-equiv (m n vars)
  (and ; m and n are well-formed Kripke structures:
       (circuit-modelp m)
       (circuit-modelp n)
       ; vars is contained in the variables of each structure:
       (subset vars (variables m))
       (subset vars (variables n))
       ; Every pair of "equal" (with respect to vars) states in m and
       ; n has the same set of successor states (with respect to vars).
       (well-formed-transition-p (states m) (transition m) (states n) (transition n) vars)
       (well-formed-transition-p (states n) (transition n) (states m) (transition m) vars)
       ; Every initial state of m is an initial state of n, and
       ; vice-versa, where we consider two states to be the same if
       ; they are the same when restricted to vars.
       (evaluation-eq-subset-p (initial-states m) (initial-states n) vars)
       (evaluation-eq-subset-p (initial-states n) (initial-states m) vars)))

; Note that circuit-bisim is similar, but has states p and q as
; additional formals and that p and q are states of m and n (resp.)
; that are equal with respect to vars.

*)

(* Definition of bisimulation equivalent *)
val BISIM_EQ_def =
 Define
  `BISIM_EQ M M' Vars =
    ?B. BISIM M M' B Vars                                          (* 1 *)
        /\
        (!s0. s0 IN M.S0 ==> ?s0'. s0' IN M'.S0 /\ B(s0,s0'))   (* 2 *)
        /\
        (!s0'. s0' IN M'.S0 ==> ?s0. s0 IN M.S0 /\ B(s0,s0'))`; (* 3 *)
(*
Notes on correspondence to ACL2.

corresponds to (c-bisim-equiv M M' vars)

1. This particular B will be
   \(s,s'). (circuit-bisim s M s' M' vars)
   for our particular M, M', and (somehow) vars

2. s0' is (c-bisimilar-initial-state-witness-m->n s0 M M' vars);
   see theorems
   c-bisimilar-equiv-implies-init->init-m->n
   (says s0' is an initial state of N)
   and
   c-bisimilar-equiv-implies-bisimilar-initial-states-m->n
   (says (s0,s0') IN B)

3. s0 is (c-bisimilar-initial-state-witness-n->m M s0' M' vars)
   see theorems
   c-bisimilar-equiv-implies-init->init-n->m
   (says s0 is an initial state of M)
   and
   c-bisimilar-equiv-implies-bisimilar-initial-states-n->m
   (says (s0,s0') IN B)
*)


(* Preparation for Lemma 1, p 10 of Ray et al.
   Lemma 31, p 172 of Clarke et al.
*)

(* 
* Auxiliary path-constructing function used in proof of Lemma1a 
* Makes a path in M B-bisimilar to p starting from s
*)
val MAKE_PATH_def =
 Define
  `MAKE_PATH M B p s =
    PRIM_REC s (\t n. @t'. M.R(t,t') /\ B(p(n+1),t'))`;

val MAKE_PATH_REC =
 prove
  (``(MAKE_PATH M B p s 0 =  s)
     /\
     (MAKE_PATH M B p s (SUC n) = 
       @t'. M.R(MAKE_PATH M B p s n, t') /\ B(p(SUC n),t'))``,
   RW_TAC std_ss 
    [MAKE_PATH_def,prim_recTheory.PRIM_REC_THM,DECIDE``n+1 = SUC n``]);

val Lemma1a =
 prove
  (``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B Vars
      ==>
      !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
      ==> !p. PATH M s p ==> ?p'. PATH M' s' p' /\ !i. M'.S(p' i) /\ B(p i, p' i)``,
   RW_TAC std_ss []
    THEN `!n. (p n) IN M.S` by METIS_TAC[PATH_LEMMA]
    THEN FULL_SIMP_TAC std_ss [IN_DEF,PATH_def]
    THEN Q.EXISTS_TAC `MAKE_PATH M' B p s'`
    THEN SIMP_TAC std_ss 
          [prim_recTheory.PRIM_REC_THM,GSYM FORALL_AND_THM,MAKE_PATH_REC]
    THEN Induct
    THEN FULL_SIMP_TAC pure_ss [DECIDE ``n + 1 = SUC n``,PATH_def]
    THEN RW_TAC pure_ss [prim_recTheory.PRIM_REC_THM]
    THEN FULL_SIMP_TAC pure_ss
          (map (SIMP_RULE std_ss [IN_DEF]) [MODEL_def,BISIM_def,PATH_def])
    THEN RW_TAC pure_ss [MAKE_PATH_REC]
    THEN METIS_TAC[]);

(* Matt's proof by symmetry *)
val BISIM_SYM =
 store_thm
  ("BISIM_SYM",
   ``!M M' B. BISIM M M' B Vars ==> BISIM M' M (\(x,y). B(y,x)) Vars``,
   RW_TAC std_ss [BISIM_def]
    THEN METIS_TAC[]);

val Lemma1b =
 prove
  (``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B Vars
       ==>
       !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
              ==> !p'. PATH M' s' p' 
                       ==> ?p. PATH M s p /\ !i. M.S(p i) /\ B(p i, p' i)``,
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
       MODEL M /\ MODEL M' /\ BISIM M M' B Vars
        ==>
        !s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
               ==>
               (!p. PATH M s p 
                    ==> ?p'. PATH M' s' p' /\ !i. M'.S(p' i) /\ B(p i, p' i))
               /\
               (!p'. PATH M' s' p' 
                     ==> ?p. PATH M s p /\ !i. M.S(p i) /\ B(p i, p' i))``,
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
   ``!M s p. MODEL M /\ M.S s /\ PATH M s p 
             ==> !n i. M.S (SUFFIX p n i)``,
   RW_TAC std_ss [MODEL_def,PATH_def,SUFFIX_def,IN_DEF]
    THEN Induct_on `n` THEN Induct_on `i`
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC arith_ss [DECIDE ``n + 1 = SUC n``]
    THEN METIS_TAC[DECIDE``SUC i + SUC n = SUC(n + SUC i)``]);

(* Lemma  2, p 10 of Ray et al. Lemma 32, p 172 of Clarke et al. *)

(* Mike's proof: runtime: 161.497s, gctime: 6.142s, systime: 0.410s. 
val Lemma2 =
  time store_thm
  ("Lemma2",
   ``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B Vars
       ==>
       !f s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
                ==> 
                !p p'. 
                 PATH M s p /\ PATH M' s' p' /\ (!i. B(p i, p' i))
                            /\ (Atoms f SUBSET Vars)
                 ==> (SEM M p f = SEM M' p' f)``,
   REPEAT GEN_TAC
    THEN SIMP_TAC std_ss []
    THEN STRIP_TAC
    THEN Induct
    THEN FULL_SIMP_TAC std_ss [SEM_def,Atoms_def,SUBSET_DEF,NOT_IN_EMPTY,IN_SING,UNION_DEF]
    THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
    THEN RW_TAC std_ss []
    THENL
     [METIS_TAC [BISIM_def, PATH_def],
      METIS_TAC [],
      METIS_TAC [],
      METIS_TAC [],
      `!i. p i IN M.S /\ p' i IN M'.S`
        by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
      THEN METIS_TAC [PATH_SUFFIX,BISIM_SUFFIX],
      `!i. p i IN M.S /\ p' i IN M'.S`
        by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
      THEN METIS_TAC [PATH_SUFFIX,BISIM_SUFFIX],
      `!i. p i IN M.S /\ p' i IN M'.S`
        by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
      THEN METIS_TAC [PATH_SUFFIX,BISIM_SUFFIX],
      `!i. p i IN M.S /\ p' i IN M'.S`
        by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
      THEN METIS_TAC [PATH_SUFFIX,BISIM_SUFFIX],
      `!i. p i IN M.S /\ p' i IN M'.S`
        by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
      THEN METIS_TAC [PATH_SUFFIX,BISIM_SUFFIX]]);
*)

(* Konrad's proof: runtime: 7.157s, gctime: 0.752s, systime: 0.015s. *)
val Lemma2 =
  time store_thm
  ("Lemma2",
   ``!M M' B.
      MODEL M /\ MODEL M' /\ BISIM M M' B Vars
       ==>
       !f s s'. s IN M.S /\ s' IN M'.S /\ B(s,s')
                ==> 
                !p p'. 
                 PATH M s p /\ PATH M' s' p' /\ (!i. B(p i, p' i))
                            /\ (Atoms f SUBSET Vars)
                 ==> (SEM M p f = SEM M' p' f)``,
   REPEAT GEN_TAC
    THEN SIMP_TAC std_ss [SUBSET_DEF]
    THEN STRIP_TAC
    THEN Induct 
    THEN RW_TAC (srw_ss()) [SEM_def,Atoms_def]
    THEN FULL_SIMP_TAC (srw_ss()) []
    THENL [FULL_SIMP_TAC std_ss [BISIM_def, PATH_def],
           METIS_TAC[], METIS_TAC[], METIS_TAC[],
           ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC] 
    THEN MAP_EVERY IMP_RES_TAC [PATH_SUFFIX,BISIM_SUFFIX] 
    THEN `!i. p i IN M.S /\ p' i IN M'.S`
          by METIS_TAC [PATH_LEMMA, MODEL_def, SPECIFICATION]
    THEN METIS_TAC []);

(* Theorem 1, p 10 of Ray et al. Theorem 14, p 175 of Clarke et al. *)
val Theorem1 =
 time store_thm
  ("Theorem1",
   ``!M M'. MODEL M /\ MODEL M' /\ BISIM_EQ M M' Vars 
            ==> !f. (Atoms f SUBSET Vars) ==> (SAT M f = SAT M' f)``,
   RW_TAC std_ss [BISIM_EQ_def,SAT_def,SPECIFICATION]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN RES_TAC
    THENL
     [`s0 IN M.S /\ (p 0) IN M'.S`
       by METIS_TAC[IN_DEF,pred_setTheory.SUBSET_DEF,MODEL_def]
       THEN `!p'. PATH M' (p 0) p' ==> ?p. PATH M s0 p /\ !i. B (p i,p' i)`
        by METIS_TAC[Lemma1]
       THEN RES_TAC
       THEN `SEM M p' f` by METIS_TAC[PATH_def,pred_setTheory.SUBSET_DEF,MODEL_def,SPECIFICATION]
       THEN METIS_TAC[Lemma2,IN_DEF],
      `s0' IN M'.S /\ (p 0) IN M.S`
        by METIS_TAC[IN_DEF,pred_setTheory.SUBSET_DEF,MODEL_def]
       THEN `?p'. PATH M' s0' p' /\ !i. B (p i,p' i)` by METIS_TAC[Lemma1]
       THEN RES_TAC
       THEN `SEM M' p' f` by METIS_TAC[PATH_def]
       THEN METIS_TAC[Lemma2,IN_DEF]]);

(* Instantiate to sexp-model

ISPECL [``MAKE_HOL_MODEL m1``,``MAKE_HOL_MODEL m2``]Theorem1;



I've tweaked the original HOL LTL proof to go through using the
assumption on the transition relation R that:

 !s s'. s IN M.S /\ (s,s') IN M.R ==> s' IN M.S

I think this corresponds to the Sandip assumption, based on what you
said in an email:
  
  ------------------------------------------------------------------
  I was however able to prove the following:

   (defthm range-transition-relation
    (implies (and (next-statep p q M)
                  (memberp p (g :states M)) ; sadly, seems necessary
                  (circuit-modelp M))
             (memberp q (g :states M))))
  ------------------------------------------------------------------

I didn't need to change the definition of a path (as you predicted).

I haven't looked at adding Vars, but I don't expect there to be any
problems.

Instead, I've been experimenting with reformulating the sexpression
version you devised so that it is an instance of the original
HOL version (i.e. so no need to convert "s IN M.S" to "s IN S M" etc).

Let me know what you think of this reformulation. If you think it
good, then I will use this approach when adding Vars.

The reformulation defines a function that converts a Sandip
s-expression representation of a model ``m:sexp`` to a HOL Kripke
structures ``MAKE_HOL_MODEL m`` which has HOL type
``(sexp,sexp)model`` - i.e. both states and propositions are 
s-expressions. The definition packages up your definitions of S, S0,
L, R into a HOL record structure:

   val MAKE_HOL_MODEL_def =
    Define
     `MAKE_HOL_MODEL m =
       <| S  := \s.     |= memberp s (g States m);
          S0 := \s.     |= memberp s (g InitialStates m);
          R  := \(p,q). |= (next_statep p q m);
          L  := \s a.   |= memberp a (label_of s m)
       |> : (sexp,sexp)model`;

The HOL Theorem1:

   |- !M M'.
       MODEL M /\ MODEL M' /\ BISIM_EQ M M' 
       ==> 
       !f. SAT M f <=> SAT M' f

can then be instantiated to

   |- MODEL (MAKE_HOL_MODEL m1) /\ MODEL (MAKE_HOL_MODEL m2) /\
      BISIM_EQ (MAKE_HOL_MODEL m1) (MAKE_HOL_MODEL m2) 
      ==>
      !f. SAT (MAKE_HOL_MODEL m1) f <=> SAT (MAKE_HOL_MODEL m2) f

where m1 and m2 are Sandip s-expression models. In our application, m2
will be COIR m1.

To link the Sandip and HOL formulations of Kripke structure models one
needs to prove that:

   !m. (|= circuit_modelp m) ==> MODEL(MAKE_HOL_MODEL m)

which, from the (revised) definition of MODEL, amounts to proving for
all m that:

   (|= circuit_modelp m)       /\
   (|= memberp s (g States m)) /\
   (|= next_statep s s' m)
   ==>
   (|= memberp s' (g States m))

and

   (|= circuit_modelp m) /\
   (|= memberp x (g InitialStates m))
   ==>
   (|= memberp x (g States m))

I think you've already done these.

The third assumption of Theorem1 is 

 BISIM_EQ (MAKE_HOL_MODEL m1) (MAKE_HOL_MODEL m2)

which expands to the following. Presumably Sandip provides an expicit
s-expression witness for the existentially quantified variable B
below, plus ACL2 theorems we can import into HOL to prove this (in the
case that m2 is COIR m1).

    ?B.
      (!s s'.
         (|= memberp s (g States m1)) /\ (|= memberp s' (g States m2)) /\
         B (s,s') ==>
         ((\a. |= memberp a (label_of s m1)) =
          (\a. |= memberp a (label_of s' m2))) /\
         (!s1.
            (|= memberp s1 (g States m1)) /\ (|= next_statep s s1 m1) ==>
            ?s1'.
              (|= memberp s1' (g States m2)) /\
              (|= next_statep s' s1' m2) /\ B (s1,s1')) /\
         !s1'.
           (|= memberp s1' (g States m2)) /\ (|= next_statep s' s1' m2) ==>
           ?s1.
             (|= memberp s1 (g States m1)) /\ (|= next_statep s s1 m1) /\
             B (s1,s1')) /\
      (!s0.
         (|= memberp s0 (g InitialStates m1)) ==>
         ?s0'. (|= memberp s0' (g InitialStates m2)) /\ B (s0,s0')) /\
      !s0'.
        (|= memberp s0' (g InitialStates m2)) ==>
        ?s0. (|= memberp s0 (g InitialStates m1)) /\ B (s0,s0')

I haven't looked at your LTLscript-*.sml files in detail yet 
(I suspect some of the stuff above may duplicate or clash with
LTLscript-3.sml). I'll do that next. BTW Holmake requires that source
files that create theories are of the exact form
<TheoryName>Script.sml (note capitalised "S"). This is indeed horrible, 
but one has to live with it, so we may need to switch to LTLScript-*.sml.

*)



val _ = export_theory();
