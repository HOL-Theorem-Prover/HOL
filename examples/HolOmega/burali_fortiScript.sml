(*---------------------------------------------------------------------------
                   Burali-Forti Paradox in HOL-Omega
      From the paper "An Analysis of Girard's Paradox" by Thierry Coquand
           but more directly following the Coq proof listed at
      http://coq.inria.fr/pylons/contribs/files/Paradoxes/v8.3/Paradoxes.BuraliForti_ex.html
              Ported to HOL-Omega by Peter Vincent Homeier

      This is a recreation of that formalization in the HOL-Omega logic
      as far as possible, to show exactly where the argument breaks down
      in this different logic, thereby showing that HOL-Omega does not
      have this vulnerability.
 ---------------------------------------------------------------------------*)

structure burali_fortiScript =
struct

open HolKernel Parse boolLib bossLib

val _ = new_theory "burali_forti";

val _ = set_trace "types" 1; (* show types when printing terms *)

open relationTheory;

(* From relationTheory, uses term constants `WF`,`WFP`, and theorems
  val WFP_STRONG_INDUCT =
    |- ∀R. (∀x. WFP R x ∧ (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. WFP R x ⇒ P x
     : thm
  val WFP_CASES =
    |- ∀R x. WFP R x ⇔ ∀y. R y x ⇒ WFP R y
     : thm
  val WFP_RULES =
    |- ∀R x. (∀y. R y x ⇒ WFP R y) ⇒ WFP R x
     : thm
  val WF_EQ_WFP =
    |- ∀R. WF R ⇔ ∀x. WFP R x
     : thm
*)

val WFP_irrefl = store_thm
  ("WFP_irrefl",
   ``!(R:'a -> 'a -> bool) (x:'a). WFP R x ==> R x x ==> F``,
   GEN_TAC
   THEN HO_MATCH_MP_TAC WFP_STRONG_INDUCT
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
  );

(*---------------------------------------------------------------------------
     The new tactic FIRST_PAT_ASSUM applies the theorem-tactic `ttac`
     to the first hypothesis in the assumption list (starting from
     the most recent) which matches the given pattern `pat`.
     The matching used here is higher order matching.
     This is needed to select one particular hypothesis with precision
     since HOL does not support random accessing of the assumptions.
 ---------------------------------------------------------------------------*)

local
val match = ho_om_match_term [] [] empty_tmset
in
fun FIRST_PAT_ASSUM pat ttac : tactic = fn (asl,gl) =>
  let val a = Lib.first (Lib.can (match pat)) asl
  in ttac (ASSUME a) (asl,gl)
  end
end;

fun REWRITE_THM th = REWRITE_TAC [th];

(* --------------------------------------------- *)
(* Definitions of predicates                     *)
(* that a function is a morphism, and            *)
(* that it preserves strictness.                 *)
(* --------------------------------------------- *)

(* We wish to use S as a variable, so we hide    *)
(* the S constant defined in the combin library. *)
val _ = hide "S";

val morphism_def = new_definition(
   "morphism_def",
  ``morphism R S (f:'a -> 'b) = !x y. R x y ==> S (f x) (f y)``);

val preserve_strictness_def = new_definition(
   "preserve_strictness_def",
  ``preserve_strictness R (f:'a -> 'b) =
      !x y. ~(x = y) ==> R x y ==> ~(f x = f y)``);


(* --------------------------------------------- *)
(* The definition of a                           *)
(* universal system of notations for relations.  *)
(* It has type !'x. ('x -> 'x -> bool) -> 'a     *)
(* for some type 'a.                             *)
(* Note this universal type is quantified        *)
(* over types of rank 0,                         *)
(* and the result type 'a is also of rank 0.     *)    
(*                                               *)
(* < The existence of such a universal system >  *)
(* < necessarily entails a contradiction.     >  *)
(* --------------------------------------------- *)

val usnr_def = new_definition(
   "usnr_def", Term
   `usnr (i : !'x. ('x -> 'x -> bool) -> 'a) =
      !:'b 'c. !(R1:'b -> 'b -> bool) (R2:'c -> 'c -> bool).
        (i [:'b:] R1 = i [:'c:] R2) ==>
        ?(f:'b -> 'c). morphism R1 R2 f /\ preserve_strictness R1 f`);

(* --------------------------------------------- *)
(* Definitions of                                *)
(* 1) the domain of a relation,                  *)
(* 2) whether a relation is strict, and          *)
(* 3) an augmentation of a relation's pairs by   *)
(*    adding reflexive pairs for a given subset. *)
(* --------------------------------------------- *)

val dom_def = new_definition(
   "dom_def",
  ``dom (R : 'a -> 'a -> bool) x = R x x``);

val strict_def = new_definition(
   "strict_def",
  ``strict (R : 'a -> 'a -> bool) x y = ~(x = y) /\ R x y``);

val define_on_def = new_definition(
   "define_on_def",
  ``define_on (P : 'a -> bool) (R : 'a -> 'a -> bool) x y =
          R x y \/ (x = y) /\ P y``);

(* --------------------------------------------- *)
(* Definition of the embedding relation, given a *)
(* universal system of notations for relations.  *)
(* --------------------------------------------- *)

val emb_def = new_definition(
   "emb_def",
  ``emb (i : !'x. ('x -> 'x -> bool) -> 'a) (x:'a) (y:'a) =
       ?:'b. ?R1:'b -> 'b -> bool.
         (x = i [:'b:] R1) /\
       ?:'c. ?R2:'c -> 'c -> bool.
         (y = i [:'c:] R2) /\
         WF (strict R2) /\
       ?f:'b -> 'c.
         morphism R1 R2 f /\
         preserve_strictness R1 f /\
       ?maj:'c.
         dom R2 maj /\
         !(z:'b). dom R1 z ==> strict R2 (f z) maj``);

fun LIST_EXISTS_TAC (tm::tms) =
      EXISTS_TAC tm
      THEN REPEAT CONJ_TAC
      THEN TRY (LIST_EXISTS_TAC tms)
  | LIST_EXISTS_TAC [] = ALL_TAC;

fun TY_TM_EXISTS_TAC (inL ty) = TY_EXISTS_TAC ty
  | TY_TM_EXISTS_TAC (inR tm) =  Q.EXISTS_TAC tm;

fun LIST_TY_TM_EXISTS_TAC (tym::tyms) =
      TY_TM_EXISTS_TAC tym
      THEN REPEAT CONJ_TAC
      THEN TRY (LIST_TY_TM_EXISTS_TAC tyms)
  | LIST_TY_TM_EXISTS_TAC [] = ALL_TAC;

val emb_trans = store_thm
  ("emb_trans",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> transitive (emb i0)``,
   REWRITE_TAC [usnr_def,transitive_def]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (fn th1 => FIRST_ASSUM (fn th2 =>
           ASSUME_TAC th1
           THEN MAP_EVERY (STRIP_ASSUME_TAC o
                           REWRITE_RULE[emb_def,dom_def]) [th2,th1]))
   THEN Q.UNDISCH_TAC `y = i0 R1'`
   THEN REWRITE_THM (ASSUME ``y = (i0:!'x. ('x -> 'x -> bool) -> 'a0) (R2:'c->'c->bool)``)
   THEN DISCH_TAC
   THEN FIRST_ASSUM (fn th => FIRST_ASSUM (STRIP_ASSUME_TAC o C MATCH_MP th))
   THEN REWRITE_TAC [emb_def]
   THEN LIST_TY_TM_EXISTS_TAC [inL ``:'b``,
                               inR `R1`,
                               inL ``:'e``,
                               inR `R2'`,
                               inR `\x. f' (f'' (f x))`,
                               inR `maj'`]
   THENL
     [ ASM_REWRITE_TAC [],

       ASM_REWRITE_TAC [],

       ASM_REWRITE_TAC [],

       FULL_SIMP_TAC bool_ss [morphism_def],

       FULL_SIMP_TAC bool_ss [preserve_strictness_def,morphism_def],

       ASM_REWRITE_TAC [dom_def],

       REPEAT STRIP_TAC
       THEN BETA_TAC
       THEN FIRST_ASSUM MATCH_MP_TAC
       THEN PROVE_TAC [morphism_def,dom_def]
     ]
  );

val WFP_emb = store_thm
  ("WFP_emb",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==>
       !:'x. !(R : 'x -> 'x -> bool) (x:'x).
         WFP (strict R) x ==>
         !:'y. !(S : 'y -> 'y -> bool) (f:'y -> 'x).
           morphism S R f ==>
           preserve_strictness S f ==>
           (!(y:'y). dom S y ==> strict R (f y) x) ==> WFP (emb i0) (i0 S)``,
   REWRITE_TAC [usnr_def]
   THEN GEN_TAC
   THEN DISCH_TAC
   THEN REWRITE_TAC [dom_def]
   THEN TY_GEN_TAC
   THEN GEN_TAC
   THEN HO_MATCH_MP_TAC WFP_STRONG_INDUCT
   THEN GEN_TAC
   THEN STRIP_TAC
   THEN POP_ASSUM MP_TAC
   THEN IMP_RES_TAC WFP_CASES
   THEN DISCH_THEN (ASSUME_TAC o GEN ``y:'x`` o SPEC ``y:'x``)
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [WFP_CASES]
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[emb_def])
   THEN REWRITE_THM (ASSUME ``y = (i0:!'x. ('x -> 'x -> bool) -> 'a0) (R1:'b -> 'b -> bool)``)
   THEN FIRST_ASSUM (MP_TAC o Q.SPECL[`R2`,`S`] o TY_SPECL[``:'c``,``:'y``])
   THEN FIRST_ASSUM (fn th => REWRITE_TAC[SYM th])
   THEN STRIP_TAC
   THEN FIRST_ASSUM (MP_TAC o SPEC ``(f:'y -> 'x) (f'' (maj:'c))``)
   THEN SUBGOAL_THEN ``strict R ((f:'y -> 'x) (f'' (maj:'c))) x`` REWRITE_THM
   THENL [ PROVE_TAC[morphism_def,dom_def], ALL_TAC ]
   THEN DISCH_THEN (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO]
                           o SPECL[``R1:'b ->'b -> bool``,
                                   ``\x. (f:'y -> 'x) (f'' ((f':'b -> 'c) x))``]
                           o TY_SPEC ``:'b``)
   THEN FULL_SIMP_TAC bool_ss [morphism_def,preserve_strictness_def]
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM (fn th => FIRST_ASSUM (MP_TAC o C MATCH_MP th o REWRITE_RULE[dom_def]))
   THEN FULL_SIMP_TAC bool_ss [strict_def]
  );

val WF_emb = store_thm
  ("WF_emb",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> WF (emb i0)``,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC usnr_def
   THEN REWRITE_TAC [WF_EQ_WFP]
   THEN GEN_TAC
   THEN MATCH_MP_TAC WFP_RULES
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC emb_def
   THEN REWRITE_THM (ASSUME ``y = (i0:!'x. ('x -> 'x -> bool) -> 'a0) (R1:'b -> 'b -> bool)``)
   THEN IMP_RES_TAC WF_EQ_WFP
   THEN IMP_RES_THEN (MP_TAC o SPECL[``maj:'c``,``R2:'c -> 'c -> bool``] o TY_SPEC ``:'c``) WFP_emb
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (MP_TAC o SPEC ``f:'b -> 'c`` o TY_SPEC ``:'b``)
   THEN DISCH_THEN (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO])
   THEN ASM_REWRITE_TAC []
  );

val emb_irrefl = store_thm
  ("emb_irrefl",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> !x y. emb i0 x y ==> ~(x = y)``,
   GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN REPEAT STRIP_TAC
   THEN MATCH_MP_TAC (REWRITE_RULE[AND_IMP_INTRO]
                       (ISPEC ``emb (i0:!'x. ('x -> 'x -> bool) -> 'a0)``
                              WFP_irrefl))
   THEN Q.EXISTS_TAC `x`
   THEN CONJ_TAC
   THENL
     [ IMP_RES_TAC (REWRITE_RULE[WF_EQ_WFP] WF_emb)
       THEN ASM_REWRITE_TAC [],

       Q.UNDISCH_TAC `emb i0 x y`
       THEN FIRST_ASSUM (REWRITE_THM o SYM)
       THEN REWRITE_TAC []
     ]
  );

(* Encoding a relation defined everywhere *)

val large_emb_def = new_definition(
   "large_emb_def", Term
   `large_emb (i : !'x. ('x -> 'x -> bool) -> 'a) = define_on (\x. T) (emb i)`);

val WF_emb_strict = store_thm
  ("WF_emb_strict",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> WF (strict (large_emb i0))``,
   GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN REWRITE_TAC [WF_EQ_WFP]
   THEN GEN_TAC
   THEN IMP_RES_THEN (MP_TAC o SPEC ``x:'a0`` o REWRITE_RULE[WF_EQ_WFP]) WF_emb
   THEN SPEC_TAC (``x:'a0``,``x:'a0``)
   THEN HO_MATCH_MP_TAC WFP_STRONG_INDUCT
   THEN (CONV_TAC o RAND_CONV o ABS_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV
                  o ONCE_REWRITE_CONV) [WFP_CASES]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (ASSUME_TAC o GEN ``y:'a0`` o SPEC ``y:'a0``)
   THEN MATCH_MP_TAC WFP_RULES
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[strict_def])
   THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[large_emb_def,define_on_def])
  );

(*---------------------------------------------------------------------------
     Definition of the Omega function.
 ---------------------------------------------------------------------------*)

val Omega_def = new_definition(
   "Omega_def",
  ``Omega (i : !'x. ('x -> 'x -> bool) -> 'a) = i (large_emb i)``);

(* Section Subsets *)

val restrict_def = new_definition(
   "restrict_def",
  ``restrict (i : !'x. ('x -> 'x -> bool) -> 'a) (a:'a) =
    define_on (\c. emb i c a) (emb i)``);

(*---------------------------------------------------------------------------
     Definition of the FF function.
     (We use `FF` instead of `F` because `F` is the boolean constant false.)
 ---------------------------------------------------------------------------*)

val FF_def = new_definition(
   "FF_def",
  ``FF (i : !'x. ('x -> 'x -> bool) -> 'a) (a:'a) = i (restrict i a)``);

val FF_emb_Omega = store_thm
  ("FF_emb_Omega",
   ``!(i0:!'x. ('x -> 'x -> bool) -> 'a0) (a:'a0). usnr i0 ==> emb i0 (FF i0 a) (Omega i0)``,
   REPEAT GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN REWRITE_TAC [emb_def]
   THEN LIST_TY_TM_EXISTS_TAC [inL ``:'a0``,
                               inR `restrict i0 a`,
                               inL ``:'a0``,
                               inR `large_emb i0`,
                               inR `\x:'a0.x`,
                               inR `a`]
   THENL
     [ REWRITE_TAC [FF_def],

       REWRITE_TAC [Omega_def],

       IMP_RES_THEN ACCEPT_TAC WF_emb_strict,

       SIMP_TAC bool_ss [morphism_def,large_emb_def,restrict_def,define_on_def]
       THEN REPEAT STRIP_TAC
       THEN ASM_REWRITE_TAC [],

       SIMP_TAC bool_ss [preserve_strictness_def],

       SIMP_TAC bool_ss [dom_def,large_emb_def,define_on_def],

       SIMP_TAC bool_ss [dom_def,restrict_def,define_on_def]
       THEN REPEAT STRIP_TAC
       THENL
         [ IMP_RES_TAC emb_irrefl
           THEN POP_ASSUM MP_TAC
           THEN REWRITE_TAC [],

           REWRITE_TAC [strict_def]
           THEN CONJ_TAC
           THENL
             [ IMP_RES_TAC emb_irrefl,

               ASM_REWRITE_TAC [large_emb_def,define_on_def]
             ]
         ]
     ]
  );

val emb_morph = store_thm
  ("emb_morph",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==>
     !f:'a0 -> 'a0. morphism (emb i0) (emb i0) f ==>
     !x:'a0. ~(emb i0 (f x) x)``,
   GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN GEN_TAC
   THEN REWRITE_TAC [morphism_def]
   THEN DISCH_TAC THEN GEN_TAC
   THEN IMP_RES_THEN (MP_TAC o SPEC ``x:'a0`` o REWRITE_RULE[WF_EQ_WFP]) WF_emb
   THEN SPEC_TAC (``x:'a0``,``x:'a0``)
   THEN HO_MATCH_MP_TAC WFP_STRONG_INDUCT
   THEN (CONV_TAC o RAND_CONV o ABS_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV
                  o ONCE_REWRITE_CONV) [WFP_CASES]
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM (MP_TAC o SPEC ``(f:'a0 -> 'a0) x``)
   THEN FIRST_ASSUM (fn th => REWRITE_TAC[th])
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN FIRST_ASSUM ACCEPT_TAC
  );

val FF_Omega_neq = store_thm
  ("FF_Omega_neq",
   ``!(i0:!'x. ('x -> 'x -> bool) -> 'a0) (a:'a0). usnr i0 ==> ~(FF i0 a = Omega i0)``,
   REPEAT GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN REWRITE_TAC[FF_def,Omega_def]
   THEN DISCH_THEN (ASSUME_TAC o SYM)
   THEN RES_TAC
   THEN POP_ASSUM MP_TAC
   THEN POP_ASSUM MP_TAC
   THEN POP_ASSUM (K ALL_TAC)
   THEN REWRITE_TAC [morphism_def,preserve_strictness_def,restrict_def]
   THEN REPEAT STRIP_TAC
   THEN SUBGOAL_THEN ``morphism (emb (i0:!'x. ('x -> 'x -> bool) -> 'a0)) (emb i0) (f:'a0 -> 'a0)`` ASSUME_TAC
   THENL
     [ REWRITE_TAC [morphism_def]
       THEN REPEAT STRIP_TAC
       THEN RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE[large_emb_def,define_on_def])
       THEN FIRST_PAT_ASSUM ``!(x:'a) (y:'a). P x y \/ Q x y ==> R x y``
                (MP_TAC o Q.SPECL[`x`,`y`])
       THEN FIRST_ASSUM (fn th => REWRITE_TAC[th])
       THEN STRIP_TAC
       THEN POP_ASSUM (K ALL_TAC)
       THEN IMP_RES_TAC emb_irrefl
       THEN FIRST_ASSUM (fn th => FIRST_ASSUM (MP_TAC o C MATCH_MP th))
       THEN ASM_REWRITE_TAC [],

       SUBGOAL_THEN ``emb (i0:!'x. ('x -> 'x -> bool) -> 'a0) (f a) (a:'a0)`` MP_TAC
       THENL
         [ POP_ASSUM MP_TAC
           THEN POP_ASSUM MP_TAC
           THEN POP_ASSUM MP_TAC
           THEN SIMP_TAC bool_ss [large_emb_def,define_on_def]
           THEN DISCH_THEN (fn th => ASSUME_TAC th
                                     THEN REPEAT STRIP_TAC
                                     THEN MP_TAC (Q.SPECL[`a`,`a`] th))
           THEN REWRITE_TAC[]
           THEN STRIP_TAC
           THEN IMP_RES_TAC emb_irrefl
           THEN POP_ASSUM MP_TAC
           THEN REWRITE_TAC[],

           IMP_RES_TAC emb_morph
           THEN ASM_REWRITE_TAC []
         ]
     ]
  );

val FF_emb_strict_Omega = store_thm
  ("FF_emb_strict_Omega",
   ``!(i0:!'x. ('x -> 'x -> bool) -> 'a0) (a:'a0). usnr i0 ==> strict (large_emb i0) (FF i0 a) (Omega i0)``,
   REPEAT GEN_TAC THEN DISCH_TAC
   THEN REWRITE_TAC[strict_def]
   THEN CONJ_TAC
   THENL
     [ IMP_RES_THEN MATCH_ACCEPT_TAC FF_Omega_neq,

       REWRITE_TAC[large_emb_def,define_on_def]
       THEN DISJ1_TAC
       THEN IMP_RES_THEN MATCH_ACCEPT_TAC FF_emb_Omega
     ]
  );

(* End of Subsets Section. *)

val WF_restrict = store_thm
  ("WF_restrict",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> !a:'a0. WF (strict (restrict i0 a))``,
   REPEAT GEN_TAC THEN DISCH_TAC
   THEN REWRITE_TAC[WF_EQ_WFP]
   THEN REPEAT GEN_TAC
   THEN IMP_RES_THEN (MP_TAC o SPEC ``x:'a0`` o REWRITE_RULE[WF_EQ_WFP]) WF_emb
   THEN SPEC_TAC (``x:'a0``,``x:'a0``)
   THEN HO_MATCH_MP_TAC WFP_STRONG_INDUCT
   THEN (CONV_TAC o RAND_CONV o ABS_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV
                  o ONCE_REWRITE_CONV) [WFP_CASES]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (ASSUME_TAC o GEN ``y:'a0`` o SPEC ``y:'a0``)
   THEN MATCH_MP_TAC WFP_RULES
   THEN REPEAT STRIP_TAC
   THEN FIRST_ASSUM MATCH_MP_TAC
   THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[strict_def])
   THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[restrict_def,define_on_def])
  );

val morphism_restrict = store_thm
  ("morphism_restrict",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> !x y:'a0. emb i0 x y ==> morphism (restrict i0 x) (restrict i0 y) (\x.x)``,
   GEN_TAC THEN DISCH_TAC
   THEN SIMP_TAC bool_ss [morphism_def]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (MP_TAC o BETA_RULE o REWRITE_RULE[restrict_def,define_on_def])
   THEN STRIP_TAC
   THENL
     [ SIMP_TAC bool_ss [restrict_def,define_on_def]
       THEN DISJ1_TAC
       THEN FIRST_ASSUM ACCEPT_TAC,

       SIMP_TAC bool_ss [restrict_def,define_on_def]
       THEN DISJ2_TAC
       THEN ASM_REWRITE_TAC []
       THEN IMP_RES_TAC (REWRITE_RULE[transitive_def] emb_trans)
     ]
  );


val FF_morphism = store_thm
  ("FF_morphism",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> morphism (large_emb i0) (large_emb i0) (FF i0)``,
   GEN_TAC THEN DISCH_TAC
   THEN SIMP_TAC bool_ss [morphism_def]
   THEN REPEAT GEN_TAC
   THEN DISCH_THEN (STRIP_ASSUME_TAC o BETA_RULE o REWRITE_RULE[large_emb_def,define_on_def])
   THENL
     [ SIMP_TAC bool_ss [large_emb_def,define_on_def]
       THEN DISJ1_TAC
       THEN REWRITE_TAC [emb_def]
       THEN LIST_TY_TM_EXISTS_TAC [inL ``:'a0``,
                                   inR `restrict i0 x`,
                                   inL ``:'a0``,
                                   inR `restrict i0 y`,
                                   inR `\x:'a0.x`,
                                   inR `x`]
       THEN ASM_SIMP_TAC bool_ss [FF_def]
       THENL (* 5 subgoals *)
         [ IMP_RES_THEN MATCH_ACCEPT_TAC WF_restrict,

           IMP_RES_TAC morphism_restrict,

           SIMP_TAC bool_ss [preserve_strictness_def],

           SIMP_TAC bool_ss [dom_def,restrict_def,define_on_def]
           THEN DISJ2_TAC
           THEN FIRST_ASSUM ACCEPT_TAC,

           GEN_TAC
           THEN DISCH_THEN
                    (STRIP_ASSUME_TAC o
                     SIMP_RULE bool_ss [dom_def,restrict_def,define_on_def])
           THENL
             [ IMP_RES_THEN (IMP_RES_THEN MP_TAC) emb_irrefl
               THEN REWRITE_TAC [],

               SIMP_TAC bool_ss [strict_def,restrict_def,define_on_def]
               THEN PROVE_TAC [emb_irrefl]
             ]
         ],

       SIMP_TAC bool_ss [large_emb_def,define_on_def]
       THEN DISJ2_TAC
       THEN FIRST_ASSUM REWRITE_THM
       THEN REFL_TAC
     ]
  );

val FF_preserve_strictness = store_thm
  ("FF_preserve_strictness",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> preserve_strictness (large_emb i0) (FF i0)``,
   GEN_TAC THEN DISCH_TAC
   THEN IMP_RES_TAC usnr_def
   THEN SIMP_TAC bool_ss [preserve_strictness_def]
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM (ASSUME_TAC o REWRITE_RULE[FF_def])
   THEN POP_ASSUM (ASSUME_TAC o SYM)
   THEN FIRST_ASSUM (fn th => FIRST_ASSUM (MP_TAC o MATCH_MP th))
   THEN REWRITE_TAC [morphism_def,preserve_strictness_def]
   THEN STRIP_TAC
   THEN STRIP_ASSUME_TAC (REWRITE_RULE[large_emb_def,define_on_def]
                              (ASSUME ``large_emb (i0:!'x. ('x -> 'x -> bool) -> 'a0) x y``))
   THEN Q.SUBGOAL_THEN `morphism (emb i0) (emb i0) f` ASSUME_TAC
   THENL
     [ REWRITE_TAC [morphism_def]
       THEN REPEAT STRIP_TAC
       THEN FIRST_PAT_ASSUM
               ``!x y. restrict (i0:!'x. ('x -> 'x -> bool) -> 'a0) u x y ==> P x y``
               (MP_TAC o Q.SPECL[`x'`,`y'`])
       THEN SIMP_TAC bool_ss [restrict_def,define_on_def]
       THEN ASM_REWRITE_TAC []
       THEN STRIP_TAC
       THEN FIRST_ASSUM (MP_TAC o Q.SPECL[`x'`,`y'`])
       THEN FIRST_PAT_ASSUM ``a:'a = b`` (fn th => REWRITE_TAC[th])
       THEN MATCH_MP_TAC (DECIDE ``~P ==> (P ==> Q)``)
       THEN SIMP_TAC bool_ss []
       THEN CONJ_TAC
       THENL
         [ IMP_RES_THEN MATCH_MP_TAC emb_irrefl
           THEN FIRST_ASSUM ACCEPT_TAC,

           SIMP_TAC bool_ss [restrict_def,define_on_def]
           THEN DISJ1_TAC
           THEN FIRST_ASSUM ACCEPT_TAC
         ],

       SUBGOAL_THEN ``emb (i0:!'x. ('x -> 'x -> bool) -> 'a0) (f x) x`` MP_TAC
       THENL
         [ FIRST_PAT_ASSUM
               ``!x y. restrict (i0:!'x. ('x -> 'x -> bool) -> 'a0) u x y ==> P x y``
               (MP_TAC o Q.SPECL[`x`,`x`])
           THEN SIMP_TAC bool_ss [restrict_def,define_on_def,strict_def]
           THEN ASM_REWRITE_TAC []
           THEN STRIP_TAC
           THEN FIRST_ASSUM (fn th => IMP_RES_THEN (MP_TAC o C MATCH_MP th) emb_irrefl)
           THEN REWRITE_TAC [],

           FIRST_ASSUM (fn th => IMP_RES_THEN (MP_TAC o C MATCH_MP th) emb_morph)
           THEN DISCH_THEN (fn th => REWRITE_TAC[th])
         ]
     ]
  );

val Omega_refl = store_thm
  ("Omega_refl",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> emb i0 (Omega i0) (Omega i0)``,
   REPEAT GEN_TAC THEN DISCH_TAC
   THEN REWRITE_TAC[emb_def]
   THEN LIST_TY_TM_EXISTS_TAC [inL ``:'a0``,
                               inR `large_emb i0`,
                               inL ``:'a0``,
                               inR `large_emb i0`,
                               inR `FF i0`,
                               inR `Omega i0`]
   THEN TRY (REWRITE_TAC[Omega_def] THEN NO_TAC)
   THENL (* 5 subgoals *)
     [ IMP_RES_TAC WF_emb_strict,

       IMP_RES_TAC FF_morphism,

       IMP_RES_TAC FF_preserve_strictness,

       SIMP_TAC bool_ss [dom_def,large_emb_def,define_on_def],

       REPEAT STRIP_TAC
       THEN IMP_RES_THEN MATCH_ACCEPT_TAC FF_emb_strict_Omega
     ]
  );

val Burali_Forti = store_thm
  ("Burali_Forti",
   ``!i0:!'x. ('x -> 'x -> bool) -> 'a0. usnr i0 ==> bool$F``,
   REPEAT STRIP_TAC
   THEN IMP_RES_TAC Omega_refl
   THEN IMP_RES_TAC emb_irrefl
   THEN POP_ASSUM MP_TAC
   THEN REWRITE_TAC[]
  );



(* ---------------------------------------------------------------------
   Coquand describes the type A0
   as having one constructor i of type (PI v)((v -> v -> Prop) -> A0)
   which in HOL-Omega could be represented as the type a0
   with the single constructor i : (?'v.   'v -> 'v -> bool) -> a0 .

   This could be done directly, or by the type definition
      Hol_datatype `a0 = i of ?'x. 'x -> 'x -> bool)`;

   Coquand's paper suggests
                        ((PI B:Type)((B -> B -> Prop) -> Prop)) -> Prop
      a0 = (!'b. (('b -> 'b -> bool) -> bool)) -> bool
      i0 = \:B. \R. \x. x(B,R)
        where B : ty
              R : B -> B -> bool
              x : a0 as above
              (B,R) is a (dependent) pair of a type and a relation

   This is accomplished by packages and existential types.
   --------------------------------------------------------------------- *)

(* First version: create A0 directly as an existential type. *)

(* To form a universal system of notation for relations, we propose
        alpha_0 = ?'b. 'b -> 'b -> bool   and
            i_0 = \:'b. \R. pack(:'b,R) : alpha_0
*)

(* The first step is to check and see if such a type and term
   could satisfy the body of the definition of usnr:

- usnr_def;
> val it =
    |- !(i :!'x. ('x -> 'x -> bool) -> 'a).
         usnr i <=>
         !:'b 'c.
           !(R1 :'b -> 'b -> bool) (R2 :'c -> 'c -> bool).
             (i [:'b:] R1 = i [:'c:] R2) ==>
             ?(f :'b -> 'c). morphism R1 R2 f /\ preserve_strictness R1 f
     : thm
 *)

val inj_lemma1 = store_thm
  ("inj_lemma1",
   ``!:'b 'c. !(R1: 'b -> 'b -> bool) (R2: 'c -> 'c -> bool).
       (pack(:'b,R1) = pack(:'c,R2)) ==>
       ?(f : 'b -> 'c).
        morphism R1 R2 f /\ preserve_strictness R1 f``,
   REPEAT STRIP_TAC
   THEN SUBGOAL_THEN
          ``let (:'d, R2') = pack(:'c, R2:'c -> 'c -> bool) in
              ?f:'b -> 'd. morphism R1 R2' f /\ preserve_strictness R1 f``
           (ACCEPT_TAC o SIMP_RULE bool_ss [])
   THEN FIRST_ASSUM (REWRITE_THM o SYM)
   THEN SIMP_TAC bool_ss []
   THEN EXISTS_TAC ``\x:'b. x``
   THEN SIMP_TAC bool_ss [morphism_def,preserve_strictness_def]
  );

val alpha0 = ``:?'b. 'b -> 'b -> bool``;
val alpha0' = ty_antiq alpha0;

val atm1 = ``\:'b. \R:'b -> 'b -> bool. pack(:'b, R)``;

val utm0 = prim_mk_const{Thy="burali_forti", Name="usnr"};
val utm1 = inst_rank 1 utm0;
val utm2 = inst_rank 2 utm0;

val utm0a0 = inst [``:'a:ty:0`` |-> alpha0] utm0;
val utm1a0 = inst [``:'a:ty:1`` |-> alpha0] utm1;
val utm2a0 = inst [``:'a:ty:2`` |-> alpha0] utm2;

(* The substitution to form utm0a0 above is not proper, but the "inst"
   operation compensates by first promoting 'a and utm0 by one rank to
   make the substitution proper. The result is then the same as utm1a0. *)

(* The following contradiction cannot be proven, because the term atm1
         \:'b. \R:'b -> 'b -> bool. pack(:'b, R)
   of type
         !'b:ty:0. ('b -> 'b -> bool) -> (?'x. 'x -> 'x -> bool)
   cannot have the type needed to be the argument to utm1a0,
         !'x:ty:1. ('x -> 'x -> bool) -> (?'b. 'b -> 'b -> bool)
   becaue the universally quantified 'b in the first type does not
   have the same (equal) rank to the universally quantified 'x
   in the second type.

   When comparing two universal types, the kinds of the two
   bound type variables must be completely equal, including rank.
*)

val RESULT1 =
  let val inj = store_thm
        ("inj1",
         mk_comb(utm1a0,atm1),
         SIMP_TAC bool_ss [INST_RANK 1 usnr_def]
         THEN MATCH_ACCEPT_TAC inj_lemma1
        )
      val CONTRADICTION = save_thm
        ("CONTRADICTION",
         MATCH_MP (INST_RANK 1 Burali_Forti) inj
        )
  in
     print "First  contradiction proven within HOL-Omega.\n";
     CONTRADICTION
  end
    handle HOL_ERR _ =>
    (print "First  contradiction prevented by HOL-Omega ranks.\n";
     TRUTH);

(* The following contradiction also cannot be proven, because the term atm1
         \:'b. \R:'b -> 'b -> bool. pack(:'b, R)
   of type
         !'b:ty:0. ('b -> 'b -> bool) -> (?'x. 'x -> 'x -> bool)
   cannot have the type needed to be the argument to utm2a0,
         !'x:ty:2. ('x -> 'x -> bool) -> (?'b. 'b -> 'b -> bool)
   becaue the universally quantified 'b in the first type does not
   have the same (equal) rank to the universally quantified 'x
   in the second type.

   When comparing two universal types, the kinds of the two
   bound type variables must be completely equal, including rank.
*)

val RESULT2 =
  let val inj = store_thm
        ("inj2",
         mk_comb(utm2a0,atm1),
         SIMP_TAC bool_ss [INST_RANK 2 usnr_def]
         THEN MATCH_ACCEPT_TAC inj_lemma1
        )
      val CONTRADICTION = save_thm
        ("CONTRADICTION",
         MATCH_MP (INST_RANK 2 Burali_Forti) inj
        )
  in
     print "Second contradiction proven within HOL-Omega.\n";
     CONTRADICTION
  end
    handle HOL_ERR _ =>
    (print "Second contradiction prevented by HOL-Omega ranks.\n";
     TRUTH);


(* ------------------------------------ *)
(* The third attempt tries to use       *)
(* the data type definition mechanism   *)
(* to finesse the rank issue.            *)
(* ------------------------------------ *)

(* Definition of the type A0 in Coq:

   Record A0 : Type :=
       i {X0 : Type; R0 : X0 -> X0 -> Prop}.

   A non-recursive type; a dependent record type.
   It has one constructor, "i", of type (?'x.  'x -> 'x -> bool) -> A0

   For HOL-Omega, we define the type a0
   using the "Hol_datatype" tool for defining
   new datatypes. The type a0 is specified as
   having a single constructor `i` which injects
   values of type ?'x. 'x -> 'x -> bool into
   the type a0.
*)

val _ = Hol_datatype `a0 = i of (?'x. 'x -> 'x -> bool)`;

(* Note that the new type a0 is not a humble type. *)

val check_humble = is_humble_type ``:a0``;

(* This definition of the new type a0 not only
   creates the new type constant of kind ty:1,
   but also the term constant i,
   and a number of other definitions and theorems,
   of which the most important are:

Type constants:
    a0 : ty:1

Term constants:
    i : (∃ψ. ψ -> ψ -> bool) -> a0

Definitions:
    a0_case_def  |- ∀f a. a0_case f (i a) = f a
    a0_size_def  |- ∀a. a0_size (i a) = 1

Theorems:
    a0_11  |- ∀a a'. (i a = i a') ⇔ (a = a')
    a0_case_cong
    |- ∀M M' f.
         (M = M') ∧ (∀a. (M' = i a) ⇒ (f a = f' a)) ⇒
         (a0_case f M = a0_case f' M')
    a0_nchotomy  |- ∀aa. ∃f. aa = i f
    a0_Axiom  |- ∀f. ∃fn. ∀a. fn (i a) = f a
    a0_induction  |- ∀P. (∀f. P (i f)) ⇒ ∀a. P a

   We will need to use the one-to-one property.
*)

val a0_11 = theorem "a0_11";

(* To form a universal system of notation for relations, we propose
        alpha_0 = a0:ty:1   and
            i_0 = \:'b:ty:1. \R. i (pack(:'b,R))
*)

(* Again, the first step is to check and see if such a type and term
   could satisfy the body of the definition of usnr. *)

val inj_lemma = store_thm
  ("inj_lemma",
   ``!:'b 'c. !(R1: 'b -> 'b -> bool) (R2: 'c -> 'c -> bool).
       (i (pack(:'b,R1)) = i (pack(:'c,R2))) ==>
       ?(f : 'b -> 'c).
        morphism R1 R2 f /\ preserve_strictness R1 f``,
   REWRITE_TAC [a0_11]
   THEN REPEAT STRIP_TAC
   THEN SUBGOAL_THEN
          ``let (:'d, R2') = pack(:'c, R2:'c -> 'c -> bool) in
              ?f:'b -> 'd. morphism R1 R2' f /\ preserve_strictness R1 f``
           (ACCEPT_TAC o SIMP_RULE bool_ss [])
   THEN FIRST_ASSUM (REWRITE_THM o SYM)
   THEN SIMP_TAC bool_ss []
   THEN EXISTS_TAC ``\x:'b. x``
   THEN SIMP_TAC bool_ss [morphism_def,preserve_strictness_def]
  );

val utm = inst [``:'a`` |-> ``:a0``]
          (prim_mk_const{Thy="burali_forti", Name="usnr"});

val itm = inst_rank 1 (prim_mk_const{Thy="burali_forti", Name="i"});

val atm = ``\:'a:ty:1. \R. ^itm (pack(:'a, R))``;

(* The following contradiction cannot be proven, because the term atm
         \:'a:ty:1. \R. ^itm (pack(:'a, R))
   of type
         !'a:ty:1. ('a -> 'a -> bool) -> a0
   cannot have the type needed to be the argument to utm,
         !'x:ty:1. ('x -> 'x -> bool) -> a0
   becaue the two a0's are of different rank!
   The first one has rank 2, whereas the second has rank 1.

   Because a0 is not a humble type,
   these different rank instances are not the same type.
*)

val RESULT =
  let val inj = store_thm
        ("inj",
         mk_comb(utm,atm),
         SIMP_TAC bool_ss [INST_RANK 1 usnr_def]
         THEN MATCH_ACCEPT_TAC inj_lemma
        )
      val CONTRADICTION = save_thm
        ("CONTRADICTION",
         MATCH_MP (INST_RANK 1 Burali_Forti) inj
        )
  in
     print "Final contradiction proven within HOL-Omega.\n";
     CONTRADICTION
  end
    handle HOL_ERR _ =>
    (print "Final contradiction prevented by HOL-Omega ranks.\n";
     TRUTH);




val _ = html_theory "burali_forti";

val _ = export_theory();

end; (* structure burali_fortiScript *)
