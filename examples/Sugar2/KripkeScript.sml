
(*****************************************************************************)
(* Create "KripkeTheory" containing definition of Kripke structure and some  *)
(* related definitions, including computation paths.                         *)
(*                                                                           *)
(* Created Wed Dec 25 23:02:12 GMT 2002                                      *)
(*****************************************************************************)

(******************************************************************************
* A model is a quintuple (S,S0,R,P,L) where
* 
*  - S  : 'state                    is a set of states
*  - S0 : 'state -> bool            is a subset of S, the initial states
*  - R  : 'state # 'state -> bool   is a transition relation 
*  - P  : 'prop                     is a set of atomic proposition
*  - L  : 'state -> ('prop -> bool) maps each state to the 
*                                   set of propositions true in that state
* 
* N.B. terms that follow are not contrained to use type variables 'state and 
       'prop, but may use 'a, 'b etc or whatever typechecking assigns.
******************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theory of finite and infinite sequences and additional definitions of 
functions on lists (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
map load ["PathTheory", "rich_listTheory", "intLib"];
open PathTheory listTheory rich_listTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open PathTheory listTheory rich_listTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called UnclockedSugarSemantics
******************************************************************************)
val _ = new_theory "Kripke";

(******************************************************************************
* Stop ``S`` parsing to the S-combinator
******************************************************************************)
val _ = hide "S";

(******************************************************************************
* KRIPKE_STRUCTURE M iff M is a well-formed Kripke structure
* i.e. every initial state is a state, 
* and L maps each state to a set of propositions.
* For many results the structure M=(S,S0,R,P,L) does not need
* to be a well-formed Kripke structure.
******************************************************************************)
val KRIPKE_STRUCTURE_def =
 Define
  `KRIPKE_STRUCTURE
    (S: 'state -> bool,
     S0:'state -> bool,
     R: 'state # 'state -> bool,
     P: 'prop -> bool,
     L: 'state -> ('prop -> bool)) = 
   (!s. S0 s ==> S s)
   /\
   (!s p . L s p ==> P p)`;

(******************************************************************************
* A useful special case (possibly the only one we'll need) is to
* identify propositions with predicates on states, and then we just need
* to specify the set of initial states B and transition relation R
*******************************************************************************)
val SIMPLE_KRIPKE_STRUCTURE_def =
 Define
  `SIMPLE_KRIPKE_STRUCTURE (B:'state -> bool) (R:'state#'state->bool) = 
    ((\s:'state. T), 
     B, 
     R, 
     (\f:'state -> bool. T), 
     (\(s:'state) (f:'state -> bool). f s))`;

(******************************************************************************
* Sanity check that a simple Kripke structure is a Kripke structure
******************************************************************************)
val SIMPLE_KRIPKE_STRUCTURE =
 store_thm
  ("SIMPLE_KRIPKE_STRUCTURE",
   ``KRIPKE_STRUCTURE(SIMPLE_KRIPKE_STRUCTURE B R)``,
   RW_TAC std_ss [KRIPKE_STRUCTURE_def,SIMPLE_KRIPKE_STRUCTURE_def]);

val getS_def  = Define `getS  (S,S0,R,P,L) = S`;
val getS0_def = Define `getS0 (S,S0,R,P,L) = S0`;
val getR_def  = Define `getR  (S,S0,R,P,L) = R`;
val getP_def  = Define `getP  (S,S0,R,P,L) = P`;
val getL_def  = Define `getL  (S,S0,R,P,L) = L`;

val _ = export_theory();

