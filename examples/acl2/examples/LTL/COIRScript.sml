(*****************************************************************************)
(* Cone Of Influence Reduction (COIR)                                        *)
(*****************************************************************************)

(*****************************************************************************)
(* Create "COIRTheory"                                                       *)
(*****************************************************************************)

(*
quietdec := true;                                    (* Switch off output    *)
map load
 [LTLTheory];
open
 pred_setTheory stringLib finite_mapTheory LTLTheory;
quietdec := false;                                   (* Restore output       *)
*)

(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory stringTheory
     finite_mapTheory pred_setTheory LTLTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called COIR
******************************************************************************)

val _ = new_theory "COIR";

(******************************************************************************
* Annoyance fix: stop ``I`` and ``S`` parsing to the identity and S-combinators
******************************************************************************)
val _ = hide "I";
val _ = hide "S";

(******************************************************************************
* Representation of models via equations for cone of influence reduction
******************************************************************************)


(******************************************************************************
* An equation is represented by a pair (v,e) where v is a string (the LHS)
* and E an expression (the LHS) as defined below.
* For example,
*  "x = (y + 3) - SUC q "
* would be represented by:
*  ``("x", BINOP $- (BINOP $+ (VAR "y", CONST 3), UNOP SUC (VAR "q")))``
* The dollar ($) is an escape telling the HOL parser not to parse as an infix.
* In this example the type ``:'val`` is instantiated to ``:num``.
******************************************************************************)
val exp_def =
 Hol_datatype
  `exp = CONST of 'val
       | VAR   of string
       | UNOP  of ('val -> 'val) => exp
       | BINOP of ('val -> 'val -> 'val) => (exp # exp)`;

(******************************************************************************
*
* A system (similar to a "synchronous circuit" in the book "Model
* Checking" by Clarke et al.) has a state defined by a mapping from a
* finite set of state variables (which we will represent by strings), a
* set of initial states and a transition relation defined by equations
* giving the possible values of the each variable in the next state.
*
* The equations are represented by a set of pairs (v,e) where v is a
* string (the LHS of the equation) and e is an expression (the RHS).  If
* the same variable is the LHS or more than one equation, then the
* system is non-deterministic. A deterministic system is one in which
* each state variable is the LHS of at most one equation.
*
* A system is thus a pair (I,E) where I is a set of initial states,
* represented as a value of type (string |-> 'val)set and E is the set
* of equations, represented as a value of type (string#exp)set, as
* described above. The state variables are the variables in I and E.
*
* The function MAKE_MODEL constructs a Kripke structure model from a
* system (I,E). The states are finite maps from strings to values
* (represented by type variable 'val) and atomic propositions are
* predicates on states. Thus the type of MAKE_MODEL is:
*
*   ((string |-> 'val)set # (string # ('val)exp)set))
*   ->
*   (((string |-> 'val) -> bool), (string |-> 'val))model
*
******************************************************************************)

(* Compute variables in an expression *)
val EXP_VARS_def =
 Define
  `(EXP_VARS (CONST c) = {})
   /\
   (EXP_VARS (VAR v) = {v})
   /\
   (EXP_VARS (UNOP op1 e) = EXP_VARS e)
   /\
   (EXP_VARS (BINOP op2 (e1,e2)) = EXP_VARS e1 UNION EXP_VARS e2)`;

(* Value of an expression in a state *)
val EXP_SEM_def =
 Define
  `(EXP_SEM s (CONST c) = c)
   /\
   (EXP_SEM s (VAR v) = s ' v)
   /\
   (EXP_SEM s (UNOP op1 e) = op1 (EXP_SEM s e))
   /\
   (EXP_SEM s (BINOP op2 (e1,e2)) = op2 (EXP_SEM s e1) (EXP_SEM s e2))`;

(* Mnemonic names for functions to extract LHS and RHS of equations *)
val LHS_def = Define `LHS = FST`;
val RHS_def = Define `RHS = SND`;

(* Set of all the variables mentioned in a system *)
val VARS_def =
 Define
  `VARS(I,E) =
    let init_vars = BIGUNION{FDOM s | s IN I}
    and lhs_vars  = {v | ?e. (v,e) IN E}
    and rhs_vars  = BIGUNION{EXP_VARS e | ? v. (v,e) IN E}
    in
     init_vars UNION lhs_vars UNION rhs_vars`;

val MAKE_MODEL_def =
 Define
  `MAKE_MODEL(I,E) : ((string |-> 'val)set, (string |-> 'val))model =
    <| S  := {s | T};
       R  := \(s,s').
              !v. (v IN VARS(I,E)) ==> ?e. (v,e) IN E /\ (s' ' v = EXP_SEM s e);
       L  := \s. {p | p s};
       S0 :=  I |>`;

val MODEL_MAKE_MODEL =
 store_thm
  ("MODEL_MAKE_MODEL",
   ``!I E. MODEL(MAKE_MODEL(I,E))``,
   RW_TAC (srw_ss()) [MODEL_def,MAKE_MODEL_def,SUBSET_DEF]);



(* Temporary stuff for testing

val _ = computeLib.add_persistent_funs (* Tell EVAL about finite maps *)
         [("finite_mapTheory.FUPDATE_LIST_THM",FUPDATE_LIST_THM),
          ("finite_mapTheory.DOMSUB_FUPDATE_THM",DOMSUB_FUPDATE_THM),
          ("finite_mapTheory.DOMSUB_FEMPTY",DOMSUB_FEMPTY),
          ("finite_mapTheory.FDOM_FUPDATE",FDOM_FUPDATE),
          ("finite_mapTheory.FAPPLY_FUPDATE_THM",FAPPLY_FUPDATE_THM),
          ("finite_mapTheory.FDOM_FEMPTY",FDOM_FEMPTY),
          ("finite_mapTheory.FRANGE_FUPDATE_DOMSUB",FRANGE_FUPDATE_DOMSUB),
          ("finite_mapTheory.FRANGE_FEMPTY",FRANGE_FEMPTY),
          ("pred_setTheory.IN_INSERT",pred_setTheory.IN_INSERT),
          ("pred_setTheory.NOT_IN_EMPTY",pred_setTheory.NOT_IN_EMPTY),
          ("listTheory.LIST_TO_SET_THM",listTheory.LIST_TO_SET_THM)
         ];

val sys =
 ``({(FEMPTY |++ [("x",0);("y",1);("p",3);("q",4)]);
     (FEMPTY |++ [("x",10);("y",11)])},
    {("x", CONST 0);
     ("x", UNOP SUC (VAR "x"));
     ("y", BINOP $+ (VAR "x", BINOP $* (VAR "p", VAR "y")))})``


 ``FEMPTY |++
    [("x", {CONST 0; UNOP SUC (VAR "x")});
     ("y", {BINOP $+ (VAR "x", BINOP $* (VAR "p", VAR "y"))});
     ("q", {})]``;

EVAL ``FDOM ^sys``;
EVAL ``BIGUNION(FRANGE ^sys)``;
EVAL ``IMAGE EXP_VARS (BIGUNION(FRANGE ^sys))``;
EVAL ``BIGUNION(IMAGE EXP_VARS (BIGUNION(FRANGE ^sys)))``;
EVAL ``FDOM ^sys UNION BIGUNION(IMAGE EXP_VARS (BIGUNION(FRANGE ^sys)))``;

*)


val _ = export_theory();
