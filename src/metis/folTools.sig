(* ========================================================================= *)
(* A HOL INTERFACE TO THE FIRST-ORDER PROVERS.                               *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature folTools =
sig

type 'a pp       = 'a mlibUseful.pp
type 'a stream   = 'a mlibStream.stream
type formula1    = mlibTerm.formula
type thm1        = mlibThm.thm
type limit       = mlibMeter.limit
type solver_node = mlibSolver.solver_node
type hol_type    = Type.hol_type
type term        = Term.term
type thm         = Thm.thm
type conv        = Abbrev.conv
type rule        = Abbrev.rule
type tactic      = Abbrev.tactic
type vars        = term list * hol_type list
  
(* First-order parameters *)
type Mparm = folMapping.parameters
type parameters =
  {equality   : bool,              (* Add equality axioms if needed *)
   boolean    : bool,              (* Add rules for reasoning about booleans *)
   combinator : bool,              (* Add combinator reduction rules *)
   mapping    : Mparm}

val defaults               : parameters
val update_parm_equality   : (bool -> bool) -> parameters -> parameters
val update_parm_boolean    : (bool -> bool) -> parameters -> parameters
val update_parm_combinator : (bool -> bool) -> parameters -> parameters
val update_parm_mapping    : (Mparm -> Mparm) -> parameters -> parameters

(* If recent_fol_problems is set to NONE then nothing happens (the default). *)
(* If it is set to SOME l then every compiled FOL problem is cons'ed to l. *)
type fol_problem = {thms : thm1 list, hyps : thm1 list, query : formula1 list}
val recent_fol_problems : fol_problem list option ref

(* Logic maps manage the interface between HOL and first-order logic *)
type logic_map
val new_map      : parameters -> logic_map
val empty_map    : logic_map                      (* Uses defaults *)
val add_thm      : vars * thm -> logic_map -> logic_map
val add_hyp      : vars * thm -> logic_map -> logic_map
val add_const    : string -> logic_map -> logic_map
val pp_logic_map : logic_map pp

(* A pure interface to the first-order solver: no normalization *)
type Query      = vars * term list
type Result     = vars * thm list
val FOL_SOLVER : solver_node -> logic_map -> limit -> Query -> Result stream

(* HOL normalization to first-order clausal form *)
val FOL_NORM_CONV : conv
val FOL_NORM_RULE : rule

(* An interface to first-order solvers with normalization *)
type Init = {parm : parameters, thms : thm list, hyps : thm list, lim : limit}
val FOL_SOLVE  : solver_node -> Init -> Query -> Result stream
val FOL_FIND   : solver_node -> Init -> Query -> Result
val FOL_REFUTE : solver_node -> Init -> thm

(* Stripping, elimination of choice operator (@), then FOL_NORM_CONV *)
val FOL_NORM_TAC : tactic

(* Calling the first-order prover from a HOL tactic *)
val FOL_TAC : solver_node * parameters * limit -> thm list -> tactic

end
