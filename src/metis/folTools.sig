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
type parameters =
  {equality     : bool,     (* Add equality axioms if needed *)
   combinator   : bool,     (* Add combinator reduction rules *)
   boolean      : bool,     (* Add rules for reasoning about booleans *)
   mapping_parm : folMapping.parameters}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults            : parameters
val update_equality     : bool parmupdate
val update_combinator   : bool parmupdate
val update_boolean      : bool parmupdate
val update_mapping_parm : folMapping.parameters parmupdate

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
val build_map    : parameters * string list * thm list -> logic_map
val pp_logic_map : logic_map pp

(* A pure interface to the first-order solver: no normalization *)
type Query  = vars * term list
type Result = vars * thm list
val FOL_SOLVE  : solver_node -> logic_map -> limit -> Query -> Result stream
val FOL_FIND   : solver_node -> logic_map -> limit -> Query -> Result
val FOL_REFUTE : solver_node -> logic_map -> limit -> thm
val FOL_TACTIC : solver_node -> logic_map -> limit -> tactic

(* HOL normalization to conjunctive normal form *)
val FOL_NORM      : thm list -> string list * thm list  (* Definitional CNF *)
val FOL_NORM_TAC  : tactic                  (* Stripping + Elimination of @ *)
val FOL_NORM_TTAC : (string list * thm list -> tactic) -> thm list -> tactic

(* Reading in TPTP problems *)
val tptp_read : {filename : string} -> term

end
