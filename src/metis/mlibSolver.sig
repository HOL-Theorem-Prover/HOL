(* ========================================================================= *)
(* PACKAGING UP SOLVERS TO ALLOW THEM TO COOPERATE UNIFORMLY                 *)
(* Created by Joe Hurd, March 2002                                           *)
(* ========================================================================= *)

signature mlibSolver =
sig

type 'a pp         = 'a mlibUseful.pp
type 'a stream     = 'a mlibStream.stream
type formula       = mlibTerm.formula
type thm           = mlibThm.thm
type limit         = mlibMeter.limit
type meter         = mlibMeter.meter
type meter_reading = mlibMeter.meter_reading
type units         = mlibUnits.units

(* The type of a generic solver *)

type solver = formula list -> thm list option stream

val contradiction_solver : thm -> solver

(* Filters to cut off searching or drop subsumed solutions *)

val solved_filter   : solver -> solver
val subsumed_filter : solver -> solver

(* User-friendly interface to generic solvers *)

val solve  : solver -> int -> formula list -> thm list list
val find   : solver -> formula list -> thm list option
val refute : solver -> thm option

(* mlibSolver nodes must construct themselves from the following form. *)

type form =
  {slice : meter ref,                   (* A meter to stop after each slice *)
   units : units ref,                   (* mlibSolvers share a unit cache *)
   thms  : thm list,                    (* Context, assumed consistent *)
   hyps  : thm list}                    (* Hypothesis, or set of support *)

(* mlibSolver nodes also incorporate a name. *)

type node_data = {name : string, solver_con : form -> solver}
type solver_node

val mk_solver_node : node_data -> solver_node
val pp_solver_node : solver_node pp

(* At each step we schedule a time slice to the least cost solver node. *)

val SLICE : limit ref

type cost_fn
val once_only  : cost_fn          (* The solver is used for one slice         *)
val time_power : real -> cost_fn  (* Time used (in seconds) raised to a power *)
val infs_power : real -> cost_fn  (* Inferences used raised to a power        *)
val pp_cost_fn : cost_fn pp

(* This allows us to hierarchically arrange solver nodes. *)

val combine : (cost_fn * solver_node) list -> solver_node

(* Overriding the 'natural' set of support from the problem. *)

type sos_filter = {name : string, filter : thm -> bool}
val apply_sos_filter : sos_filter -> solver_node -> solver_node

val everything   : sos_filter
val one_negative : sos_filter
val one_positive : sos_filter
val all_negative : sos_filter     (* This one is used by mlibMetis.prove *)
val all_positive : sos_filter

(* Initializing a solver node makes it ready for action. *)

type init_data = {limit : limit, thms : thm list, hyps : thm list}

val initialize : solver_node -> init_data -> solver

end
