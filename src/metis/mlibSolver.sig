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

(* Solver nodes must construct themselves from the following form. *)

type form =
  {slice : meter ref,                   (* A meter to stop after each slice *)
   units : units ref,                   (* Solvers share a unit cache *)
   thms  : thm list,                    (* Context, assumed consistent *)
   hyps  : thm list}                    (* Hypothesis, or set of support *)

(* Solver nodes also incorporate a name. *)

type node_data = {name : string, solver_con : form -> solver}
type solver_node

val mk_solver_node : node_data -> solver_node
val pp_solver_node : solver_node pp

(* At each step we schedule a time slice to the least cost solver node. *)

val SLICE : limit ref

type cost_fn = meter_reading -> real

val once_only : cost_fn                 (* Time taken (in seconds) *)
val time1     : cost_fn                 (* Time taken (in seconds) *)
val time2     : cost_fn                 (* Time squared *)
val infs1     : cost_fn                 (* Number of inferences made*)
val infs2     : cost_fn                 (* Inferences squared *)

(* This allows us to hierarchically arrange solver nodes. *)

val combine : (cost_fn * solver_node) list -> solver_node

(* Overriding the 'natural' set of support from the problem. *)

val set_of_support : (thm -> bool) -> solver_node -> solver_node
val everything     : thm -> bool
val one_negative   : thm -> bool
val one_positive   : thm -> bool
val all_negative   : thm -> bool        (* This one is used by mlibMetis.prove *)
val all_positive   : thm -> bool
val nothing        : thm -> bool

(* Initializing a solver node makes it ready for action. *)

type init_data = {limit : limit, thms : thm list, hyps : thm list}

val initialize : solver_node -> init_data -> solver

end
