(* ========================================================================= *)
(* CLAUSE = ID + THEOREM + CONSTRAINTS                                       *)
(* Created by Joe Hurd, September 2002                                       *)
(* ========================================================================= *)

signature mlibClause =
sig

type ('a,'b) maplet = ('a,'b) mlibUseful.maplet
type 'a pp          = 'a mlibUseful.pp
type term           = mlibTerm.term
type formula        = mlibTerm.formula
type subst          = mlibSubst.subst
type thm            = mlibThm.thm
type termorder      = mlibTermorder.termorder

type parameters =
  {term_order       : bool,
   literal_order    : bool,
   order_stickiness : int,       (* Stickiness of ordering constraints: 0..3 *)
   termorder_parm   : mlibTermorder.parameters}

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults                : parameters
val update_term_order       : bool parmupdate
val update_literal_order    : bool parmupdate
val update_order_stickiness : int parmupdate
val update_termorder_parm   : mlibTermorder.parameters parmupdate

type clause

(* Basic operations *)
type bits = {parm : parameters, id : int, thm : thm, order : termorder}
val mk_clause   : parameters -> thm -> clause
val dest_clause : clause -> bits
val literals    : clause -> formula list
val is_empty    : clause -> bool
val is_rewr     : clause -> bool

(* Using ordering constraints to cut down the set of possible inferences *)
val largest_lits : clause -> (clause * int, formula) maplet list
val largest_eqs  : clause -> (clause * int * bool, term) maplet list
val largest_tms  : clause -> (clause * int * int list, term) maplet list
val drop_order   : clause -> clause

(* Subsumption *)
val subsumes : clause -> clause -> bool

(* mlibClause rewriting *)
type rewrs
val empty    : parameters -> rewrs
val size     : rewrs -> int
val add      : clause -> rewrs -> rewrs
val reduce   : rewrs -> rewrs
val eqns     : rewrs -> clause list
val pp_rewrs : rewrs pp

(* Simplifying rules: these preserve the clause id *)
val INST       : subst -> clause -> clause
val FRESH_VARS : clause -> clause
val NEQ_VARS   : clause -> clause
val DEMODULATE : mlibUnits.units -> clause -> clause
val REWRITE    : rewrs -> clause -> clause

(* Ordered resolution and paramodulation: these generate new clause ids *)
val FACTOR       : clause -> clause list
val RESOLVE      : clause * int -> clause * int -> clause
val PARAMODULATE : clause * int * bool -> clause * int * int list -> clause

(* Pretty printing *)
val show_id         : bool ref
val show_constraint : bool ref
val pp_clause       : clause pp

end
