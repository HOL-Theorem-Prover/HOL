(* ========================================================================= *)
(* CLAUSE = THEOREM + CONSTRAINTS                                            *)
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
type units          = mlibUnits.units

type parameters =
  {literal_order  : bool,
   term_order     : bool,
   termorder_parm : mlibTermorder.parameters}

type 'a Parmupdate = ('a -> 'a) -> parameters -> parameters
val defaults              : parameters
val update_literal_order  : bool Parmupdate
val update_term_order     : bool Parmupdate
val update_termorder_parm : mlibTermorder.parameters Parmupdate

type clause

(* Basic operations *)
val mk_clause    : parameters -> thm -> clause
val empty_clause : clause -> bool
val clause_parm  : clause -> parameters
val clause_thm   : clause -> thm  (* fails if there are coherence constraints *)
val clause_lits  : clause -> formula list
val active_lits  : clause -> (clause * int, formula) maplet list
val active_eqs   : clause -> (clause * int * bool, term) maplet list
val active_tms   : clause -> (clause * int * int list, term) maplet list
val subsumes     : clause -> clause -> bool
val demodulate   : units -> clause -> clause

(* mlibClauses with coherence constraints *)
val mk_coherent    : parameters -> formula list -> clause
val list_coherents : clause -> formula list list
val dest_coherents : (formula list * int) list -> clause -> clause

(* Rules of inference *)
val INST         : subst -> clause -> clause
val FRESH_VARS   : clause -> clause
val SYM          : clause * int -> clause
val NEQ_SIMP     : clause -> clause
val FACTOR       : clause -> clause list
val RESOLVE      : clause * int -> clause * int -> clause
val PARAMODULATE : clause * int * bool -> clause * int * int list -> clause
val REWRITE      : mlibThm.rewrs -> int * clause -> clause

(* Pretty printing *)
val show_constraints  : bool ref
val pp_clause         : clause pp
val clause_to_string' : int -> clause -> string        (* purely functional *)
val clause_to_string  : clause -> string               (* uses !LINE_LENGTH *)

end