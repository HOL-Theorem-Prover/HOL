(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Specification of SMT solvers: name, command, etc. *)

(* The main reason for having this as an opaque type is to give HolSmtLib a
   stable signature. *)

signature SolverSpec = sig

  type T

  (* see HolSmtLib.GENERIC_SMT for how the values below are used precisely, and
     see Yices.sml for a concrete solver specification *)

  (* name          : human-readable solver name
     command       : system command to execute the solver
     translation_fn: translation of HOL terms into the solver's input format;
       a string list (rather than a single string) is returned solely to
       circumvent String.maxSize, which may not be big enough for large SMT
       problems
     infile        : name of the solver's input file
     outfiles      : name of the solver's output file(s)
     is_sat_fn     : must return true (only) if the solver determined its input
       to be satisfiable, false (only) if the solver determined its input to be
       unsatisfiable, and raise HOL_ERR if neither (e.g., due to a timeout)
     model_fn      : must return a satisfying model (provided is_sat_fn ()
       returned true); NONE if the solver does not generate (or if we don't
       care about) models
     proof_fn      : must return a proof of unsatisfiability (provided
       is_sat_fn () returned false); NONE if the solver does not generate (or
       if we don't want to check) proofs of unsatisfiability *)

  val get_name           : T -> string
  val get_command        : T -> string
  val get_translation_fn : T -> Term.term -> string list
  val get_infile         : T -> string
  val get_outfiles       : T -> string list
  val get_is_sat_fn      : T -> unit -> bool
  val get_model_fn       : T -> (unit -> string) option
  val get_proof_fn       : T -> (unit -> string) option

  val set_name           : T -> string -> T
  val set_command        : T -> string -> T
  val set_translation_fn : T -> (Term.term -> string list) -> T
  val set_infile         : T -> string -> T
  val set_outfiles       : T -> string list -> T
  val set_is_sat_fn      : T -> (unit -> bool) -> T
  val set_model_fn       : T -> (unit -> string) option -> T
  val set_proof_fn       : T -> (unit -> string) option -> T

  val make_solver : string * string * (Term.term -> string list) * string *
    string list * (unit -> bool) * (unit -> string) option *
    (unit -> string) option -> T

  val dest_solver : T -> string * string * (Term.term -> string list) * string *
    string list * (unit -> bool) * (unit -> string) option *
    (unit -> string) option

end
