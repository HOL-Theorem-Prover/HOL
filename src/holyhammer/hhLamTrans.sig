(* Lambda translation for hhProblemGen. *)
signature hhLamTrans =
sig

  type term = Term.term

  (* The slice vocabulary names the modes lifting, combs,
     combs_and_lifting and keep_lams.  The empty string denotes the legacy
     exporter and is deliberately rejected here.  The problem generator,
     rather than this module, downgrades keep_lams to lifting for formats
     without full HO syntax. *)
  datatype mode = Lifting | Combs | CombsAndLifting | KeepLams
  val mode_of_string : string -> mode
  val mode_name : mode -> string
  val valid_mode : string -> bool

  (* [translate mode formulas] closes each formula over its free variables
     (except the generated pxy. and $ symbols) and removes the abstractions
     in term position, returning the rewritten formulas and the lambda
     definitions.  Lifting replaces an abstraction by a symbol lam.<n>
     applied to its free variables, defined by the fact lam.<n>; combs
     rewrites it with the combinators I, K, S, C and o (B);
     combs_and_lifting lifts and also defines each lam.<n> by combinators,
     in lam.<n>.combs; keep_lams only eta-contracts. *)
  val translate :
    mode -> term list -> term list * (string * term) list

end
