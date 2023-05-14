(* ========================================================================= *)
(* FILE          : Compute.sig                                               *)
(* DESCRIPTION   : Interpreter for first-order lisp-style terms with natural *)
(*                 numbers.                                                  *)
(*                                                                           *)
(* AUTHORS       : (c) Oskar Abrahamsson, Magnus O. Myreen                   *)
(* DATE          : May 2023, Oskar Abrahamsson                               *)
(* ========================================================================= *)

signature Compute =
sig

  type hol_type = Type.hol_type
  type term = Term.term

  val term_compute :
    (* initialization: *)
    { cval_terms : (string * term) list,
      cval_type  : hol_type,
      num_type   : hol_type,
      char_eqns  : (string * term) list }
    (* code equations: *)
    -> term list
    -> term -> term

end (* sig *)

