(* Copyright (c) Michael Norrish *)

signature mlibOmega =
sig
  type arbint   = mlibOmegaint.int
  type 'a table = 'a mlibPatricia.t

  type factoid
  datatype 'a derivation =
         ASM of 'a
       | REAL_COMBIN of int * 'a derivation * 'a derivation
       | GCD_CHECK of 'a derivation
       | DIRECT_CONTR of 'a derivation * 'a derivation
  type 'a dfactoid = factoid * 'a derivation
  datatype 'a result = CONTR of 'a derivation
                     | SATISFIABLE of arbint table
                     | NO_CONCL
  type 'a cstdb

  val false_factoid      : factoid -> bool
  val true_factoid       : factoid -> bool
  val fromList           : int list -> factoid
  val fromArbList        : arbint list -> factoid
  val toList             : factoid -> arbint list

  exception no_gcd
  val factoid_gcd : factoid -> factoid

  val gcd_check_dfactoid : 'a dfactoid -> 'a dfactoid

  val add_check_factoid  : 'b cstdb -> 'b dfactoid ->
                           ('b cstdb -> ('b result -> 'a) -> 'a) ->
                           ('b result -> 'a) ->
                           'a

  val dbempty            : int -> 'a cstdb

  val work               : 'b cstdb -> ('b result -> 'a) -> 'a

end

(* ----------------------------------------------------------------------
    The factoid datatype

    A factoid c[0..n] represents the term
       0 <= c[0] * v_0 + .. + c[n-1] * v_{n-1} + c[n] * 1
    The factoid "key" is the vector of variable coefficients, leaving
    out the constant part.
   ---------------------------------------------------------------------- *)

(* a derivation represents a proof of a factoid *)

