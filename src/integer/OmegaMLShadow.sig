signature OmegaMLShadow =
sig

  include Abbrev
  type factoid
  datatype 'a derivation =
         ASM of 'a
       | REAL_COMBIN of int * 'a derivation * 'a derivation
       | GCD_CHECK of 'a derivation
       | DIRECT_CONTR of 'a derivation * 'a derivation
  type 'a dfactoid = factoid * 'a derivation
  datatype 'a result = CONTR of 'a derivation
                     | SATISFIABLE of Arbint.int PIntMap.t
                     | NO_CONCL
  type 'a cstdb

  val false_factoid      : factoid -> bool
  val true_factoid       : factoid -> bool
  val fromList           : int list -> factoid
  val fromArbList        : Arbint.int list -> factoid

  val term_to_dfactoid   : term list -> term -> term dfactoid
  val gcd_check_dfactoid : 'a dfactoid -> 'a dfactoid

  val add_check_factoid  : 'b cstdb -> 'b dfactoid ->
                           ('b cstdb -> ('b result -> 'a) -> 'a) ->
                           ('b result -> 'a) ->
                           'a

  val dbempty            : int -> 'a cstdb

  val work               : 'b cstdb -> ('b result -> 'a) -> 'a

end;
