signature OmegaMLShadow =
sig

  include Abbrev
  type factoid
  datatype derivation =
         ASM of term
       | REAL_COMBIN of int * derivation * derivation
       | GCD_CHECK of derivation
       | DIRECT_CONTR of derivation * derivation
  type dfactoid = factoid * derivation
  datatype result = CONTR of derivation
                  | SATISFIABLE of Arbint.int PIntMap.t
                  | NO_CONCL
  type cstdb

  val false_factoid      : factoid -> bool
  val true_factoid       : factoid -> bool

  val term_to_dfactoid   : term -> dfactoid
  val gcd_check_dfactoid : dfactoid -> dfactoid

  val add_check_factoid  : cstdb -> dfactoid ->
                           (cstdb -> (result -> 'a) -> 'a) ->
                           (result -> 'a) ->
                           'a

  val dbempty            : int -> cstdb

  val work               : cstdb -> (result -> 'a) -> 'a

end;
