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
  structure Map : sig
    type 'a t
    exception NotFound
    val items : 'a t -> (int * 'a dfactoid list) list
    val add : int -> 'a dfactoid list -> 'a t -> 'a t
    val find : 'a t -> int -> 'a dfactoid list (* exn NotFound *)
    val width : 'a t -> int
    val size : 'a t -> int
    val empty : int -> 'a t
  end
  datatype 'a result = CONTR of 'a derivation
                     | SATISFIABLE of Arbint.int PIntMap.t
                     | NO_CONCL

  val false_factoid      : factoid -> bool
  val true_factoid       : factoid -> bool
  val fromList           : int list -> factoid
  val fromArbList        : Arbint.int list -> factoid
  val toArbVector        : factoid -> Arbint.int vector

  val term_to_dfactoid   : term list -> term -> term dfactoid
  val gcd_check_dfactoid : 'a dfactoid -> 'a dfactoid

  val add_check_factoid  : 'b Map.t -> 'b dfactoid ->
                           ('b Map.t -> ('b result -> 'a) -> 'a) ->
                           ('b result -> 'a) ->
                           'a

  val dbempty            : int -> 'a Map.t

  val work               : 'b Map.t -> ('b result -> 'a) -> 'a

end
