signature Refute_Gen = sig
  type term = Term.term
  type hol_type = Type.hol_type

  val enum_cap : int

  datatype numkind = Num | Int | Char | Word of int

  type rng = IntInf.int

  type custom_gen =
    { enumerate : (int -> term list) option,
      random : (int -> rng -> term * rng) option }

  datatype genspec =
      GenDatatype of
        { constrs : (term * hol_type list) list,
          exhaustive : bool,
          recursive : bool list list,
          min_size : int list list,
          (* One entry per constructor: is any argument type recursive
             under a function type?  Constant for a spec, so precomputed
             here rather than re-traversed per generated value. *)
          fun_recursive : bool list,
          family : hol_type list }
    | GenEnum of term list
    | GenNum of numkind
    | GenFun of hol_type * hol_type
    | GenCustom of hol_type * custom_gen

  exception NoGenerator of hol_type * string

  val predicate_of : hol_type -> term option
  val has_registered_generator : hol_type -> bool
  val register_generator : hol_type -> custom_gen -> unit
  val register_generator_family :
    {canonical : (term -> term) option,
     constructors : term list,
     tyop : {Thy : string, Tyop : string}} ->
    unit
  val snapshot_family_canonicals : unit -> hol_type -> (term -> term) option
  val is_family_constructor : term -> bool
  val own_floor : genspec -> int
  val spec_of : hol_type -> genspec
  val type_recursive_under_function : hol_type -> bool
  val abstract_generator :
    {constructors : term list, pred : term option, ty : hol_type} -> unit
  val narrowing_terms : numkind -> int -> term list
  val cardinality : hol_type -> int option
  val enumerate : hol_type -> term list option
end
