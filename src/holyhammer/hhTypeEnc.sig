signature hhTypeEnc =
sig

  type hol_type = Type.hol_type
  type term = Term.term

  datatype type_level = AllTypes | NonmonoNonUniform
  datatype type_enc =
      Native of {higher : bool, fool : bool, poly : bool}
    | Guards of {poly : bool, level : type_level}
    | LegacySP

  (* The formats are fof, tf0, tf1, tx0, tx0- (tx0 without $ite and
     $let), th0 and th1 (th0 with polymorphism and $ite). *)
  val format_of_string : string -> hhTptpProblem.format
  val valid_format : string -> bool

  (* The accepted slice vocabulary is precisely mono_native,
     mono_native_fool, mono_native_higher, mono_native_higher_fool,
     poly_native, mono_guards, mono_guards??, and the empty legacy
     encoding.  THF implies the higher encoding: the generator treats a
     native encoding in THF as higher, and the problem header names the
     requested encoding. *)
  val of_string : string -> type_enc
  val to_string : type_enc -> string

  (* Fits an encoding to a format: under fof a native encoding becomes
     mono_guards; under tff it loses higher; under tff and thf FOOL and
     polymorphism are kept only where the format has them.  Guards and
     the legacy encoding fail outside fof. *)
  val adjust_type_enc : hhTptpProblem.format -> type_enc -> type_enc

  (* A conservative datatype-introspection oracle.  False means only that
     infiniteness has not been established. *)
  val surely_infinite : hol_type -> bool

  (* The distinct types that mono_guards?? guards: bool and the types of
     possibly universal naked variables in equations that are not
     negative, or as arguments of the equality proxy (an application
     headed by a constant or variable named pxy.eq), except types proved
     infinite by surely_infinite.  As in Sledgehammer, a variable is
     possibly universal when it is free in a fact or bound by a
     quantifier that is universal once the conjecture is negated or whose
     polarity is unknown (under an iff), and an equation under an iff has
     unknown polarity.  The inputs are HOL formulas after lambda handling
     and monomorphization: the conjecture and every fact of the problem. *)
  val types_needing_encoding :
    {conjecture : term, facts : term list} -> hol_type list

end
