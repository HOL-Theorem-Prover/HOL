signature hhTypeEnc =
sig

  type hol_type = Type.hol_type
  type term = Term.term

  datatype type_level = AllTypes | NonmonoNonUniform
  datatype type_enc =
      Native of {higher : bool, fool : bool, poly : bool}
    | Guards of {poly : bool, level : type_level}
    | LegacySP

  (* The accepted slice vocabulary is precisely mono_native,
     mono_native_fool, mono_native_higher, mono_native_higher_fool,
     poly_native, mono_guards, mono_guards??, and the empty legacy
     encoding. *)
  val format_of_string : string -> hhTptpProblem.format
  val valid_format : string -> bool
  val of_string : string -> type_enc
  val to_string : type_enc -> string
  val adjust_type_enc : hhTptpProblem.format -> type_enc -> type_enc

  (* A conservative datatype-introspection oracle.  False means only that
     infiniteness has not been established. *)
  val surely_infinite : hol_type -> bool

  (* This is run after lambda handling and first-orderization.  Its inputs
     are HOL formulas: universal quantifiers are boolSyntax.mk_forall,
     equality is boolSyntax.mk_eq, and the first-order equality proxy is an
     application headed by a constant or variable named fequal or pxy.eq.
     Free variables are treated as implicitly universal.  It returns the
     distinct types which require mono_guards?? encoding: bool and the
     types of possibly universal naked variables in positive equality or
     fequal occurrences, except types proved infinite by surely_infinite.
     The generator passes its complete formula list in one call. *)
  val types_needing_encoding : term list -> hol_type list

end
