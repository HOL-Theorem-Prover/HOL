signature stringSyntax =
sig
   include Abbrev

  val char_ty           : hol_type
  val string_ty         : hol_type

  val chr_tm            : term
  val ord_tm            : term
  val implode_tm        : term
  val explode_tm        : term
  val string_tm         : term
  val emptystring_tm    : term
  val string_case_tm    : term
  val strlen_tm         : term
  val strcat_tm         : term
  val isprefix_tm       : term

  val mk_chr            : term -> term
  val mk_ord            : term -> term
  val mk_implode        : term -> term
  val mk_explode        : term -> term
  val mk_string         : term * term -> term
  val mk_string_case    : term * term * term -> term
  val mk_strlen         : term -> term
  val mk_strcat         : term * term -> term
  val mk_isprefix       : term * term -> term

  val dest_chr          : term -> term
  val dest_ord          : term -> term
  val dest_implode      : term -> term
  val dest_explode      : term -> term
  val dest_string       : term -> term * term
  val dest_string_case  : term -> term * term * term
  val dest_strlen       : term -> term
  val dest_strcat       : term -> term * term
  val dest_isprefix     : term -> term * term

  val is_chr            : term -> bool
  val is_ord            : term -> bool
  val is_implode        : term -> bool
  val is_explode        : term -> bool
  val is_string         : term -> bool
  val is_emptystring    : term -> bool
  val is_string_case    : term -> bool
  val is_strlen         : term -> bool
  val is_strcat         : term -> bool
  val is_isprefix       : term -> bool

  val fromMLchar        : char -> term
  val fromHOLchar       : term -> char
  val fromMLstring      : string -> term
  val fromHOLstring     : term -> string

  val is_char_literal   : term -> bool
  val is_string_literal : term -> bool

  val lift_char         : hol_type -> char -> term
  val lift_string       : hol_type -> string -> term

end

