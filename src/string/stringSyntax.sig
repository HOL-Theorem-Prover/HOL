signature stringSyntax =
sig
   include Abbrev

  val char_ty           : hol_type
  val string_ty         : hol_type

  val char_ge_tm : term
  val char_gt_tm : term
  val char_le_tm : term
  val char_lt_tm : term
  val chr_tm : term
  val emptystring_tm : term
  val explode_tm : term
  val extract_tm : term
  val fields_tm : term
  val implode_tm : term
  val isalpha_tm : term
  val isalphanum_tm : term
  val isascii_tm : term
  val iscntrl_tm : term
  val isdigit_tm : term
  val isgraph_tm : term
  val ishexdigit_tm : term
  val islower_tm : term
  val isprefix_tm : term
  val isprint_tm : term
  val ispunct_tm : term
  val isspace_tm : term
  val isupper_tm : term
  val ord_tm : term
  val str_tm : term
  val strcat_tm : term
  val stri : term -> term
  val string_case_tm : term
  val string_ge_tm : term
  val string_gt_tm : term
  val string_le_tm : term
  val string_lt_tm : term
  val string_tm : term
  val strlen_tm : term
  val sub_tm : term
  val substring_tm : term
  val tochar_tm : term
  val tokens_tm : term
  val tolower_tm : term
  val toupper_tm : term
  val translate_tm : term

  val mk_char_ge : term * term -> term
  val mk_char_gt : term * term -> term
  val mk_char_le : term * term -> term
  val mk_char_lt : term * term -> term
  val mk_chr : term -> term
  val mk_dest_string : term -> term
  val mk_explode : term -> term
  val mk_extract : term -> term
  val mk_fields : term * term -> term
  val mk_implode : term -> term
  val mk_isalpha : term -> term
  val mk_isalphanum : term -> term
  val mk_isascii : term -> term
  val mk_iscntrl : term -> term
  val mk_isdigit : term -> term
  val mk_isgraph : term -> term
  val mk_ishexdigit : term -> term
  val mk_islower : term -> term
  val mk_isprefix : term * term -> term
  val mk_isprint : term -> term
  val mk_ispunct : term -> term
  val mk_isspace : term -> term
  val mk_isupper : term -> term
  val mk_ord : term -> term
  val mk_str : term -> term
  val mk_strcat : term * term -> term
  val mk_string : term * term -> term
  val mk_string_case : term * term * term -> term
  val mk_string_ge : term * term -> term
  val mk_string_gt : term * term -> term
  val mk_string_le : term * term -> term
  val mk_string_lt : term * term -> term
  val mk_strlen : term -> term
  val mk_sub : term -> term
  val mk_substring : term -> term
  val mk_tochar : term -> term
  val mk_tokens : term * term -> term
  val mk_tolower : term -> term
  val mk_toupper : term -> term
  val mk_translate : term * term -> term

  val dest_char_ge : term -> term * term
  val dest_char_gt : term -> term * term
  val dest_char_le : term -> term * term
  val dest_char_lt : term -> term * term
  val dest_chr : term -> term
  val dest_dest_string : term -> term
  val dest_explode : term -> term
  val dest_extract : term -> term
  val dest_fields : term -> term * term
  val dest_implode : term -> term
  val dest_isalpha : term -> term
  val dest_isalphanum : term -> term
  val dest_isascii : term -> term
  val dest_iscntrl : term -> term
  val dest_isdigit : term -> term
  val dest_isgraph : term -> term
  val dest_ishexdigit : term -> term
  val dest_islower : term -> term
  val dest_isprefix : term -> term * term
  val dest_isprint : term -> term
  val dest_ispunct : term -> term
  val dest_isspace : term -> term
  val dest_isupper : term -> term
  val dest_ord : term -> term
  val dest_str : term -> term
  val dest_strcat : term -> term * term
  val dest_string : term -> term * term
  val dest_string_case : term -> term * term * term
  val dest_string_ge : term -> term * term
  val dest_string_gt : term -> term * term
  val dest_string_le : term -> term * term
  val dest_string_lt : term -> term * term
  val dest_string_tm : term
  val dest_strlen : term -> term
  val dest_sub : term -> term
  val dest_substring : term -> term
  val dest_tochar : term -> term
  val dest_tokens : term -> term * term
  val dest_tolower : term -> term
  val dest_toupper : term -> term
  val dest_translate : term -> term * term

  val is_char_ge : term -> bool
  val is_char_gt : term -> bool
  val is_char_le : term -> bool
  val is_char_lt : term -> bool
  val is_chr : term -> bool
  val is_dest_string : term -> bool
  val is_emptystring : term -> bool
  val is_fields : term -> bool
  val is_explode : term -> bool
  val is_extract : term -> bool
  val is_implode : term -> bool
  val is_isalpha : term -> bool
  val is_isalphanum : term -> bool
  val is_isascii : term -> bool
  val is_iscntrl : term -> bool
  val is_isdigit : term -> bool
  val is_isgraph : term -> bool
  val is_ishexdigit : term -> bool
  val is_islower : term -> bool
  val is_isprefix : term -> bool
  val is_isprint : term -> bool
  val is_ispunct : term -> bool
  val is_isspace : term -> bool
  val is_isupper : term -> bool
  val is_ord : term -> bool
  val is_str : term -> bool
  val is_strcat : term -> bool
  val is_string : term -> bool
  val is_string_case : term -> bool
  val is_string_ge : term -> bool
  val is_string_gt : term -> bool
  val is_string_le : term -> bool
  val is_string_lt : term -> bool
  val is_strlen : term -> bool
  val is_sub : term -> bool
  val is_substring : term -> bool
  val is_tochar : term -> bool
  val is_tokens : term -> bool
  val is_tolower : term -> bool
  val is_toupper : term -> bool
  val is_translate : term -> bool

  val fromMLchar        : char -> term
  val fromHOLchar       : term -> char
  val fromMLstring      : string -> term
  val fromHOLstring     : term -> string

  val is_char_literal   : term -> bool
  val is_string_literal : term -> bool

  val lift_char         : hol_type -> char -> term
  val lift_string       : hol_type -> string -> term

end

