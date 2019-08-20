signature regexpSyntax =
sig
  include Abbrev

  val charset_ty : hol_type
  val regexp_ty  : hol_type

  val chset_tm   : term
  val cat_tm     : term
  val star_tm    : term
  val or_tm      : term
  val neg_tm     : term
  val and_tm     : term
  val regexp_lang_tm : term

  val mk_chset   : term -> term
  val mk_star    : term -> term
  val mk_neg     : term -> term
  val mk_cat     : term * term -> term
  val mk_or      : term list -> term
  val mk_and     : term * term -> term
  val mk_regexp_lang : term -> term

  val dest_chset : term -> term
  val dest_cat   : term -> term * term
  val dest_star  : term -> term
  val dest_neg   : term -> term
  val dest_or    : term -> term list
  val dest_and   : term -> term * term
  val dest_regexp_lang : term -> term

  val is_chset   : term -> bool
  val is_cat     : term -> bool
  val is_star    : term -> bool
  val is_neg     : term -> bool
  val is_or      : term -> bool
  val is_and     : term -> bool
  val is_regexp_lang : term -> bool

  val vector_tm  : term
  val mk_vector  : term -> term
  val dest_vector : term -> term

  val regexp_matcher_tm   : term
  val mk_regexp_matcher   : term * term -> term
  val dest_regexp_matcher : term -> term * term
  val is_regexp_matcher   : term -> bool

  val charset_to_term  : Regexp_Type.charset -> term
  val term_to_charset  : term -> Regexp_Type.charset
  val regexp_to_term   : Regexp_Type.regexp -> term
  val term_to_regexp   : term -> Regexp_Type.regexp

  val charset_empty_tm : term
  val charset_full_tm  : term
  val empty_tm         : term
  val dot_tm           : term
  val epsilon_tm       : term
  val dot_star_tm      : term

end
