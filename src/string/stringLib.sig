signature stringLib =
sig
   include Abbrev

   val char_ty        : hol_type
   val string_ty      : hol_type

   val chr_tm         : term
   val ord_tm         : term
   val implode_tm     : term
   val explode_tm     : term
   val string_tm      : term
   val emptystring_tm : term

   val mk_chr         : term -> term
   val mk_ord         : term -> term
   val mk_implode     : term -> term
   val mk_explode     : term -> term
   val mk_string      : term * term -> term

   val dest_chr       : term -> term
   val dest_ord       : term -> term
   val dest_implode   : term -> term
   val dest_explode   : term -> term
   val dest_string    : term -> term * term

   val is_chr         : term -> bool
   val is_ord         : term -> bool
   val is_implode     : term -> bool
   val is_explode     : term -> bool
   val is_string      : term -> bool
   val is_emptystring : term -> bool

   val fromMLchar     : char -> term
   val fromHOLchar    : term -> char
   val fromMLstring   : string -> term
   val fromHOLstring  : term -> string

   val ORD_CHR_CONV   : conv
   val char_EQ_CONV   : conv
   val string_EQ_CONV : conv

   val add_string_compset : computeLib.compset -> unit

   val Define_enum2string : hol_type -> thm
   val Define_string2enum : hol_type -> thm
end
