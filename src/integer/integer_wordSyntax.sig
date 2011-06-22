signature integer_wordSyntax = sig

  include Abbrev

  val i2w_tm                 : term
  val w2i_tm                 : term
  val int_min_tm             : term
  val int_max_tm             : term
  val uint_max_tm            : term
  val saturate_i2sw_tm       : term
  val saturate_i2w_tm        : term
  val saturate_sw2sw_tm      : term
  val saturate_sw2w_tm       : term
  val saturate_w2sw_tm       : term
  val signed_saturate_add_tm : term
  val signed_saturate_sub_tm : term

  val mk_i2w                 : term * hol_type -> term
  val mk_w2i                 : term -> term
  val mk_int_min             : hol_type -> term
  val mk_int_max             : hol_type -> term
  val mk_uint_max            : hol_type -> term
  val mk_saturate_i2sw       : term * hol_type -> term
  val mk_saturate_i2w        : term * hol_type -> term
  val mk_saturate_sw2sw      : term * hol_type -> term
  val mk_saturate_sw2w       : term * hol_type -> term
  val mk_saturate_w2sw       : term * hol_type -> term
  val mk_signed_saturate_add : term * term -> term
  val mk_signed_saturate_sub : term * term -> term

  val dest_i2w                 : term -> term
  val dest_w2i                 : term -> term
  val dest_int_min             : term -> hol_type
  val dest_int_max             : term -> hol_type
  val dest_uint_max            : term -> hol_type
  val dest_saturate_i2sw       : term -> term * hol_type
  val dest_saturate_i2w        : term -> term * hol_type
  val dest_saturate_sw2sw      : term -> term * hol_type
  val dest_saturate_sw2w       : term -> term * hol_type
  val dest_saturate_w2sw       : term -> term * hol_type
  val dest_signed_saturate_add : term -> term * term
  val dest_signed_saturate_sub : term -> term * term

  val is_i2w                 : term -> bool
  val is_w2i                 : term -> bool
  val is_int_min             : term -> bool
  val is_int_max             : term -> bool
  val is_uint_max            : term -> bool
  val is_saturate_i2sw       : term -> bool
  val is_saturate_i2w        : term -> bool
  val is_saturate_sw2sw      : term -> bool
  val is_saturate_sw2w       : term -> bool
  val is_saturate_w2sw       : term -> bool
  val is_signed_saturate_add : term -> bool
  val is_signed_saturate_sub : term -> bool

end
