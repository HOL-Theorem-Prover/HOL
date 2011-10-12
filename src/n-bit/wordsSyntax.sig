signature wordsSyntax =
sig

  include Abbrev
  type num = Arbnum.num

  val mk_word_type      : hol_type -> hol_type
  val dest_word_type    : hol_type -> hol_type
  val is_word_type      : hol_type -> bool
  val dim_of            : term -> hol_type

  val mk_int_word_type  : int -> hol_type

  val mk_word           : num * num -> term
  val mk_wordi          : num * int -> term
  val mk_wordii         : int * int -> term

  val fcp_index_tm        : term
  val dimindex_tm         : term
  val dimword_tm          : term
  val word_T_tm           : term
  val word_L_tm           : term
  val word_H_tm           : term
  val word_L2_tm          : term
  val uint_max_tm         : term
  val int_min_tm          : term
  val int_max_tm          : term
  val word_modify_tm      : term
  val word_reverse_tm     : term
  val word_compare_tm     : term
  val nzcv_tm             : term
  val word_lt_tm          : term
  val word_le_tm          : term
  val word_gt_tm          : term
  val word_ge_tm          : term
  val word_add_tm         : term
  val word_sub_tm         : term
  val word_rrx_tm         : term
  val word_mul_tm         : term
  val word_log2_tm        : term
  val word_msb_tm         : term
  val word_lsb_tm         : term
  val word_join_tm        : term
  val word_concat_tm      : term
  val word_div_tm         : term
  val word_sdiv_tm        : term
  val word_mod_tm         : term
  val word_srem_tm        : term
  val word_smod_tm        : term
  val word_slice_tm       : term
  val word_bit_tm         : term
  val word_bits_tm        : term
  val word_extract_tm     : term
  val word_lsl_tm         : term
  val word_lsr_tm         : term
  val word_asr_tm         : term
  val word_ror_tm         : term
  val word_rol_tm         : term
  val word_lsl_bv_tm      : term
  val word_lsr_bv_tm      : term
  val word_asr_bv_tm      : term
  val word_ror_bv_tm      : term
  val word_rol_bv_tm      : term
  val word_hi_tm          : term
  val word_lo_tm          : term
  val word_hs_tm          : term
  val word_ls_tm          : term
  val word_and_tm         : term
  val word_or_tm          : term
  val word_xor_tm         : term
  val word_nand_tm        : term
  val word_nor_tm         : term
  val word_xnor_tm        : term
  val word_1comp_tm       : term
  val word_2comp_tm       : term
  val word_replicate_tm   : term
  val word_reduce_tm      : term
  val reduce_and_tm       : term
  val reduce_or_tm        : term
  val reduce_xor_tm       : term
  val reduce_nand_tm      : term
  val reduce_nor_tm       : term
  val reduce_xnor_tm      : term
  val concat_word_list_tm : term
  val bit_field_insert_tm : term
  val w2w_tm              : term
  val n2w_tm              : term
  val w2n_tm              : term
  val sw2sw_tm            : term
  val saturate_n2w_tm     : term
  val saturate_w2w_tm     : term
  val saturate_add_tm     : term
  val saturate_sub_tm     : term
  val saturate_mul_tm     : term

  val mk_index            : term * term -> term
  val mk_dimindex         : hol_type -> term
  val mk_dimword          : hol_type -> term
  val mk_word_T           : hol_type -> term
  val mk_word_L           : hol_type -> term
  val mk_word_H           : hol_type -> term
  val mk_word_L2          : hol_type -> term
  val mk_uint_max         : hol_type -> term
  val mk_int_min          : hol_type -> term
  val mk_int_max          : hol_type -> term
  val mk_word_modify      : term * term -> term
  val mk_word_reverse     : term -> term
  val mk_word_compare     : term * term -> term
  val mk_nzcv             : term * term -> term
  val mk_word_lt          : term * term -> term
  val mk_word_le          : term * term -> term
  val mk_word_gt          : term * term -> term
  val mk_word_ge          : term * term -> term
  val mk_word_add         : term * term -> term
  val mk_word_sub         : term * term -> term
  val mk_word_mul         : term * term -> term
  val mk_word_rrx         : term * term -> term
  val mk_word_join        : term * term -> term
  val mk_word_concat      : term * term -> term
  val mk_word_div         : term * term -> term
  val mk_word_sdiv        : term * term -> term
  val mk_word_mod         : term * term -> term
  val mk_word_srem        : term * term -> term
  val mk_word_smod        : term * term -> term
  val mk_word_log2        : term -> term
  val mk_word_msb         : term -> term
  val mk_word_lsb         : term -> term
  val mk_word_slice       : term * term * term -> term
  val mk_word_bits        : term * term * term -> term
  val mk_word_bit         : term * term -> term
  val mk_word_extract     : term * term * term * hol_type -> term
  val mk_word_lsl         : term * term -> term
  val mk_word_lsr         : term * term -> term
  val mk_word_asr         : term * term -> term
  val mk_word_ror         : term * term -> term
  val mk_word_rol         : term * term -> term
  val mk_word_lsl_bv      : term * term -> term
  val mk_word_lsr_bv      : term * term -> term
  val mk_word_asr_bv      : term * term -> term
  val mk_word_ror_bv      : term * term -> term
  val mk_word_rol_bv      : term * term -> term
  val mk_word_hi          : term * term -> term
  val mk_word_lo          : term * term -> term
  val mk_word_hs          : term * term -> term
  val mk_word_ls          : term * term -> term
  val mk_word_and         : term * term -> term
  val mk_word_or          : term * term -> term
  val mk_word_xor         : term * term -> term
  val mk_word_nand        : term * term -> term
  val mk_word_nor         : term * term -> term
  val mk_word_xnor        : term * term -> term
  val mk_word_replicate   : term * term -> term
  val mk_word_reduce      : term * term -> term
  val mk_reduce_and       : term -> term
  val mk_reduce_or        : term -> term
  val mk_reduce_xor       : term -> term
  val mk_reduce_nand      : term -> term
  val mk_reduce_nor       : term -> term
  val mk_reduce_xnor      : term -> term
  val mk_word_1comp       : term -> term
  val mk_word_2comp       : term -> term
  val mk_concat_word_list : term -> term
  val mk_bit_field_insert : term * term * term * term -> term
  val mk_w2w              : term * hol_type -> term
  val mk_n2w              : term * hol_type -> term
  val mk_w2n              : term -> term
  val mk_sw2sw            : term * hol_type -> term
  val mk_saturate_n2w     : term * hol_type -> term
  val mk_saturate_w2w     : term * hol_type -> term
  val mk_saturate_add     : term * term -> term
  val mk_saturate_sub     : term * term -> term
  val mk_saturate_mul     : term * term -> term

  val dest_index            : term -> term * term
  val dest_dimindex         : term -> hol_type
  val dest_dimword          : term -> hol_type
  val dest_word_T           : term -> hol_type
  val dest_word_L           : term -> hol_type
  val dest_word_H           : term -> hol_type
  val dest_word_L2          : term -> hol_type
  val dest_uint_max         : term -> hol_type
  val dest_int_min          : term -> hol_type
  val dest_int_max          : term -> hol_type
  val dest_word_modify      : term -> term * term
  val dest_word_reverse     : term -> term
  val dest_word_compare     : term -> term * term
  val dest_nzcv             : term -> term * term
  val dest_word_lt          : term -> term * term
  val dest_word_le          : term -> term * term
  val dest_word_gt          : term -> term * term
  val dest_word_ge          : term -> term * term
  val dest_word_add         : term -> term * term
  val dest_word_sub         : term -> term * term
  val dest_word_mul         : term -> term * term
  val dest_word_rrx         : term -> term
  val dest_word_join        : term -> term * term
  val dest_word_concat      : term -> term * term
  val dest_word_div         : term -> term * term
  val dest_word_sdiv        : term -> term * term
  val dest_word_mod         : term -> term * term
  val dest_word_srem        : term -> term * term
  val dest_word_smod        : term -> term * term
  val dest_word_log2        : term -> term
  val dest_word_msb         : term -> term
  val dest_word_lsb         : term -> term
  val dest_word_slice       : term -> term * term * term
  val dest_word_bits        : term -> term * term * term
  val dest_word_bit         : term -> term * term
  val dest_word_extract     : term -> term * term * term * hol_type
  val dest_word_lsl         : term -> term * term
  val dest_word_lsr         : term -> term * term
  val dest_word_asr         : term -> term * term
  val dest_word_ror         : term -> term * term
  val dest_word_rol         : term -> term * term
  val dest_word_lsl_bv      : term -> term * term
  val dest_word_lsr_bv      : term -> term * term
  val dest_word_asr_bv      : term -> term * term
  val dest_word_ror_bv      : term -> term * term
  val dest_word_rol_bv      : term -> term * term
  val dest_word_hi          : term -> term * term
  val dest_word_lo          : term -> term * term
  val dest_word_hs          : term -> term * term
  val dest_word_ls          : term -> term * term
  val dest_word_and         : term -> term * term
  val dest_word_xor         : term -> term * term
  val dest_word_or          : term -> term * term
  val dest_word_nand        : term -> term * term
  val dest_word_xnor        : term -> term * term
  val dest_word_nor         : term -> term * term
  val dest_word_replicate   : term -> term * term
  val dest_word_reduce      : term -> term * term
  val dest_reduce_and       : term -> term
  val dest_reduce_or        : term -> term
  val dest_reduce_xor       : term -> term
  val dest_reduce_nand      : term -> term
  val dest_reduce_nor       : term -> term
  val dest_reduce_xnor      : term -> term
  val dest_word_1comp       : term -> term
  val dest_word_2comp       : term -> term
  val dest_concat_word_list : term -> term
  val dest_bit_field_insert : term -> term * term * term * term
  val dest_w2w              : term -> term * hol_type
  val dest_n2w              : term -> term * hol_type
  val dest_sw2sw            : term -> term * hol_type
  val dest_w2n              : term -> term
  val dest_saturate_n2w     : term -> term * hol_type
  val dest_saturate_w2w     : term -> term * hol_type
  val dest_saturate_add     : term -> term * term
  val dest_saturate_sub     : term -> term * term
  val dest_saturate_mul     : term -> term * term

  val is_index            : term -> bool
  val is_dimindex         : term -> bool
  val is_dimword          : term -> bool
  val is_word_T           : term -> bool
  val is_word_L           : term -> bool
  val is_word_H           : term -> bool
  val is_word_L2          : term -> bool
  val is_uint_max         : term -> bool
  val is_int_min          : term -> bool
  val is_int_max          : term -> bool
  val is_word_modify      : term -> bool
  val is_word_reverse     : term -> bool
  val is_word_compare     : term -> bool
  val is_nzcv             : term -> bool
  val is_word_lt          : term -> bool
  val is_word_le          : term -> bool
  val is_word_gt          : term -> bool
  val is_word_ge          : term -> bool
  val is_word_add         : term -> bool
  val is_word_sub         : term -> bool
  val is_word_mul         : term -> bool
  val is_word_rrx         : term -> bool
  val is_word_concat      : term -> bool
  val is_word_div         : term -> bool
  val is_word_sdiv        : term -> bool
  val is_word_mod         : term -> bool
  val is_word_srem        : term -> bool
  val is_word_smod        : term -> bool
  val is_word_log2        : term -> bool
  val is_word_msb         : term -> bool
  val is_word_lsb         : term -> bool
  val is_word_slice       : term -> bool
  val is_word_bits        : term -> bool
  val is_word_bit         : term -> bool
  val is_word_extract     : term -> bool
  val is_word_lsl         : term -> bool
  val is_word_lsr         : term -> bool
  val is_word_asr         : term -> bool
  val is_word_ror         : term -> bool
  val is_word_rol         : term -> bool
  val is_word_lsl_bv      : term -> bool
  val is_word_lsr_bv      : term -> bool
  val is_word_asr_bv      : term -> bool
  val is_word_ror_bv      : term -> bool
  val is_word_rol_bv      : term -> bool
  val is_word_hi          : term -> bool
  val is_word_lo          : term -> bool
  val is_word_hs          : term -> bool
  val is_word_ls          : term -> bool
  val is_word_and         : term -> bool
  val is_word_or          : term -> bool
  val is_word_xor         : term -> bool
  val is_word_nand        : term -> bool
  val is_word_nor         : term -> bool
  val is_word_xnor        : term -> bool
  val is_word_replicate   : term -> bool
  val is_word_reduce      : term -> bool
  val is_reduce_and       : term -> bool
  val is_reduce_or        : term -> bool
  val is_reduce_xor       : term -> bool
  val is_reduce_nand      : term -> bool
  val is_reduce_nor       : term -> bool
  val is_reduce_xnor      : term -> bool
  val is_concat_word_list : term -> bool
  val is_bit_field_insert : term -> bool
  val is_word_1comp       : term -> bool
  val is_word_2comp       : term -> bool
  val is_w2w              : term -> bool
  val is_n2w              : term -> bool
  val is_w2n              : term -> bool
  val is_sw2sw            : term -> bool
  val is_saturate_n2w     : term -> bool
  val is_saturate_w2w     : term -> bool
  val is_saturate_add     : term -> bool
  val is_saturate_sub     : term -> bool
  val is_saturate_mul     : term -> bool

  val dest_mod_word_literal : term -> Arbnum.num * Arbnum.num
  val dest_word_literal     : term -> Arbnum.num
  val is_word_literal       : term -> bool
  val uint_of_word          : term -> int

end
