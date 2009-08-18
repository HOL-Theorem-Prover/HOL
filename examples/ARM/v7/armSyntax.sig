signature armSyntax =
sig

  include Abbrev

  val dest_monad_type : hol_type -> hol_type

  val valuestate_tm                 : term
  val error_tm                      : term
  val constT_tm                     : term
  val seqT_tm                       : term
  val parT_tm                       : term
  val forT_tm                       : term
  val readT_tm                      : term
  val writeT_tm                     : term
  val read__reg_tm                  : term
  val write__reg_tm                 : term
  val read__psr_tm                  : term
  val write__psr_tm                 : term
  val read_reg_mode_tm              : term
  val write_reg_mode_tm             : term
  val read_reg_tm                   : term
  val write_reg_tm                  : term
  val read_cpsr_tm                  : term
  val write_cpsr_tm                 : term
  val read_spsr_tm                  : term
  val write_spsr_tm                 : term
  val read_memA_tm                  : term
  val write_memA_tm                 : term
  val decode_psr_tm                 : term
  val bytes_tm                      : term
  val align_tm                      : term
  val aligned_tm                    : term
  val bit_count_tm                  : term
  val ITAdvance_tm                  : term
  val Encoding_ARM_tm               : term
  val Encoding_Thumb_tm             : term
  val Encoding_Thumb2_tm            : term
  val clear_event_register_tm       : term
  val send_event_tm                 : term
  val wait_for_interrupt_tm         : term
  val clear_wait_for_interrupt_tm   : term
  val arm_decode_tm                 : term
  val thumb_decode_tm               : term
  val thumb2_decode_tm              : term

  val mk_valuestate                 : term * term -> term
  val mk_error                      : term -> term
  val mk_constT                     : term -> term
  val mk_seqT                       : term * term -> term
  val mk_parT                       : term * term -> term
  val mk_forT                       : term * term * term -> term
  val mk_readT                      : term -> term
  val mk_writeT                     : term -> term
  val mk_read__reg                  : term * term -> term
  val mk_write__reg                 : term * term * term -> term
  val mk_read__psr                  : term * term -> term
  val mk_write__psr                 : term * term * term -> term
  val mk_read_reg_mode              : term * term * term -> term
  val mk_write_reg_mode             : term * term * term * term -> term
  val mk_read_reg                   : term * term -> term
  val mk_write_reg                  : term * term * term -> term
  val mk_read_cpsr                  : term -> term
  val mk_write_cpsr                 : term * term -> term
  val mk_read_spsr                  : term -> term
  val mk_write_spsr                 : term * term -> term
  val mk_read_memA                  : term * term * term -> term
  val mk_write_memA                 : term * term * term * term -> term
  val mk_decode_psr                 : term -> term
  val mk_bytes                      : term * term -> term
  val mk_align                      : term * term -> term
  val mk_aligned                    : term * term -> term
  val mk_bit_count                  : term -> term
  val mk_ITAdvance                  : term -> term
  val mk_clear_event_register       : term -> term
  val mk_send_event                 : term -> term
  val mk_wait_for_interrupt         : term -> term
  val mk_clear_wait_for_interrupt   : term -> term
  val mk_read_memA_1                : term * term -> term
  val mk_write_memA_1               : term * term * term -> term
  val mk_read_memA_2                : term * term -> term
  val mk_write_memA_2               : term * term * term -> term
  val mk_read_memA_4                : term * term -> term
  val mk_write_memA_4               : term * term * term -> term
  val mk_arm_decode                 : term * term -> term
  val mk_thumb_decode               : term * term * term -> term
  val mk_thumb2_decode              : term * term * term -> term

  val dest_valuestate               : term -> term * term
  val dest_error                    : term -> term
  val dest_constT                   : term -> term
  val dest_seqT                     : term -> term * term
  val dest_parT                     : term -> term * term
  val dest_forT                     : term -> term * term * term
  val dest_readT                    : term -> term
  val dest_writeT                   : term -> term
  val dest_read__reg                : term -> term * term
  val dest_write__reg               : term -> term * term * term
  val dest_read__psr                : term -> term * term
  val dest_write__psr               : term -> term * term * term
  val dest_read_reg_mode            : term -> term * term
  val dest_write_reg_mode           : term -> term * term * term
  val dest_read_reg                 : term -> term * term
  val dest_write_reg                : term -> term * term * term
  val dest_read_cpsr                : term -> term
  val dest_write_cpsr               : term -> term * term
  val dest_read_spsr                : term -> term
  val dest_write_spsr               : term -> term * term
  val dest_read_memA                : term -> term * term
  val dest_write_memA               : term -> term * term * term
  val dest_clear_event_register     : term -> term
  val dest_send_event               : term -> term
  val dest_wait_for_interrupt       : term -> term
  val dest_clear_wait_for_interrupt : term -> term
  val dest_decode_psr               : term -> term
  val dest_bytes                    : term -> term
  val dest_align                    : term -> term
  val dest_aligned                  : term -> term
  val dest_bit_count                : term -> term
  val dest_ITAdvance                : term -> term
  val dest_arm_decode               : term -> term * term
  val dest_thumb_decode             : term -> term * term * term
  val dest_thumb2_decode            : term -> term * term

  val is_valuestate                 : term -> bool
  val is_error                      : term -> bool
  val is_constT                     : term -> bool
  val is_seqT                       : term -> bool
  val is_parT                       : term -> bool
  val is_forT                       : term -> bool
  val is_readT                      : term -> bool
  val is_writeT                     : term -> bool
  val is_read__reg                  : term -> bool
  val is_write__reg                 : term -> bool
  val is_read__psr                  : term -> bool
  val is_write__psr                 : term -> bool
  val is_read_reg_mode              : term -> bool
  val is_write_reg_mode             : term -> bool
  val is_read_reg                   : term -> bool
  val is_write_reg                  : term -> bool
  val is_read_cpsr                  : term -> bool
  val is_write_cpsr                 : term -> bool
  val is_read_spsr                  : term -> bool
  val is_write_spsr                 : term -> bool
  val is_read_memA                  : term -> bool
  val is_write_memA                 : term -> bool
  val is_clear_event_register       : term -> bool
  val is_send_event                 : term -> bool
  val is_wait_for_interrupt         : term -> bool
  val is_clear_wait_for_interrupt   : term -> bool
  val is_decode_psr                 : term -> bool
  val is_bytes                      : term -> bool
  val is_align                      : term -> bool
  val is_aligned                    : term -> bool
  val is_ITAdvance                  : term -> bool
  val is_arm_decode                 : term -> bool
  val is_thumb_decode               : term -> bool
  val is_thumb2_decode              : term -> bool

end
