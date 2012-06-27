signature bitstringSyntax =
sig

   include Abbrev

   val bitstring_ty : hol_type

   val int_to_bitlist : int -> bool list
   val bitlist_to_int : bool list -> int

   val bool_of_term : term -> bool
   val term_of_bool : bool -> term

   val bitlist_of_term : term -> bool list
   val binstring_of_term : term -> string
   val hexstring_of_term : term -> string
   val int_of_term : term -> int

   val bitstring_of_bitlist : bool list -> term
   val bitstring_of_binstring : string -> term
   val bitstring_of_hexstring : string -> term
   val bitstring_of_int : int -> term

   val bitvector_of_bitlist : bool list -> term
   val bitvector_of_binstring : string -> term
   val bitvector_of_hexstring : string -> term
   val bitvector_of_int : int -> term

   val fixedwidth_of_bitlist : bool list * int -> term
   val fixedwidth_of_binstring : string * int -> term
   val fixedwidth_of_hexstring : string * int -> term
   val fixedwidth_of_int : int * int -> term

   val padded_fixedwidth_of_int : int * int -> term

   val mk_fixedwidth : term * int -> term

   val add_tm : term
   val band_tm : term
   val bitify_tm : term
   val bitwise_tm : term
   val bnot_tm : term
   val boolify_tm : term
   val bor_tm : term
   val bxor_tm : term
   val field_insert_tm : term
   val field_tm : term
   val fixwidth_tm : term
   val modify_tm : term
   val n2v_tm : term
   val replicate_tm : term
   val s2v_tm : term
   val shiftl_tm : term
   val shiftr_tm : term
   val sign_extend_tm : term
   val testbit_tm : term
   val v2n_tm : term
   val v2s_tm : term
   val v2w_tm : term
   val w2v_tm : term
   val zero_extend_tm : term

   val dest_add : term -> term * term
   val dest_band : term -> term * term
   val dest_bitify : term -> term * term
   val dest_bitwise : term -> term * term * term
   val dest_bnot : term -> term
   val dest_boolify : term -> term * term
   val dest_bor : term -> term * term
   val dest_bxor : term -> term * term
   val dest_field : term -> term * term * term
   val dest_field_insert : term -> term * term * term * term
   val dest_fixwidth : term -> term * term
   val dest_modify : term -> term * term
   val dest_n2v : term -> term
   val dest_replicate : term -> term * term
   val dest_s2v : term -> term
   val dest_shiftl : term -> term * term
   val dest_shiftr : term -> term * term
   val dest_sign_extend : term -> term * term
   val dest_testbit : term -> term * term
   val dest_v2n : term -> term
   val dest_v2s : term -> term
   val dest_v2w : term -> term * hol_type
   val dest_w2v : term -> term
   val dest_zero_extend : term -> term * term

   val is_add : term -> bool
   val is_band : term -> bool
   val is_bitify : term -> bool
   val is_bitwise : term -> bool
   val is_bnot : term -> bool
   val is_boolify : term -> bool
   val is_bor : term -> bool
   val is_bxor : term -> bool
   val is_field : term -> bool
   val is_field_insert : term -> bool
   val is_fixwidth : term -> bool
   val is_modify : term -> bool
   val is_n2v : term -> bool
   val is_replicate : term -> bool
   val is_s2v : term -> bool
   val is_shiftl : term -> bool
   val is_shiftr : term -> bool
   val is_sign_extend : term -> bool
   val is_testbit : term -> bool
   val is_v2n : term -> bool
   val is_v2s : term -> bool
   val is_v2w : term -> bool
   val is_w2v : term -> bool
   val is_zero_extend : term -> bool

   val mk_add : term * term -> term
   val mk_band : term * term -> term
   val mk_bitify : term * term -> term
   val mk_bitwise : term * term * term -> term
   val mk_bnot : term -> term
   val mk_boolify : term * term -> term
   val mk_bor : term * term -> term
   val mk_bxor : term * term -> term
   val mk_field : term * term * term -> term
   val mk_field_insert : term * term * term * term -> term
   val mk_fixwidth : term * term -> term
   val mk_modify : term * term -> term
   val mk_n2v : term -> term
   val mk_replicate : term * term -> term
   val mk_s2v : term -> term
   val mk_shiftl : term * term -> term
   val mk_shiftr : term * term -> term
   val mk_sign_extend : term * term -> term
   val mk_testbit : term * term -> term
   val mk_v2n : term -> term
   val mk_v2s : term -> term
   val mk_v2w : term * hol_type -> term
   val mk_w2v : term -> term
   val mk_zero_extend : term * term -> term

end
