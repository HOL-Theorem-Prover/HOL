signature mlMatrix =
sig

  type vect = real vector
  type mat = real vector vector

  (* vector *)
  val vector_to_list : 'a vector -> 'a list
  val sum_rvect      : vect -> real
  val average_rvect  : vect -> real
  val diff_rvect     : vect -> vect -> vect
  val mult_rvect     : vect -> vect -> vect
  val scalar_product : vect -> vect -> real
  val scalar_mult    : real -> vect -> vect
  val add_vectl      : vect list -> vect 
  (* matrix *)
  val mat_mult     : mat -> vect -> vect
  val mat_smult    : real -> mat -> mat
  val mat_map      : ('a -> 'b) -> 'a vector vector -> 'b vector vector
  val mat_tabulate : (int -> int -> 'a) -> int * int -> 'a vector vector
  val mat_dim      : 'a vector vector -> int * int
  val mat_sub      : 'a vector vector -> int -> int -> 'a
  val mat_update   : 'a vector vector -> (int * int) * 'a -> 'a vector vector
  val mat_add      : mat -> mat -> mat
  val matl_add     : mat list -> mat
  val mat_transpose : 'a vector vector -> 'a vector vector
  val mat_random    : int * int -> mat
  (* input/output *)
  val string_of_vect : vect -> string
  val string_of_mat : mat -> string
  val enc_vect : vect -> HOLsexp.t
  val dec_vect : HOLsexp.t -> vect option
  val enc_mat : mat -> HOLsexp.t
  val dec_mat : HOLsexp.t -> mat option

end
