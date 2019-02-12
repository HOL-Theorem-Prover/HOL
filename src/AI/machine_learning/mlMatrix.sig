signature mlMatrix =
sig

  (* vector *)
  val vector_to_list : real vector -> real list
  val sum_rvect      : real vector -> real
  val average_rvect  : real vector -> real
  val diff_rvect     : real vector -> real vector -> real vector
  val mult_rvect     : real vector -> real vector -> real vector
  val scalar_product : real vector -> real vector -> real
  val scalar_mult    : real -> real vector -> real vector
  (* matrix *)
  val mat_mult     : real vector vector -> real vector -> real vector
  val mat_smult    : real -> real vector vector -> real vector vector
  val mat_map      : ('a -> 'b) -> 'a vector vector -> 'b vector vector
  val mat_tabulate : (int -> int -> 'a) -> int * int -> 'a vector vector
  val mat_dim      : 'a vector vector -> int * int
  val mat_sub      : 'a vector vector -> int -> int -> 'a
  val mat_add      :
    real vector vector -> real vector vector -> real vector vector
  val mat_transpose : 'a vector vector -> 'a vector vector
  val mat_random    : int * int -> real vector vector
  (* output *)
  val string_of_vect : real vector -> string
  val string_of_mat : real vector vector -> string

end
