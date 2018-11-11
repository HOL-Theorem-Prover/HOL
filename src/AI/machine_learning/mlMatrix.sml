(* ========================================================================== *)
(* FILE          : mlMatrix.sml                                               *)
(* DESCRIPTION   : Matrix operations.                                         *)
(*                 Matrix are represented as lists of lines                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure mlMatrix :> mlMatrix =
struct
 
open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "mlMatrix"

(*----------------------------------------------------------------------------
 * Vectors
 *----------------------------------------------------------------------------*)

fun sum_rvect v = Vector.foldl (op +) 0.0 v

fun average_rvect v = sum_rvect v / Real.fromInt (Vector.length v)

fun diff_rvect v1 v2 =
  let fun f i = (Vector.sub (v1,i): real) - Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end
  
fun mult_rvect v1 v2 =
  let fun f i = (Vector.sub (v1,i): real) * Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end

fun scalar_product v1 v2 = sum_rvect (mult_rvect v1 v2)

fun scalar_mult (k:real) v = Vector.map (fn x => (k:real) * x) v

(*----------------------------------------------------------------------------
 * Matrix
 *----------------------------------------------------------------------------*)

fun mat_mult m inv =
  let fun f line = scalar_product line inv in
    Vector.map f m
  end

fun mat_map f m = Vector.map (Vector.map f) m 

fun mat_tabulate f (linen,coln) =
  let fun mk_line i = Vector.tabulate (coln, f i) in
    Vector.tabulate (linen, mk_line)
  end

fun mat_smult (k:real) m = mat_map (fn x => k * x) m

fun mat_dim m = (Vector.length m, Vector.length (Vector.sub (m,0)))

fun mat_sub m i j = Vector.sub (Vector.sub (m,i), j)

fun mat_add m1 m2 = 
  let fun f i j = (mat_sub m1 i j : real) + mat_sub m2 i j in
    mat_tabulate f (mat_dim m1)
  end
  
fun inv_dim (a,b) = (b,a)

fun mat_transpose m1 =
  let fun f i j = mat_sub m1 j i in
    mat_tabulate f (inv_dim (mat_dim m1))
  end

fun mat_random dim =
  let fun f i j = 2.0 * random_real () - 1.0 in
    mat_tabulate f dim
  end

fun string_of_vect v = 
  String.concatWith " " (map (Real.toString o approx 2) (vector_to_list v))

fun string_of_mat m =
  String.concatWith "\n" (map string_of_vect (vector_to_list m))


end (* struct *)
