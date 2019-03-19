(* ========================================================================= *)
(* FILE          : mlMatrix.sml                                              *)
(* DESCRIPTION   : Matrix operations.                                        *)
(*                 Matrix are represented as lists of lines                  *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlMatrix :> mlMatrix =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "mlMatrix"

type vect = real vector
type mat = real vector vector

(*---------------------------------------------------------------------------
 * Vectors
 *---------------------------------------------------------------------------*)

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

(*---------------------------------------------------------------------------
 * Matrix
 *---------------------------------------------------------------------------*)

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

fun matl_add ml = case ml of
    [] => raise ERR "mat_addl" ""
  | [m] => m 
  | m :: contl => mat_add m (matl_add contl)

fun inv_dim (a,b) = (b,a)

fun mat_transpose m1 =
  let fun f i j = mat_sub m1 j i in
    mat_tabulate f (inv_dim (mat_dim m1))
  end

fun mat_random (dim as (a,b)) =
  let 
    val r = Math.sqrt (6.0 / (Real.fromInt (a + b)))  
    fun f i j = r * (2.0 * random_real () - 1.0) 
  in
    mat_tabulate f dim
  end



fun string_of_vect v =
  String.concatWith " " (map Real.toString (vector_to_list v))

fun string_of_mat m =
  String.concatWith "\n" (map string_of_vect (vector_to_list m))

fun read_mat_sl sl =
  let 
    val l2 = map (String.tokens Char.isSpace) sl
    val l3 = map (map (valOf o Real.fromString)) l2
  in
    Vector.fromList (map Vector.fromList l3)
  end

fun read_mat file = read_mat_sl (readl file)


fun is_comma c = c = #","

fun read_diml s =
  let 
    val l1 = String.tokens Char.isSpace s
    val l2 = map (map string_to_int o String.tokens is_comma) l1
  in
    map pair_of_list l2
  end


(* 
load "mlMatrix"; load "aiLib"; open mlMatrix aiLib; 
val dir = HOLDIR ^ "/src/AI";
val m1 = mat_random (9,2);
val file = dir ^ "/test";
writel file [string_of_mat m1];
val m2 = read_mat file;

load "mlMatrix"; load "aiLib"; open mlMatrix aiLib; 

val l1 = List.tabulate (10000,fn _ => random_real ());
val l2 = List.tabulate (10000,fn _ => random_real ());
val v1 = Vector.fromList l1;
val v2 = Vector.fromList l2;

fun f0 l1 (l2 : real list) =  map (op +) (combine (l1,l2));
val (_,t1) = add_time (f0 l1) l2;
fun f1 v1 (v2 : real vector) = 
  Vector.tabulate 
    (Vector.length v1, fn i => Vector.sub (v1,i) + Vector.sub (v2,i))
;
val (_,t2) = add_time (f1 v1) v2;

val m1 = mat_random (100,100);
val m2 = mat_random (100,100);

val (m,t3) = add_time (mat_add m1) m2;


val a1 = Array.fromList l1;
val a2 = Array.fromList l2;

fun f2 a1 (a2 : real array) = 
  Array.tabulate 
    (Array.length a1, fn i => Array.sub (a1,i) + Array.sub (a2,i))

val (_,t4) = add_time (f2 a1) a2;


*)




end (* struct *)
