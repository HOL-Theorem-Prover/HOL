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

(* -------------------------------------------------------------------------
   Vectors
   ------------------------------------------------------------------------- *)

fun sum_rvect v = Vector.foldl (op +) 0.0 v

fun average_rvect v = sum_rvect v / Real.fromInt (Vector.length v)

fun diff_rvect v1 v2 =
  let fun f i = Vector.sub (v1,i) - Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end

fun vect_add v1 v2 =
  let fun f i = Vector.sub (v1,i) + Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end


fun mult_rvect v1 v2 =
  let fun f i = Vector.sub (v1,i) * Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end

fun sp_vecl l1 l2 = case (l1,l2) of
    (a1 :: m1, a2 :: m2) => a1 * a2 + sp_vecl m1 m2
  | _ => 0.0

fun scalar_product v1 v2 =
  let
    val sum = ref 0.0
    fun f (i,x) = (sum := !sum + x * Vector.sub (v2,i))
  in
    Vector.appi f v1;
    !sum
  end

fun scalar_mult k v = Vector.map (fn x => k * x) v

fun add_vectl vl =
  let fun f i = sum_real (map (fn x => Vector.sub (x,i)) vl) in
    Vector.tabulate (Vector.length (hd vl), f)
  end

(* -------------------------------------------------------------------------
   Matrix
   ------------------------------------------------------------------------- *)

fun mat_mult m inv =
  let fun f line = scalar_product line inv in Vector.map f m end

fun mat_map f m = Vector.map (Vector.map f) m
fun mat_app f m = Vector.app (Vector.app f) m

fun mat_tabulate f (linen,coln) =
  let fun mk_line i = Vector.tabulate (coln, f i) in
    Vector.tabulate (linen, mk_line)
  end

fun mat_smult (k:real) m = mat_map (fn x => k * x) m

fun mat_dim m = (Vector.length m, Vector.length (Vector.sub (m,0)))

fun mat_sub m i j = Vector.sub (Vector.sub (m,i), j)

fun mat_update m ((i,j),k) =
  let val newv = Vector.update (Vector.sub(m,i),j,k) in
    Vector.update (m,i,newv)
  end

fun mat_add m1 m2 =
  let fun f i j = mat_sub m1 i j + mat_sub m2 i j in
    mat_tabulate f (mat_dim m1)
  end

fun matl_add ml = case ml of
    [] => raise ERR "mat_addl" ""
  | [m] => m
  | m :: contl => mat_add m (matl_add contl)


fun mat_appije f m =
  let
    fun felem i (j,elem) = f i j elem
    fun fline (i,line) = Vector.appi (felem i) line
  in
    Vector.appi fline m
  end


fun mat_appij f m =
  let
    fun felem i (j,elem) = f i j
    fun fline (i,line) = Vector.appi (felem i) line
  in
    Vector.appi fline m
  end

fun mat_add_mem mem m =
  let fun f i j =
    let val r = mat_sub mem i j in r := !r + mat_sub m i j end
  in
    mat_appij f mem
  end

fun matl_add_mem mem ml = case ml of
    [] => ()
  | m :: cont => (mat_add_mem mem m; matl_add_mem mem cont)

fun add_colrow mv i j =
  let
    val sum = ref 0.0
    fun g m = sum := !sum + (mat_sub m i j)
  in
    Vector.app g mv; !sum
  end

fun matv_add mv =
  mat_tabulate (add_colrow mv) (mat_dim (Vector.sub (mv,0)))

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

(* -------------------------------------------------------------------------
   Input/output
   ------------------------------------------------------------------------- *)

fun string_of_vect v =
  String.concatWith " " (map Real.toString (vector_to_list v))
fun string_of_mat m =
  String.concatWith "\n" (map string_of_vect (vector_to_list m))

local open HOLsexp in
fun enc_vect v = list_encode enc_real (vector_to_list v)
fun dec_vect t = Option.map Vector.fromList (list_decode dec_real t)
fun enc_mat m = list_encode enc_vect (vector_to_list m)
fun dec_mat t = Option.map Vector.fromList (list_decode dec_vect t)
end


end (* struct *)
