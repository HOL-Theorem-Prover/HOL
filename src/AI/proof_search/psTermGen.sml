(* ========================================================================= *)
(* FILE          : psTermGen.sml                                             *)
(* DESCRIPTION   : Term generation algorithms                                *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure psTermGen :> psTermGen =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "psTermGen"

fun int_product nl = case nl of
    [] => 1
  | a :: m => a * int_product m

fun im_ty oper = snd (strip_type (type_of oper))

(* -------------------------------------------------------------------------
   Number of terms of each type and size.
   ------------------------------------------------------------------------- *)

fun ntermc cache operl (size,ty) =
  if size <= 0 then 0 else
  dfind (size,ty) (!cache) handle NotFound =>
  let val n = sum_int (map (ntermc_oper cache operl (size,ty)) operl) in
    cache := dadd (size,ty) n (!cache); n
  end
and ntermc_oper cache operl (size,ty) oper =
  let val (tyargl,im) = strip_type (type_of oper) in
    if ty <> im orelse size <= 0 then 0 else
    if null tyargl andalso size <> 1 then 0 else (* first-order *)
    if null tyargl andalso size = 1 then 1 else
    let
      val nll = number_partition (length tyargl) (size - 1)
                handle HOL_ERR _ => []
      fun f nl = int_product (map (ntermc cache operl) (combine (nl,tyargl)))
    in
      sum_int (map f nll)
    end
  end

(* -------------------------------------------------------------------------
   Random terms. Generate with respect to uniform probability over
   all possible terms of certain size and type.
   ------------------------------------------------------------------------- *)

fun random_termc cache operl (size,ty) =
  if ntermc cache operl (size,ty) <= 0 then raise ERR "random_term" "" else
  let
    val freql1 = map_assoc (ntermc_oper cache operl (size,ty)) operl
    val freql2 = filter (fn x => snd x > 0) freql1
    val freql3 = map_snd Real.fromInt freql2
  in
    random_termc_oper cache operl (size,ty) (select_in_distrib freql3)
  end
and random_termc_oper cache operl (size,ty) oper =
  let val (tyargl,im) = strip_type (type_of oper) in
    if ntermc_oper cache operl (size,ty) oper <= 0
      then raise ERR "random_term_oper" "" else
    if null tyargl then oper else
    let
      val nll = number_partition (length tyargl) (size - 1)
                handle HOL_ERR _ => raise ERR "random_term_oper" ""
      fun f nl =
        (int_product (map (ntermc cache operl) (combine (nl,tyargl))))
      val freql1 = map_assoc f nll
      val freql2 = filter (fn x => snd x > 0) freql1
      val freql3 = map_snd Real.fromInt freql2
      val nl_chosen = select_in_distrib freql3
      val argl = map (random_termc cache operl) (combine (nl_chosen,tyargl))
    in
      list_mk_comb (oper,argl)
    end
  end

(* -------------------------------------------------------------------------
   Functions with no cache
   ------------------------------------------------------------------------- *)

fun nterm operl (size,ty) =
  let val cache = ref (dempty (cpl_compare Int.compare Type.compare)) in
    ntermc cache operl (size,ty)
  end

fun random_term operl (size,ty) =
  let val cache = ref (dempty (cpl_compare Int.compare Type.compare)) in
    random_termc cache operl (size,ty)
  end

fun random_terml operl (size,ty) n =
  let val cache = ref (dempty (cpl_compare Int.compare Type.compare)) in
    List.tabulate (n, fn _ => random_termc cache operl (size,ty))
  end

(* -------------------------------------------------------------------------
   All terms up to a fixed size with a certain type
   ------------------------------------------------------------------------- *)

fun is_applicable (ty1,ty2) =
  let fun apply ty1 ty2 = mk_comb (mk_var ("x",ty1), mk_var ("y",ty2)) in
    can (apply ty1) ty2
  end

fun all_mk_comb d1 d2 (ty1,ty2) =
  map mk_comb (cartesian_product (dfind ty1 d1) (dfind ty2 d2))

fun gen_size cache n =
  (if n <= 0 then dempty Type.compare else dfind n (!cache))
  handle NotFound =>
  let
    val l = map pair_of_list (number_partition 2 n)
    fun all_comb (n1,n2) =
      let
        val d1     = gen_size cache n1
        val d2     = gen_size cache n2
        val tytyl  = cartesian_product (dkeys d1) (dkeys d2)
        val tytyl' = filter is_applicable tytyl
      in
        List.concat (map (all_mk_comb d1 d2) tytyl')
      end
    val tml1 = List.concat (map all_comb l)
    val tml2  = map (fn x => (type_of x, x)) tml1
    val d3 = dregroup Type.compare tml2
  in
    cache := dadd n d3 (!cache); d3
  end

fun gen_term operl (size,ty) =
  let
    val tycset = map (fn x => (type_of x, x)) operl
    val d = dregroup Type.compare tycset
    val cache = ref (dnew Int.compare [(1,d)])
    fun g n = dfind ty (gen_size cache n) handle NotFound => []
  in
    List.concat (List.tabulate (size, g))
  end

end (* struct *)
