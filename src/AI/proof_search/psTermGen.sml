(* ========================================================================= *)
(* FILE          : psTermGen.sml                                             *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure psTermGen :> psTermGen =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "psTermGen"

fun product_int nl = case nl of
    [] => 1
  | a :: m => a * product_int m

fun im_ty oper = snd (strip_type (type_of oper))

(* -------------------------------------------------------------------------
   Number of terms of each type and size.
   ------------------------------------------------------------------------- *)

(* consumes little memory but should be made local at some point *)
val nterm_cache = ref (dempty (cpl_compare Int.compare Type.compare));

(* easily overflow *)
fun nterm operl (size,ty) =
  if size <= 0 then 0 else
  dfind (size,ty) (!nterm_cache) handle NotFound => 
  let val n = sum_int (map (nterm_oper operl (size,ty)) operl) in
    nterm_cache := dadd (size,ty) n (!nterm_cache); n
  end

and nterm_oper operl (size,ty) oper =
  let val (tyargl,im) = strip_type (type_of oper) in
    if ty <> im orelse size <= 0 then 0 else 
    if null tyargl andalso size <> 1 then 0 else
    if null tyargl andalso size = 1 then 1 else
    let 
      val nll = number_partition (length tyargl) (size - 1)
                handle HOL_ERR _ => []
      fun f nl = product_int (map (nterm operl) (combine (nl,tyargl)))
    in
      sum_int (map f nll)
    end
  end

(* -------------------------------------------------------------------------
   Random terms. Generate with respect to uniform probability over
   all possible terms of certain size and type.
   ------------------------------------------------------------------------- *)

fun random_term operl (size,ty) =
  if nterm operl (size,ty) <= 0 then raise ERR "random_term" "" else
  let 
    val freql1 = map_assoc (nterm_oper operl (size,ty)) operl 
    val freql2 = filter (fn x => snd x > 0) freql1
    val freql3 = map_snd Real.fromInt freql2
  in
    if null freql3 then raise ERR "random_term" "" else
    random_term_oper operl (size,ty) (select_in_distrib freql3)
  end

and random_term_oper operl (size,ty) oper =
  let val (tyargl,im) = strip_type (type_of oper) in
    if nterm_oper operl (size,ty) oper <= 0 
      then raise ERR "random_term_oper" "" else
    if null tyargl then oper else
    let 
      val nll = number_partition (length tyargl) (size - 1)
                handle HOL_ERR _ => raise ERR "random_term_oper" ""
      fun f nl = 
        (product_int (map (nterm operl) (combine (nl,tyargl))))
      val freql1 = map_assoc f nll
      val freql2 = filter (fn x => snd x > 0) freql1
      val freql3 = map_snd Real.fromInt freql2
      val nl_chosen = select_in_distrib freql3
      val argl = map (random_term operl) (combine (nl_chosen,tyargl))
    in
      list_mk_comb (oper,argl)
    end
  end

fun random_term_upto operl (size,ty) =
  let  
    val il = List.tabulate (size, fn n => n + 1) 
    val freql1 = map_assoc (fn i => nterm operl (i,ty)) il
    val freql2 = filter (fn x => snd x > 0) freql1
    val freql3 = map_snd Real.fromInt freql2
    val i = select_in_distrib freql3
  in
    random_term operl (i,ty)
  end


fun random_term_uni operl (l,ty) =
  random_term operl (random_elem l,ty)

(* 
load "psTermGen"; open psTermGen;
val operl = [``0``,``$+``,``SUC``];
val ty = ``:num``;
val size = 6;
val tm = random_term operl (size,ty);
*)

(* -------------------------------------------------------------------------
   All terms up to a fixed size
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

fun gen_term_size size (ty,cset) =
  let
    val tycset = map (fn x => (type_of x, x)) cset
    val d = dregroup Type.compare tycset
    val cache = ref (dnew Int.compare [(1,d)])
    fun g n = dfind ty (gen_size cache n) handle NotFound => []
  in
    List.concat (List.tabulate (size, g))
  end

end (* struct *)
