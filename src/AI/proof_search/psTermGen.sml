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

(* -------------------------------------------------------------------------
   Random terms for a fixed size (top-down).
   ------------------------------------------------------------------------- *)

fun random_term tycdict (size,ty) =
  if size <= 0 then raise ERR "random_term" "<= 0" else
  if size = 1 then hd (shuffle (dfind ty tycdict)) else
  let
    fun f x =
      let val (tyargl,im) = strip_type x in
        im = ty andalso length tyargl <= size - 1 andalso length tyargl > 0
      end
    val tyl  = filter f (dkeys tycdict)
    val tml  = List.concat (map (fn x => dfind x tycdict) tyl)
    val oper =
      if null tml then raise ERR "random_term" "" else hd (shuffle tml)
    val (tyargl,_) = strip_type (type_of oper)
    val sizel = hd (shuffle (number_partition (length tyargl) (size - 1)))
    val argl = map (random_term tycdict) (combine (sizel,tyargl))
  in
    list_mk_comb (oper,argl)
  end

fun n_random_term n cset (size,ty) =
  let val tycdict = dregroup Type.compare (map (fn x => (type_of x, x)) cset)
  in
    map (random_term tycdict) (List.tabulate (n,fn _ => (size,ty)))
  end

fun uniform_term n cset (size,ty) =
  let
    val cjl0 = mapfilter (n_random_term (n * 10) cset)
      (List.tabulate (size + 1,fn x => (x,ty)))
    val cjl1 = map (first_n n o shuffle o mk_fast_set Term.compare) cjl0
  in
    List.concat cjl1
  end

(* -------------------------------------------------------------------------
   Random terms of a fixed size (bottom-up)
   ------------------------------------------------------------------------- *)

fun is_applicable (ty1,ty2) =
  let fun apply ty1 ty2 =
    mk_comb (mk_var ("x",ty1), mk_var ("y",ty2))
  in
    can (apply ty1) ty2
  end

fun all_mk_comb d1 d2 (ty1,ty2) =
  let
    val tml1 = dfind ty1 d1
    val tml2 = dfind ty2 d2
    val l = cartesian_product tml1 tml2
  in
    map mk_comb l
  end

fun synthetize filterf (maxgen,maxdepth) (targettype,cset) =
  let
    val tycset = map (fn x => (type_of x, x)) cset
    val d1 = dregroup Type.compare tycset
    val gen_size_cache = ref (dnew Int.compare [(1,d1)])
    fun gen_size n =
      (if n <= 0 then raise ERR "gen_size" "" else dfind n (!gen_size_cache))
      handle NotFound =>
      let
        val l = map pair_of_list (number_partition 2 n)
        fun all_comb (n1,n2) =
          let
            val d1     = gen_size n1
            val d2     = gen_size n2
            val tytyl  = cartesian_product (dkeys d1) (dkeys d2)
            val tytyl' = filter is_applicable tytyl
          in
            List.concat (map (all_mk_comb d1 d2) tytyl')
          end
        val combl = List.concat (map all_comb l)
        val tml1  = filterf combl
        val tml2  = map (fn x => (type_of x, x)) tml1
        val r     = dregroup Type.compare tml2
      in
        gen_size_cache := dadd n r (!gen_size_cache);
        r
      end
    fun filter_with_targettype acc n depth =
      if length acc >= maxgen orelse depth > maxdepth
        then first_n maxgen acc else
      let
        val tml    = dfind targettype (gen_size depth) handle NotFound => []
        val newacc = acc @ tml
      in
        filter_with_targettype newacc n (depth + 1)
      end
  in
    filter_with_targettype [] maxgen 1
  end


(* -------------------------------------------------------------------------
   Function for building cuts for the Cutter theorem prover.
   ------------------------------------------------------------------------- *)

(*
fun is_metaground x =
 not (can (find_term (fn x => x = ``meta_var : num``)) x)

fun build_fo_cut subl metatm =
  let
    val n = length (find_terms (fn x => x = ``meta_var : num``) metatm)
    fun f sub i = subst_occs [[i+1]] sub metatm
    val absl = map (fn x => List.tabulate (n,f x)) subl
  in
    mk_fast_set Term.compare (List.concat absl)
  end

val tml = find_terms (fn x => type_of x = ``:num``) tm

fun build_fo_cut subl metatm =
  let
    fun f sub i = subst active_var
    val absl = map (fn x => List.tabulate (n,f x)) subl
  in
    mk_fast_set Term.compare (List.concat absl)
  end


fun build_term (subfl,n) (tm : term) = (List.nth (subfl,n) tm : term);

*)






end (* struct *)

(* test
load "psTermGen"; open psTermGen tttTools;

(* can derive the filter function from the nn scoring function *)

val maxsize = 20;

(* signature *)
val active_var = ``active_var : num``;
val pending_var = ``pending_var : num``;
val starttm = mk_eq (active_var,pending_var);
fun mk_suc x = mk_comb (``SUC``,x);
fun mk_add (a,b) = list_mk_comb (``$+``,[a,b]);
val zero = ``0``;

val sub1 = [{redex = active_var, residue = mk_suc active_var}];
val sub2 = [{redex = active_var, residue = mk_add (active_var,pending_var)}];
val sub3 = [{redex = active_var, residue = zero},
            {redex = pending_var, residue = active_var}];

val subl = [sub1,sub2,sub3];
val subfl = [subst_occs [[1]] sub1,
 subst_occs [[1]] sub2,
 subst_occs [[1],[1]] sub3];

val curtm = starttm;

val curtm' = ;
val curtm = curtm';

fun loop tm =
  if can (find_term (fn x => x = active_var)) tm then
    let
      val tm' = (hd (shuffle subfl)) tm
      val _ = print_endline (term_to_string tm')
    in
      loop tm'
    end
  else tm

val subl = [sub1,sub2,sub3];

val metatml1 = build_fo_cut subl metatm;
val metatml2 =
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml1));
val metatml3 =
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml2));
val metatml4 =
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml3));
val metatml5 =
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml4));
val metatml6 =
  mk_fast_set Term.compare (List.concat (map (build_fo_cut subl) metatml5));

*)



