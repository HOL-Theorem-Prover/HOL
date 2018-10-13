(* ========================================================================== *)
(* FILE          : tttSynt.sml                                                *)
(* DESCRIPTION   : Synthesis of terms for conjecturing lemmas                 *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttSynt :> tttSynt =
struct

open HolKernel boolLib Abbrev tttTools

val ERR = mk_HOL_ERR "tttSynt"
val dbg = dbg_file "tttSynt"

(* --------------------------------------------------------------------------
   "Random" first-order terms of a certain size.
   -------------------------------------------------------------------------- 
*)

fun number_partition m n = 
  if m > n then raise ERR "partition" "" else
  if m = 1 then [[n]] else
  let 
    fun f x l = x :: l
    val sizel = List.tabulate (n-m+1, fn x => x+1)
    fun g size = map (f size) (number_partition (m-1) (n-size))
  in
    List.concat (map g sizel)
  end

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
  let val tycdict = dregroup Type.compare (map (fn x => (type_of x, x)) cset) in
    map (random_term tycdict) (List.tabulate (n,fn _ => (size,ty))) 
  end


fun n_random_formula n cset size =
  let val tycdict = dregroup Type.compare (map (fn x => (type_of x, x)) cset) in
    map (random_term tycdict) (List.tabulate (n,fn _ => (size,bool))) 
  end

fun success_tac tac g = null (fst (tac g))

fun uniform_provable tac n cset size =
  let
    val cjl0 = 
      mapfilter (n_random_formula (n * 10) cset) (List.tabulate (size + 1,I))
    val cjl1 = map (mk_fast_set Term.compare) cjl0    
    fun is_proved cj = success_tac tac ([], cj)
    val cjpl0 = map (filter is_proved) cjl1
    val cjpl1 = map (first_n n o shuffle) cjpl0
  in 
    List.concat cjpl1
  end

fun uniform_term n cset (size,ty) =
  let
    val cjl0 = mapfilter (n_random_term (n * 10) cset) 
      (List.tabulate (size + 1,fn x => (x,ty)))
    val cjl1 = map (first_n n o shuffle o mk_fast_set Term.compare) cjl0    
  in 
    List.concat cjl1
  end





end (* struct *)
