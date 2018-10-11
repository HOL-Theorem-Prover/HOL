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

fun partition m n = 
  if m > n then raise ERR "partition" "" else
  if m = 1 then [[n]] else
  let 
    fun f x l = x :: l
    val sizel = List.tabulate (n-m+1, fn x => x+1)
    fun g size = map (f size) (partition (m-1) (n-size))
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
    val sizel = hd (shuffle (partition (length tyargl) (size - 1))) 
    val argl = map (random_term tycdict) (combine (sizel,tyargl)) 
  in
    list_mk_comb (oper,argl)
  end

end (* struct *)

(* 
load "tttSynt"; open tttSynt; open tttTools;
val ax1 = ``PRE 0 = 0``;
val ax2 = ``PRE (SUC x) = x``;
val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``x * 0 = 0``;
val ax7 = ``x * (SUC y) = (x * y) + x``;
val cl = List.concat (map (find_terms is_const) [ax1,ax2,ax4,ax5,ax6,ax7]);
val cset = mk_fast_set Term.compare cl;
val tycdict = dregroup Type.compare (map (fn x => (type_of x, x)) cset);
val thm = random_term tycdict (10,bool);
val thml = map (random_term tycdict) (List.tabulate (10,fn _ => (10,bool))); 
*)









