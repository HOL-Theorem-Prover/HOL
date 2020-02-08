(* ========================================================================= *)
(* FILE          : mleDiophLib.sml                                           *)
(* DESCRIPTION   : Tools for term synthesis on Diophantine equations         *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleDiophLib :> mleDiophLib =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory 
numSyntax psTermGen

val ERR = mk_HOL_ERR "mleDiophLib"

type poly = int list list

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

val modulo = 16
val maxexponent = 4
val maxmonomial = 5
val maxvar = 4
val numberl = List.tabulate (modulo,I)

(* -------------------------------------------------------------------------
   Computing the Diophantine set of a formula
   ------------------------------------------------------------------------- *)

fun eval_exp (i,n) = fn l => int_pow (List.nth (l,i)) n mod 16

fun eval_mono il =
  let 
    val (coeff,expl) = (hd il, tl il) 
    val iexpl = number_fst 0 expl
    val fl = map eval_exp iexpl
  in
    fn l => coeff * int_product (map (fn f => f l) fl) mod 16 
  end

fun eval_poly poly = 
  let val fl = map eval_mono poly in
    fn l => (sum_int (map (fn f => f l) fl) mod 16)
  end

fun has_solution n f k =
  let
    val l1 = if n >= 2 
             then cartesian_productl (List.tabulate (n-2, fn _ => numberl))
             else []
    val l2 = map (fn l => k :: l) l1
  in
    exists (fn l => f l = 0) l2
  end

fun dioph_set poly = 
  if null poly then numberl else
  let val n = list_imax (map length poly) in 
    filter (has_solution n (eval_poly poly)) numberl
  end

fun dioph_match poly graph =
  if null poly then false else
  let 
    val n = list_imax (map length poly)
    val diophf = eval_poly poly
    fun f (b,i) = (has_solution n diophf i = b)
  in 
    all f (number_snd 0 graph)
  end

(* -------------------------------------------------------------------------
   Generating random polynomials and Diophantine sets
   ------------------------------------------------------------------------- *)

fun random_mono () = 
  random_int (1,modulo-1) ::
  List.tabulate (random_int (0,maxvar), fn _ => random_int (0,maxexponent))

fun random_poly () =
  let val n = random_int (1,maxmonomial) in
    List.tabulate (n, fn _ => random_mono ())
  end

fun poly_size poly = length (List.concat poly)

fun gen_diophset n d =
  if dlength d >= n then d else
  let 
    val poly = random_poly () 
    val set = dioph_set poly
  in
    if dmem set d then 
      let val oldpoly = dfind set d in
        if poly_size poly < poly_size oldpoly 
        then (print "*"; gen_diophset n (dadd set poly d))
        else (print "."; gen_diophset n d)
      end
    else (print_endline (its ((dlength d) + 1)); 
          gen_diophset n (dadd set poly d))
  end

(* -------------------------------------------------------------------------
   Converting polynomials to a term representation
   ------------------------------------------------------------------------- *)

fun term_of_mono mono = 
  let 
    val _ = if null mono then raise ERR "term_of_mono" "" else ()
    val (coeff,expl) = (hd mono, tl mono)
    val iexpl = number_fst 0 expl
    fun f (i,n) = mk_var ("v" ^ its i ^ "p" ^ its n, ``:num``)
    val coefftm = mk_var ("n" ^ its coeff, ``:num``)
  in
    list_mk_mult (coefftm :: map f iexpl)
  end

fun term_of_poly poly = 
  if null poly 
  then mk_var ("start",``:num``)
  else list_mk_plus (map term_of_mono poly)

(*
load "aiLib"; open aiLib;
load "mleDiophLib"; open mleDiophLib;
val d = gen_diophset 100 (dempty (list_compare Int.compare));
val l = map_snd term_of_poly (dlist d);
*)




end (* struct *)

