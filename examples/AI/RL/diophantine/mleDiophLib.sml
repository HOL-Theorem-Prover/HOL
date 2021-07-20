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
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Types for graphs and polynomials
   ------------------------------------------------------------------------- *)

type graph = bool list
val graph_compare = list_compare bool_compare
fun graph_to_string graph = String.concatWith " " (map bts graph)
fun string_to_graph s = map string_to_bool (String.tokens Char.isSpace s)
fun graph_to_il bl = map snd (filter fst (number_snd 0 bl))

type poly = int list list
val poly_compare = list_compare (list_compare Int.compare)
fun ilts il = String.concatWith " " (map its il)
fun stil s = map string_to_int (String.tokens Char.isSpace s)
fun poly_to_string poly = String.concatWith "," (map ilts poly)
fun string_to_poly s = map stil (String.tokens (fn c => c = #",") s)
fun poly_size poly = length (List.concat poly)

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

fun eval_exp_bare (a,b) = int_pow a b mod 16
val expv =
  (Vector.tabulate (16, fn i => Vector.tabulate
  (5, fn j => eval_exp_bare (i,j))));
fun eval_exp_vect (a,b) = Vector.sub (Vector.sub (expv,a),b);
fun eval_exp k v i n =
  eval_exp_vect (if i = 0 then k else Vector.sub (v,i-1), n)

fun eval_mono mono k v =
  hd mono * int_product (mapi (eval_exp k v) (tl mono)) mod 16
fun eval_poly poly k v =
  sum_int (map (fn x => eval_mono x k v) poly) mod 16

val car0 = map Vector.fromList
  (cartesian_productl (List.tabulate (0, fn _ => numberl)))
val car1 = map Vector.fromList
  (cartesian_productl (List.tabulate (1, fn _ => numberl)))
val car2 =  map Vector.fromList
  (cartesian_productl (List.tabulate (2, fn _ => numberl)))
val car3 = map Vector.fromList
  (cartesian_productl (List.tabulate (3, fn _ => numberl)))

fun has_solution nvar f k =
  let
    val l =
      if nvar = 0 then car0
      else if nvar = 1 then car1
      else if nvar = 2 then car2
      else if nvar = 3 then car3
      else raise ERR "has_solution" "nvar"
  in
    exists (fn v => f k v = 0) l
  end

fun dioph_set poly =
  if null poly then numberl else
  let val nvar = Int.max (list_imax (map length poly) - 2, 0) in
    filter (has_solution nvar (eval_poly poly)) numberl
  end

fun dioph_match poly graph =
  if null poly then false else
  let
    val nvar = Int.max (list_imax (map length poly) - 2, 0)
    val diophf = eval_poly poly
    fun f (b,k) = (has_solution nvar diophf k = b)
  in
    all f (number_snd 0 graph)
  end

(* -------------------------------------------------------------------------
   Generating random polynomials and compute their Diophantine sets
   ------------------------------------------------------------------------- *)

fun random_mono () =
  random_int (1,modulo-1) ::
  List.tabulate (random_int (0,maxvar), fn _ => random_int (0,maxexponent))

fun random_poly () =
  let val n = random_int (1,maxmonomial) in
    List.tabulate (n, fn _ => random_mono ())
  end

fun poly_size poly = length (List.concat poly)

fun compare_mono (l1,l2) =
  cpl_compare (list_compare Int.compare) Int.compare
    ((tl l1,hd l1),(tl l2,hd l2))

fun norm_poly poly = dict_sort compare_mono poly

fun gen_diophset n nmax d =
  if dlength d >= nmax then (d,n) else
  let
    val _ = if n mod 1000 = 0 then print_endline ("try " ^ its n) else ()
    val poly = random_poly ()
    val set = dioph_set poly
  in
    if dmem set d then
      let val oldpoly = dfind set d in
        if poly_size poly < poly_size oldpoly
        then gen_diophset (n+1) nmax (dadd set poly d)
        else gen_diophset (n+1) nmax d
      end
    else (print_endline (its ((dlength d) + 1));
          gen_diophset (n+1) nmax (dadd set poly d))
  end

(* -------------------------------------------------------------------------
   Converting polynomials to a term representation for the TNN
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

(* -------------------------------------------------------------------------
   Converting polynomials to a term representation for verification
   ------------------------------------------------------------------------- *)

fun veri_of_mono mono =
  let
    val _ = if null mono then raise ERR "term_of_mono" "" else ()
    val (coeff,expl) = (hd mono, tl mono)
    val iexpl = number_fst 0 expl
    fun f (i,n) = List.tabulate (n, fn _ =>
      if i = 0 then mk_var ("k",``:num``) else
      if i = 1 then mk_var ("x",``:num``) else
      if i = 2 then mk_var ("y",``:num``) else
      if i = 3 then mk_var ("z",``:num``) else
      raise ERR "veri_of_mono" "")
    val coefftm = numSyntax.term_of_int coeff
  in
    list_mk_mult (coefftm :: List.concat (map f iexpl))
  end

fun veri_of_poly poly =
  if null poly
  then raise ERR "veritm_of_poly" ""
  else list_mk_plus (map veri_of_mono poly)


(* -------------------------------------------------------------------------
   Export
   ------------------------------------------------------------------------- *)

fun human_of_mono mono =
  let
    val _ = if null mono then raise ERR "term_of_mono" "" else ()
    val (coeff,expl) = (hd mono, tl mono)
    val iexpl = combine (first_n (length expl) ["k","x","y","z"], expl)
    fun f (is,n) = if n = 0 then "" else is ^
      (if n = 1 then "" else "^" ^ its n)
    val coeffs =
      if not (all (fn x => x = 0) expl) andalso coeff = 1
      then "" else its coeff
  in
    String.concat (coeffs :: map f iexpl)
  end

fun human_of_poly poly = String.concatWith " + " (map human_of_mono poly)

val targetdir = selfdir ^ "/dioph_target"

fun export_data (train,test) =
  let
    val l = train @ test
    val _ = mkDir_err targetdir
    fun f1 (graph,poly) =
      let val poly' = norm_poly poly in
        "graph: " ^ ilts graph ^
        "\npoly: " ^ poly_to_string poly' ^
        "\n%poly(human): " ^ human_of_poly poly'
      end
    val il = map (poly_size o snd) l
    val statsl = dlist (count_dict (dempty Int.compare) il);
    fun f2 (i,j) = its i ^ "-" ^ its j
    val train_sorted =
      dict_sort (cpl_compare (list_compare Int.compare) poly_compare) train
    val test_sorted =
      dict_sort (cpl_compare (list_compare Int.compare) poly_compare) test
  in
    writel (targetdir ^ "/train_export") (map f1 train_sorted);
    writel (targetdir ^ "/test_export") (map f1 test_sorted);
    writel (targetdir ^ "/distrib") (map f2 statsl)
  end

fun import_data file =
  let
    val sl = readl (targetdir ^ "/" ^ file)
    val l = map triple_of_list (mk_batch 3 sl)
    fun f (a,b,_) =
      (
      stil (snd (split_string "graph: " a)),
      string_to_poly (snd (split_string "poly: " b))
      )
  in
    map f l
  end

(*
load "aiLib"; open aiLib;
load "mleDiophLib"; open mleDiophLib;
val train = import_data "train_export";
val test = import_data "test_export";
val l1 = map (poly_size o snd) (train @ test);
val l2 = dlist (count_dict (dempty Int.compare) l1);

fun real_product l =
  case l of [] => 1.0 | a :: m => (a:real) * real_product m

fun freqmono i = Real.fromInt (16 * int_pow 5 (i - 1));
fun freqpoly partl = real_product (map freqmono partl);
fun freqpoly_n n =
  let val partll =
    List.concat (List.tabulate (6, fn i => (number_partition (i+1) n
    handle HOL_ERR _ => [])))
  in
    sum_real (map freqpoly partll)
  end;

*)

end (* struct *)

