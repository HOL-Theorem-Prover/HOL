(* ========================================================================= *)
(* FILE          : mleEntail.sml                                             *)
(* DESCRIPTION   : Estimating the truth of propositional formulas            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleEntail :> mleEntail =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork mleLib

val ERR = mk_HOL_ERR "mleEntail"
val entail_dir = HOLDIR ^ "/examples/TNN_tasks/data_entail"

(* -------------------------------------------------------------------------
   Parse examples from string
   ------------------------------------------------------------------------- *)

fun parse_ex s =
  let
    fun is_comma c = c = #","
    val (s1,s2,s3) = triple_of_list (first_n 3 (String.tokens is_comma s))
    fun translate_token c = case c of
        #">" => " ==> "
      | #"|" => " \\/ "
      | #"&" => " /\\ "
      | #"~" => "~ "
      | #"(" => "("
      | #")" => ")"
      | _ => if Char.isLower c
             then ("(V" ^ Char.toString c ^ ":bool)")
             else raise ERR "translate_token" ""
    fun dm_to_hol s =
       let val s' = String.translate translate_token s in
         (Parse.Term [HOLPP.QUOTE s'] handle HOL_ERR _ => raise ERR "read_ex" s')
       end
  in
    (mk_imp (dm_to_hol s1, dm_to_hol s2), [Real.fromInt (string_to_int s3)])
  end;


fun read_true_exl file =
  let
    val exl1 = map parse_ex (readl file)
    val exl2 = map fst (filter (fn (_,x) => hd x > 0.5) exl1)
  in
    map rename_allvar exl2
  end

fun read_false_exl file =
  let
    val exl1 = map parse_ex (readl file)
    val exl2 = map fst (filter (fn (_,x) => hd x < 0.5) exl1)
  in
    map rename_allvar exl2
  end

(* -------------------------------------------------------------------------
   Normalize examples
   ------------------------------------------------------------------------- *)

val prime_tag = mk_var ("prime_tag", ``:bool -> bool``)
fun prime_term n tm =
   if n <= 0 then tm else mk_comb (prime_tag, prime_term (n - 1) tm)
fun mk_boolvar i = mk_var ("V" ^ its i,bool)

fun prime_boolvar_sub m =
  List.tabulate
    (m, fn n => {redex = mk_boolvar n, residue = prime_term n ``x:bool``})


fun exprimed_from_file maxvar basename =
  let
    val ex1 = map parse_ex (readl (entail_dir ^ "/" ^ basename))
    val ex2 = map_fst rename_allvar ex1
  in
    map_fst (subst (prime_boolvar_sub maxvar)) ex2
  end

(* -------------------------------------------------------------------------
   Tree neural network
   ------------------------------------------------------------------------- *)

fun entail_random_tnn dim =
  let
    val operl =
      [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),
       (``$= :bool -> bool -> bool``,2)] @
      [(``x:bool``,0),(prime_tag,1)]
    val tnn_param =
      {dimin = dim, dimout = 1,
       nlayer_headnn = 2, nlayer_oper = 2,
       operl = operl}
  in
    random_tnn tnn_param
  end

(* -------------------------------------------------------------------------
   Train
   ------------------------------------------------------------------------- *)

fun train_fixed () =
  let
    val trainex = exprimed_from_file 10 "train.txt"
    val schedule =
      [{batch_size = 16, learning_rate = 0.02,
       ncore = 4, nepoch = 100, verbose = true}]
    val randtnn = entail_random_tnn 12
    val tnn = train_tnn schedule randtnn (trainex,first_n 100 trainex)
  in
    write_tnn (entail_dir ^ "/tnn") tnn;
    tnn
  end

(* ------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun test_fixed tnn =
  let
    val filel =
      ["validate.txt","test_easy.txt","test_hard.txt",
       "test_big.txt","test_massive.txt","test_exam.txt"]
    val exl = map (exprimed_from_file 26) filel
  in
    map (tnn_accuracy tnn) exl
  end

(*
load "aiLib"; open aiLib;
load "mleEntail"; open mleEntail;
val tnn = train_fixed ();
val l = test_fixed tnn;
*)


end (* struct *)
