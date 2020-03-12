(* ========================================================================= *)
(* FILE          : mleEntail.sml                                             *)
(* DESCRIPTION   : Estimating the truth of propositional formulas            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleEntail :> mleEntail =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleEntail"
val entaildir = HOLDIR ^ "/examples/AI_TNN/data_entail"

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
         (Parse.Term [HOLPP.QUOTE s'] 
          handle HOL_ERR _ => raise ERR "read_ex" s')
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
   Vocabulary
   ------------------------------------------------------------------------- *)

val prime_tag = mk_var ("prime_tag", ``:bool -> bool``)
fun prime_term n tm =
   if n <= 0 then tm else mk_comb (prime_tag, prime_term (n - 1) tm)
fun mk_boolvar i = mk_var ("V" ^ its i,bool)
fun prime_boolvar_sub m =
  List.tabulate
    (m, fn n => {redex = mk_boolvar n, residue = prime_term n ``x:bool``})
val operl = [prime_tag,``x:bool``,``$/\``,``$\/``,``$~``,``$==>``]
val head_entail = mk_var ("head_entail",``:bool -> bool``)
fun mk_head x = mk_comb (head_entail, x)

(* -------------------------------------------------------------------------
   Import and normalize examples
   ------------------------------------------------------------------------- *)

fun import_entaildata maxvar basename =
  let
    val ex1 = map parse_ex (readl (entaildir ^ "/" ^ basename))
    val ex2 = map_fst rename_allvar ex1
    val ex3 = map_fst (subst (prime_boolvar_sub maxvar)) ex2
  in
    map (fn (a,b) => [(mk_head a,b)]) ex3
  end

(* -------------------------------------------------------------------------
   Tree neural network
   ------------------------------------------------------------------------- *)

val tnnparam = map_assoc (dim_std (2,12)) operl @ [(head_entail,[12,12,1])]

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 8, nepoch = 50}] @
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 50}] @
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 32, nepoch = 50}] @
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 64, nepoch = 50}]

(* -------------------------------------------------------------------------
   Train
   ------------------------------------------------------------------------- *)

fun train_fixed () =
  let
    val trainex = import_entaildata 10 "train.txt"
    val tnn = train_tnn schedule (random_tnn tnnparam) (trainex,[])
  in
    mkDir_err entaildir;
    write_tnn (entaildir ^ "/tnn") tnn; tnn
  end

(* ------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun test_fixed tnn =
  let
    val filel =
      ["validate.txt","test_easy.txt","test_hard.txt",
       "test_big.txt","test_massive.txt","test_exam.txt"]
    val exl = map (import_entaildata 26) filel
  in
    map (tnn_accuracy tnn) exl
  end

(*
load "aiLib"; open aiLib;
load "mleEntail"; open mleEntail;
val tnn = train_fixed (); (* takes a minute to parse the data set *)
val l = test_fixed tnn;
*)


end (* struct *)
