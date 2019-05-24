(* ========================================================================= *)
(* FILE          : mleEntail.sml                                             *)
(* DESCRIPTION   : Experiments on satisfiability of boolean formulas         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mleEntail :> mleEntail =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleEntail"

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
         (Term [QUOTE s'] handle HOL_ERR _ => raise ERR "read_ex" s')
       end
  in
    (mk_eq (dm_to_hol s1, dm_to_hol s2), [Real.fromInt (string_to_int s3)]) 
  end;

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

val entail_dir = HOLDIR ^ "/src/AI/experiments/data_entail"

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
  let val operl =
    [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),
     (``$= :bool -> bool -> bool``,2)] @ 
    [(``x:bool``,0),(prime_tag,1)]
  in
    random_tnn (dim,1) operl
  end

(* -------------------------------------------------------------------------
   Train
   ------------------------------------------------------------------------- *)

fun train_fixed basename =
  let
    val trainex = exprimed_from_file 10 basename
    val bsize = 16
    val schedule = [(100, 0.02 / (Real.fromInt bsize))]
    val ncore = 4
    val randtnn = entail_random_tnn 12
    val tnn = prepare_train_tnn (ncore,bsize) randtnn 
      (trainex,first_n 100 trainex) schedule
  in
    write_tnn (entail_dir ^ "/" ^ basename) tnn;
    accuracy_set tnn trainex
  end

(* ------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun accuracy_fixed tnn =
  let
    val filel = 
      ["validate.txt","test_easy.txt","test_hard.txt",
       "test_big.txt","test_massive.txt","test_exam.txt"]
    val exl = map (exprimed_from_file 26) filel
  in 
    map (accuracy_set tnn) exl
  end


end (* struct *)
