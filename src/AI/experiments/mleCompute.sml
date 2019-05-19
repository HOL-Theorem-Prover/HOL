(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleCompute"


(* -------------------------------------------------------------------------
   Generation of random arithmetical term
   ------------------------------------------------------------------------- *)

fun add_I x = mk_comb (``I:num -> num``,x);

fun operl_compute n = 
  [``SUC``,``$+``,``$*``] @ 
  map (add_I o mk_sucn) (List.tabulate (n+1,I));

fun random_numtm (nsuc,nsize) = 
  random_term (operl_compute nsuc) (nsize,``:num``);

(* -------------------------------------------------------------------------
   Evaluation of a term to int
   ------------------------------------------------------------------------- *)

fun eval_numtm tm = 
  (string_to_int o term_to_string o rhs o concl o bossLib.EVAL) tm


(* -------------------------------------------------------------------------
   Creation of set of examples
   ------------------------------------------------------------------------- *)

fun create_exset notset nex (nsuc,nsize) =
  let
    val d = ref (dempty Term.compare)
    fun random_exl n =   
      if n <= 0 orelse dlength (!d) >= nex then () else
      let val tm = random_numtm (nsuc,nsize) in
        if dmem tm (!notset) orelse dmem tm (!d) then () 
        else (d := dadd tm () (!d); notset := dadd tm () (!notset)); 
        random_exl (n - 1)
      end
  in
    random_exl (nex * 10); dkeys (!d)
  end

fun create_exset_table notset nex (nsuc,nsize) =
  let 
    fun f x = x + 1 
    val l = cartesian_product (List.tabulate (nsuc,f)) 
                              (List.tabulate (nsize,f))
  in
    map_assoc (create_exset notset nex) l
  end

(* -------------------------------------------------------------------------
   Creation of training set, validation set and training set
   ------------------------------------------------------------------------- *)

fun create_allex nex =
  let 
    val notset = ref (dempty Term.compare)
    val l0 = create_exset_table notset nex (10,10)
    val l1 = List.concat (map snd l0)
    val trainex = map_assoc (bin_rep 4 o eval_numtm) l1
    val l2 = create_exset_table notset nex (10,10)
    val l3 = List.concat (map snd l2)
    val validex = map_assoc (bin_rep 4 o eval_numtm) l3
  in
    (trainex,validex)
  end

fun stats_ex ex =
  let 
    val l0 = map_assoc (fn x => eval_numtm x mod 16) (map fst ex)
    val l1 = dregroup Int.compare (map swap l0) 
  in
    map_snd length (dlist l1)
  end

(* -------------------------------------------------------------------------
   Tnn for compute
   ------------------------------------------------------------------------- *)

fun random_tnn_compute dim =
  let 
    val operl = mk_fast_set oper_compare (operl_of ``I 0 + SUC 0 * 0``)
    val nbit = 4
  in
    random_tnn (dim,nbit) operl
  end

(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleCompute"; open mleCompute;

val (trainex,validex) = create_allex 200;

val randtnn = random_tnn_compute dim;
val bsize = 64;
val schedule = [200, 0.1 / (Real.fromInt bsize)];
val ncore = 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex,first_n 100 
trainex) schedule;

val r1 = accuracy_set tnn trainex;
val r2 = accuracy_set tnn validex;
*)

end (* struct *)
