(* ========================================================================= *)
(* FILE          : mleArithData.sml                                          *)
(* DESCRIPTION   : Data for elementary arithmetic problems                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleArithData :> mleArithData =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleArithData"

(* -------------------------------------------------------------------------
   Evaluation of an arithmetical term
   ------------------------------------------------------------------------- *)

fun eval_numtm tm = 
  (string_to_int o term_to_string o rhs o concl o bossLib.EVAL) tm

(* -------------------------------------------------------------------------
   Generation of random arithmetical term
   ------------------------------------------------------------------------- *)

fun num_operl n = 
  [``SUC``,``$+``,``$*``] @ map mk_sucn (List.tabulate (n+1,I));

fun random_numtm (nsuc,nsize) = random_term (num_operl nsuc) (nsize,``:num``);

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

fun create_train_valid nex =
  let 
    val notset = ref (dempty Term.compare)
    val l0 = create_exset_table notset nex (10,10)
    val traintml = List.concat (map snd l0)
    val l1 = create_exset_table notset nex (10,10)
    val validtml = List.concat (map snd l1)
  in
    (map_assoc eval_numtm traintml, map_assoc eval_numtm validtml)
  end

fun create_test (trainex,validex) nex =
  let val notset = ref  (dset Term.compare (map fst (trainex @ validex))) in
    create_exset_table notset nex (20,20)
  end

(* -------------------------------------------------------------------------
   Statistics about repartitions of examples.
   ------------------------------------------------------------------------- *)

fun stats_ex ex = map_snd length (dlist (dregroup Int.compare (map swap ex)))

(*
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
val (trainex,validex) = create_train_valid 200;
export_terml (HOLDIR ^ "/src/AI/experiments/data200_train") (map fst trainex);
export_terml (HOLDIR ^ "/src/AI/experiments/data200_valid") (map fst validex);

val testex = create_test (trainex,validex) 20;
*)

end (* struct *)
