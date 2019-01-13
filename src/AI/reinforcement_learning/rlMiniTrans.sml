(* ========================================================================= *)
(* FILE          : rlTrain.sml                                               *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniTrans :> rlMiniTrans =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor";
*)

open HolKernel Abbrev boolLib aiLib rlLib mlTreeNeuralNetwork psTermGen
mlNearestNeighbor rlMiniTruth

val ERR = mk_HOL_ERR "rlMiniTrans"

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)
(*
val pdict = gen_term 8;
val tml0 = dfind 0 pdict;

fun gen_triplet n tml =
  if n <= 0 then [] else
  (hd (shuffle tml),hd (shuffle tml),hd (shuffle tml)) ::
  gen_triplet (n - 1) tml;

fun list_mk_add l = case l of
  [] => raise ERR "" ""
 | [a] => a
 | a :: m => mk_add (a, list_mk_add m)

fun compare_triplet ((a1,a2,a3),(b1,b2,b3)) =
  Term.compare (list_mk_add [a1,a2,a3], list_mk_add [b1,b2,b3]);

val triplet0 = gen_triplet 2100 tml0;
val triplet1 = mk_fast_set compare_triplet triplet0;
val triplet2 = first_n 2000 triplet1;
length triplet2;

fun mk_tripleteq (a,b,c) = (mk_eq (a,b), mk_eq (b,c));
val eql = map mk_tripleteq triplet2;

(* -------------------------------------------------------------------------
   All equalities
   ------------------------------------------------------------------------- *)
fun is_refl tm =
  let val (a,b) = dest_eq tm in a = b end handle HOL_ERR _ => false

fun sym_tac tm = let val (a,b) = dest_eq tm in mk_eq (b,a) end

val ax1 = ``x + 0 = x``;
val ax2 = ``x * 0 = 0``;
val ax3 = ``x + SUC y = SUC (x + y)``;
val ax4 = ``x * SUC y = x * y + x``;
val ax5 = sym_tac ax3;
val ax6 = sym_tac ax4;
val axl_glob = [ax1,ax2,ax3,ax4] @ map sym_tac [ax1,ax2,ax3,ax4];

fun is_axiom_inst tm =
  exists (fn x => can (match_term x) tm) axl_glob
;

val alleq = map mk_eq (cartesian_product tml0 tml0);
val (p0,q0) = partition is_refl alleq;

fun inv_para (tm1,tm2) =
  let
    val (oper1,argl1) = strip_comb tm1
    val (oper2,argl2) = strip_comb tm2
  in
    if oper1 <> oper2
    then [(tm1,tm2)]
    else List.concat (map inv_para (combine (argl1,argl2)))
  end

val paradict =
  dnew (cpl_compare Term.compare Term.compare)
  (map_assoc inv_para (cartesian_product tml0 tml0));

val stepdict =
  let fun f ((tm1,tm2),l) =
    length l = 1 andalso is_axiom_inst (mk_eq (hd l))
  in
    dmap f paradict
  end

fun mk_tablebase n pl (p,q) =
  if n <= 0 then (rev pl,q) else
  let
    fun is_provable x =
      let
        val (ax,bx) = dest_eq x
        fun onestep y =
          let val (ay,by) = dest_eq y in
            if ax = ay then dfind (bx,by) stepdict
            else if bx = by then dfind (ax,ay) stepdict
            else false
          end
      in
        exists onestep p
      end
    val (newp,newq) = partition is_provable q
    val _ = print_endline (int_to_string (length newp))
  in
    mk_tablebase (n-1) (newp :: pl) (newp,newq)
  end

val tb = mk_tablebase 10 [p0] (p0,q0);
map length (fst tb);
length (snd tb);

val proofl0 = number_fst 0 (fst tb @ [snd tb]);
val proofl1 = map swap (distrib proofl0);
val pdict = dnew Term.compare proofl1;

fun mk_evalex (a,b) =
  let
    val (na,nb) = (dfind a pdict, dfind b pdict)
    val sum = na + nb
  in
    (mk_conj (a,b), if sum = 0 then 0.5 else int_div na sum)
  end

val evalex = map mk_evalex eql;

val (trainset,testset) = traintest8020 evalex;
(* possible number equality *)

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun trainset_info_eval trainset =
  let
    val mean = average_real (map snd trainset)
    val dev = standard_deviation (map snd trainset)
  in
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^
    "  mean: " ^ Real.toString mean ^ "\n" ^
    "  standard deviation: " ^ Real.toString dev
  end

fun train_tnn_eval dim randtnn (trainset,testset) =
  if null trainset then (print_endline "empty trainset"; randtnn) else
  let
    val _        = print_endline (trainset_info_eval trainset)
    val bsize    = if length trainset < 16 then 1 else 16
    val schedule = [(100,0.1),(100,0.01)]
    val (ptrain,ptest) = (prepare_trainset_eval trainset,
                          prepare_trainset_eval testset)
    val ((tnn,loss), nn_tim) =
      add_time
      (train_treenn_schedule dim randtnn bsize (ptrain,ptest)) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    tnn
  end

fun tnn_accuracy tnn testset =
  let fun correct (tm,expectv) =
    let val v = eval_treenn tnn tm in
      if expectv > 0.5 then v > 0.5 else v < 0.5
    end
  in
    int_div (length (filter correct testset)) (length testset)
  end



(*

val operl = operl_of_term ``(SUC 0 + 0 * 0 = 0) /\ (0 = 0)``;
val dim = 4;
val randtnn = random_treenn (dim,1) operl;
val tnn = train_tnn_eval dim randtnn (trainset,testset);
val tnnaccuracy = tnn_accuracy tnn testset;


*)


(* trainset *)
fun random_accuracy testset =
  let fun correct (tm,expectv) =
    let val v = random_real () in
      if expectv > 0.5 then v > 0.5 else v < 0.5
    end
  in
    int_div (length (filter correct testset)) (length testset)
  end
val randaccuracy = random_accuracy testset;


(* nearest neighbor *)
val trainfea = map_assoc feahash_of_term (map fst trainset);
val trainfead = dnew Term.compare trainfea;
val symweight = learn_tfidf trainfea;

fun knn_accuracy testset =
  let fun correct (tm,expectv) =
    let
      val predtm = hd (termknn (symweight,trainfead) 1 (feahash_of_term tm))
      val v = assoc predtm trainset
    in
      if expectv > 0.5 then v > 0.5 else v < 0.5
    end
  in
    int_div (length (filter correct testset)) (length testset)
  end

val knnaccuracy = knn_accuracy testset;
*)

(*
eval_treenn tnn
  ``SUC (SUC 0) * SUC (SUC 0) + SUC (SUC 0) = SUC (SUC (SUC (SUC (SUC 0))))``;
*)

end (* struct *)






