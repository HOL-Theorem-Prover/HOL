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
    (traintml, validtml)
  end

fun create_test tml nex =
  let val notset = ref (dset Term.compare tml) in
    List.concat (map snd (create_exset_table notset nex (10,10)))
  end

fun create_big tml nex =
  let val notset = ref (dset Term.compare tml) in
    List.concat (map snd (create_exset_table notset nex (10,20)))
  end

(*
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
val data_in = HOLDIR ^ "/src/AI/experiments";

val (traintml,validtml) = create_train_valid 200;
export_terml (data_in ^ "/data200_train") traintml;
export_terml (data_in ^ "/data200_valid") validtml;
*)

(*
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
val traintml = import_terml (data_in ^ "/data200_train");
val validtml = import_terml (data_in ^ "/data200_valid");

val testtml = create_test (traintml @ validtml) 200;
export_terml (data_in ^ "/data200_test") testtml;
val bigtml = create_big (traintml @ validtml @ testtml) 200;
export_terml (data_in ^ "/data200_big") bigtml;
*)


(*
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
load "aiLib"; open aiLib;

fun compressed_size tm = 
  let val (oper,argl) = strip_comb tm in
    if is_suc_only tm then 1
    else 1 + sum_int (map compressed_size argl)
  end
fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => its a ^ " " ^ its b) l);
fun comp_stats file =
  let
    val l0 = import_terml file
    val l1 = map_assoc compressed_size l0;
    val l2 = dlist (dregroup Int.compare (map swap l1));
  in
    map_snd length l2 
  end;

val data_out = "/home/thibault/prague-server/papers/2019-05-NIPS/data";

val stats1 = comp_stats (data_in ^ "/data200_train");
write_graph (data_out ^ "/comp_train") ("csize","total") stats1;

val stats2 = comp_stats (data_in ^ "/data200_valid");
write_graph (data_out ^ "/comp_valid") ("csize","total") stats2;

val stats3 = comp_stats (data_in ^ "/data200_test");
write_graph (data_out ^ "/comp_test") ("csize","total") stats3;

val stats4 = comp_stats (data_in ^ "/data200_big");
write_graph (data_out ^ "/comp_big") ("csize","total") stats4;


val tml2 = dict_sort compare_imin tml1;
*)

end (* struct *)
