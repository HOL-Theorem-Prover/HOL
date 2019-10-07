(* ========================================================================= *)
(* FILE          : mleArithData.sml                                          *)
(* DESCRIPTION   : Data for elementary arithmetic problems                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleArithData :> mleArithData =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTacticData mlTreeNeuralNetwork
  mleLib

val ERR = mk_HOL_ERR "mleArithData"

(* -------------------------------------------------------------------------
   Arithmetical term generation
   ------------------------------------------------------------------------- *)

fun num_operl n =
  [``SUC``,``$+``,``$*``] @ map mk_sucn (List.tabulate (n+1,I))

fun random_numtm (nsuc,nsize) = random_term (num_operl nsuc) (nsize,``:num``)

(* -------------------------------------------------------------------------
   Set of arithmetical examples
   ------------------------------------------------------------------------- *)

fun create_exset_class notset nex (nsuc,nsize) =
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
    map_assoc (create_exset_class notset nex) l
  end

fun create_exset tml nex (nsuc,nsize) =
  let val notset = ref (dset Term.compare tml) in
    List.concat (map snd (create_exset_table notset nex (nsuc,nsize)))
  end

(* -------------------------------------------------------------------------
   Creation of training set, validation set and test set and export
   ------------------------------------------------------------------------- *)

fun create_train nex = create_exset [] nex (10,10)
fun create_alt nex = create_exset [] nex (0,10)
fun create_valid tml nex = create_exset tml nex (10,10)
fun create_test tml nex = create_exset tml nex (10,10)
fun create_big tml nex = create_exset tml nex (10,20)

val dataarith_dir = HOLDIR ^ "/src/AI/experiments/data_arith"

(* -------------------------------------------------------------------------
   Export term as an s-expression with statistics about value and proof length
   ------------------------------------------------------------------------- *)

fun export_arithdata databare =
  let
    val dir = HOLDIR ^ "/src/AI/experiments/data_arithexport"
    val _ = mkDir_err dir
    val tml = import_terml (dataarith_dir ^ "/" ^ databare)
    fun f tm =
      let val ps = its (lo_prooflength 500 tm) handle Option => "?" in
        tts tm ^ ","  ^ its (eval_numtm tm) ^ "," ^  ps
      end
  in
    writel (dir ^ "/" ^ databare) (map f tml)
  end

(*
load "mleArithData"; open mleArithData;
app export_arithdata ["train","valid","test","big"];
*)


(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun read_arithtml databare = import_terml (dataarith_dir ^ "/" ^ databare)

fun regroup_by_metric f tml =
  let val d = dregroup Int.compare (map swap (map_assoc f tml)) in
    map_snd length (dlist d)
  end

(*
load "aiLib"; open aiLib;
val dir = "/home/thibault/prague-server/papers/2019-10-CPP/stats";
load "mleArithData"; open mleArithData;
val traintml = read_arithtml "train";
length traintml;
val trainsize = regroup_by_metric term_size traintml;
write_texgraph (dir ^ "/trainsize") ("size","number") trainsize;
val trainvalue = regroup_by_metric eval_numtm traintml;
write_texgraph (dir ^ "/trainvalue") ("value","number") trainvalue;
val x = sum_int (map snd (filter (fn x => fst x <= 100) trainvalue));

load "mleLib"; open mleLib;
fun f x = lo_prooflength 500 x handle Option => ~1;
val trainlength = regroup_by_metric f traintml;
write_texgraph (dir ^ "/trainlength") ("length","number") trainlength;
val x = sum_int (map snd (filter (fn x => fst x <= 100) trainlength));


load "mleArithData"; open mleArithData;
val tml = create_alt 1000; 


fun f x = lo_prooflength 10000 x handle Option => ~1;
val trainlength = regroup_by_metric f traintml;

val validtml = read_arithtml "valid";
length validtml;
val validsize = regroup_by_metric term_size validtml;
write_texgraph (dir ^ "/validsize") ("size","number") validsize;

val testtml = read_arithtml "test";
length testtml;
val testsize = regroup_by_metric term_size testtml;
write_texgraph (dir ^ "/testsize") ("size","number") testsize;





*)



end (* struct *)
