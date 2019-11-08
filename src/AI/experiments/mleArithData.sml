(* ========================================================================= *)
(* FILE          : mleArithData.sml                                          *)
(* DESCRIPTION   : Data for elementary arithmetic problems                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleArithData :> mleArithData =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTacticData mlTreeNeuralNetwork
  mleLib mlFeature

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
app export_arithdata ["train","valid","test"];
*)



fun export_computefea databare =
  let
    val dir = HOLDIR ^ "/src/AI/experiments/exp_compute"
    val _ = mkDir_err dir
    val tml' =
      import_terml (dataarith_dir ^ "/test") @
      import_terml (dataarith_dir ^ "/train")
    fun all_features x =
      let val l = List.concat (map (feahash_of_term_mod 1299827) x) in
        dnew Int.compare (number_snd 0 (mk_fast_set Int.compare l))
      end
    val tml = import_terml (dataarith_dir ^ "/" ^ databare)
    val d = all_features tml'
    fun f tm =
      let
        val il1 = dict_sort Int.compare
          (map (fn x => dfind x d) (feahash_of_term_mod 1299827 tm))
        val il2 = map (fn x => (its x ^ ":1")) il1
      in
        ("+" ^ its (eval_numtm tm mod 16) ^ " " ^
         String.concatWith " " il2)
      end
  in
    writel (dir ^ "/" ^ databare) (map f tml)
  end

(*
load "mleArithData"; open mleArithData;
app export_computefea ["train","test"];
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
val dir = "/home/thibault/prague-server/papers/2019-10-CPP/figures";
load "mleArithData"; open mleArithData;
val traintml = read_arithtml "train";
fun compare_termsize (a,b) = Int.compare (term_size b,term_size a);

length traintml;
val trainsize = regroup_by_metric term_size traintml;
write_texgraph (dir ^ "/trainsize") ("size","number") trainsize;
val trainvalue = regroup_by_metric eval_numtm traintml;
write_texgraph (dir ^ "/trainvalue") ("value","number") trainvalue;
val x = sum_int (map snd (filter (fn x => fst x <= 100) trainvalue));

fun U x = Int.min (term_size x, eval_numtm x);
val trainU= regroup_by_metric U traintml;
write_texgraph (dir ^ "/trainU") ("U","number") trainU;

fun mod16 x = eval_numtm x mod 16;
val trainmod16 = regroup_by_metric mod16 traintml;
write_texgraph (dir ^ "/trainmod16") ("mod16","number") trainmod16;

fun valsize x = if (eval_numtm x > term_size x) then 2
            else if eval_numtm x = term_size x then 1 else 0;
val trainvalsize = regroup_by_metric valsize traintml;
map_snd (fn x => int_div x 11990) trainvalsize;

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

load "psTermGen"; open psTermGen;
fun mk_train_alt (n,m) =
  random_terml [``SUC``,``0``,``$+``,``$*``] (n,``:num``) m;

val train_alt = List.concat (map mk_train_alt trainsize);
val train_alt = it;
length train_alt;
val l = filter (fn x => eval_numtm x = 0) train_alt;
int_div (length l) (length train_alt);

val l12 = filter (fn x => term_size x = 12) traintml;
val l12' = filter (fn x => eval_numtm x = 0) l12;
int_div (length l12') (length l12);

val l = filter (fn x => eval_numtm x = 0) traintml;
int_div (length l) (length traintml);






*)



end (* struct *)
