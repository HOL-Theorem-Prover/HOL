(* ========================================================================= *)
(* FILE          : mleArithData.sml                                          *)
(* DESCRIPTION   : Data for elementary arithmetic problems                   *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleArithData :> mleArithData =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTacticData 
mlTreeNeuralNetwork mlFeature numSyntax

val ERR = mk_HOL_ERR "mleArithData"
val arithdir = HOLDIR ^ "/examples/AI_TNN/data_arith"

(* -------------------------------------------------------------------------
   Arithmetic
   ------------------------------------------------------------------------- *)

fun mk_sucn n = funpow n mk_suc zero_tm

fun eval_numtm tm =
  (string_to_int o term_to_string o rhs o concl o computeLib.EVAL_CONV) tm

(* -------------------------------------------------------------------------
   Arithmetical term generation
   ------------------------------------------------------------------------- *)

fun num_operl n = 
  [``SUC``,``$+``,``$*``] @ map mk_sucn (List.tabulate (n+1,I))
fun random_numtm (nsuc,nsize) = 
  random_term (num_operl nsuc) (nsize,``:num``)

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
fun create_valid tml nex = create_exset tml nex (10,10)
fun create_test tml nex = create_exset tml nex (10,10)

(* -------------------------------------------------------------------------
   Export/Import functions
   ------------------------------------------------------------------------- *)

fun create_export_arithdata () =
  let
    val _ = mkDir_err arithdir
    val tmltrain = create_train 200
    val tmlvalid = create_valid tmltrain 200
    val tmltest = create_test (tmltrain @ tmlvalid) 200
    fun f tm = tts tm ^ "," ^ its (eval_numtm tm)
  in
    writel (arithdir ^ "/train") (map f tmltrain);
    writel (arithdir ^ "/valid") (map f tmlvalid);
    writel (arithdir ^ "/test") (map f tmltest)
  end

(*
load "mleArithData"; open mleArithData;
val _ = create_export_arithdata ();
*)

fun lisp_to_arith lisp = 
  case lisp of
    Lstring "0" => zero_tm
  | Lterm [Lstring "S",a] => mk_suc (lisp_to_arith a)
  | Lterm [Lstring "+",a,b] => mk_plus (lisp_to_arith a, lisp_to_arith b)
  | Lterm [Lstring "*",a,b] => mk_mult (lisp_to_arith a, lisp_to_arith b)
  | _ => raise ERR "lisp_to_arith" ""

fun import_arithdata dataname = 
  let 
    val l1 = readl (arithdir ^ "/" ^ dataname)
    val l2 = map pair_of_list (mk_batch_full 2 l1)
    val l3 = map_snd string_to_int l2
    fun f x = if x = "0" then zero_tm else
      (lisp_to_arith o singleton_of_list o lisp_parser) x
  in
    map_fst f l3
  end 

(*
load "mleArithData"; open mleArithData;
load "aiLib"; open aiLib;
val train = import_arithdata "train";
*)

(* -------------------------------------------------------------------------
   Write subterm features for feature-based predictors
   ------------------------------------------------------------------------- *)

fun export_arithfea dataname =
  let
    val tml' = map fst (List.concat (map import_arithdata ["test","train"]))
    fun all_features x =
      let val l = List.concat (map (feahash_of_term_mod 1299827) x) in
        dnew Int.compare (number_snd 0 (mk_fast_set Int.compare l))
      end
    val tml = import_arithdata dataname
    val d = all_features tml'
    fun f (tm,i) =
      let
        val il1 = dict_sort Int.compare
          (map (fn x => dfind x d) (feahash_of_term_mod 1299827 tm))
        val il2 = map (fn x => (its x ^ ":1")) il1
      in
        ("+" ^ its (i mod 16) ^ " " ^ String.concatWith " " il2)
      end
  in
    writel (arithdir ^ "/" ^ dataname ^ "_fea") (map f tml)
  end

(*
load "mleArithData"; open mleArithData;
app export_computefea ["train","test"];
*)

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun regroup_by_metric f tml =
  let val d = dregroup Int.compare (map swap (map_assoc f tml)) in
    map_snd length (dlist d)
  end


end (* struct *)
