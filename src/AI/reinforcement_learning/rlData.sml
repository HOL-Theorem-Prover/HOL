(* ========================================================================= *)
(* FILE          : rlData.sml                                                *)
(* DESCRIPTION   : Creating machine learning data for supervised and         *)
(* reinforcement learning                                                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlData :> rlData =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor"; load "psTermGen";
*)

open HolKernel Abbrev boolLib aiLib rlLib psTermGen

val ERR = mk_HOL_ERR "rlData"

fun eval_ground tm = 
  (string_to_int o term_to_string o rhs o concl o bossLib.EVAL) tm

val uni_flag = ref false



fun random_num operl (nsuc,noper) = 
  let val cset = map mk_sucn (List.tabulate (nsuc,I)) @ operl in
    if !uni_flag 
    then 
      random_term_uni cset 
      (List.tabulate (noper + 1, fn x => 2 * x + 1), ``:num``)
    else random_term_upto cset (2 * noper + 1,``:num``)
  end

fun inter_traintest (train,test) = 
  length (filter (fn x => tmem (fst x) (map fst train)) test)

(* -------------------------------------------------------------------------
   Computation
   ------------------------------------------------------------------------- *)

fun bin_rep nbit n = 
  if nbit > 0 
  then n mod 2 :: bin_rep (nbit - 1) (n div 2)
  else []

val uniq_flag = ref false

fun computation_data operl (nsuc,noper) (nex,nclass,nbit) =
  let
    val d = ref (dempty Int.compare)
    val dr = ref (dempty Term.compare)
    fun random_ex () =
      let
        val tm = random_num operl (nsuc,noper)
        val n = (eval_ground tm) mod nclass
        val nocc = dfind n (!d) handle NotFound => 0
      in
        if nocc >= nex div nclass orelse 
           (!uniq_flag andalso dmem tm (!dr))
        then random_ex () 
        else 
        (
         d := count_dict (!d) [n];
         dr := dadd tm (map Real.fromInt (bin_rep nbit n)) (!dr)
        )
      end
    val _ = d := dempty Int.compare
  in
    ignore (List.tabulate (nex, fn _ => random_ex ()));
    dlist (!dr)
  end

(*
app load ["rlData", "aiLib", "rlLib", "mlTreeNeuralNetwork", "psTermGen"];
open rlData aiLib rlLib mlTreeNeuralNetwork psTermGen;

val operl = [``$+``,``$*``];
val (nsuc,noper) = (16,2);
val (nex,nclass,nbit) = (4000,16,4);

val _ = uniq_flag := false;
val _ = uni_flag := true;
val train = computation_data operl (nsuc,noper) (nex,nclass,nbit);
val _ = uni_flag := false;
val test = computation_data operl (nsuc,noper) (nex,nclass,nbit);
val ninter = inter_traintest (train,test);
val nuniq = length (mk_fast_set Term.compare (map fst train));


val nn_operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``);
val randtnn = random_tnn (8,nbit) nn_operl;
val bsize = 16;
fun f x = (200, x / (Real.fromInt bsize));
val schedule = map f [0.1];
val ncore = 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (train,test) schedule;
*)

(* -------------------------------------------------------------------------
   Proof
   ------------------------------------------------------------------------- *)

val axl = [ax1,ax2,ax3,ax4];

fun rw tm = 
  let 
    fun f pos = 
      let fun test x = isSome (paramod_ground x (tm,pos)) in
        exists test axl
      end
  in
    List.find f (all_pos tm)
  end
 
(*
app load ["rlData", "aiLib", "rlLib", "mlTreeNeuralNetwork", "psTermGen"];
open rlData aiLib rlLib mlTreeNeuralNetwork psTermGen;
val tm = ``(SUC 0 + 0) * 0``;
val pos = valOf (rw tm);
val tm1 = hd (List.mapPartial (C paramod_ground (tm,pos)) [ax1,ax2,ax3,ax4]);
*)

fun lo_trace nmax toptm =
  let
    val l = ref []
    val acc = ref 0
    fun loop tm =
      if is_suc_only tm then rev (!l) 
      else if !acc > nmax then [] else
    let 
      val pos = valOf (rw tm)
      val tm' = hd (List.mapPartial (C paramod_ground (tm,pos)) axl)
    in
      (l := (tm,pos) :: !l; acc := length pos + 1 + !acc; loop tm')
    end
  in
    loop toptm
  end

fun expand_trace trace =
  let 
    fun f (tm,pos) = 
      if null pos then [(tm,pos)] 
      else (tm,pos) :: f (tm,butlast pos) 
  in
    List.concat (map (rev o f) trace)
  end

fun number_trace l = rev (number_snd 1 (rev l))

fun full_trace tm = number_trace (expand_trace (lo_trace 200 tm))
fun term_cost tm = length (full_trace tm)

(* dataset *)
fun proof_data_aux tml =
  mk_fast_set 
    (cpl_compare (cpl_compare Term.compare (list_compare Int.compare))
     Int.compare)
  (List.concat (map full_trace tml))

fun proof_data tml =
  let 
    val pdata = proof_data_aux tml;
    val pdata3 = filter (fn x => null (snd (fst x))) pdata;
    val pdata4 = dict_sort compare_imin pdata3;
    val pdata5 = map_fst fst pdata4;
  in
    pdata5
  end

val cset_glob = map mk_sucn (List.tabulate (4,I)) @ [``$+``,``$*``];
val tml_glob = mk_fast_set Term.compare (gen_term_size 8 (``:num``,cset_glob));
val proof_data_glob = proof_data tml_glob;

(*
app load ["rlData", "aiLib", "rlLib", "mlTreeNeuralNetwork", "psTermGen"];
open rlData aiLib rlLib mlTreeNeuralNetwork psTermGen;





val pdata2 = dict_sort Int.compare (map snd pdata1);
*)

(* -------------------------------------------------------------------------
   Proof
   ------------------------------------------------------------------------- *)

(*
fun list_cost tm =
  let val newtm = (rhs o concl) (norm tm) in
    if term_eq newtm tm then raise ERR "total_cost" "" else
    if is_only_suc newtm then [(newtm,0)] else
      let val cost = 1 + valOf (depth_diff (tm,newtm)) in
        (newtm,cost) :: list_cost newtm
      end
  end

fun total_cost tm = sum_int (map snd (list_cost tm))
*)



end (* struct *)

(*
todo: try to implement momentum.


val (trainset,testset) = mk_ttset_ground2 7;



(* inference *)
fun binary_of_int x = Term [QUOTE (its x)];

fun bin_rep nbit n = 
  if nbit > 0 
  then n mod 2 :: bin_rep (nbit - 1) (n div 2)
  else [];

fun numeral_pos (tm,pos) = 
  let 
    val (oper,argl) = strip_comb tm 
    fun f i x = numeral_pos (x,pos @ [i])
  in
    if term_eq oper ``NUMERAL`` orelse term_eq oper ``0``
    then [(tm,pos)] 
    else List.concat (mapi f argl)
  end
;
fun eval_ground tm = 
  (string_to_int o term_to_string o rhs o concl o bossLib.EVAL) tm
;
fun random_ex k =
      let
        val cset = map binary_of_int (List.tabulate (8,I)) @ [``$+``]
        val tm1 = random_term_upto cset (k,``:num``)
        val tm2 = mk_eq (tm1, binary_of_int (eval_ground tm1 mod 8))
        val (subtm,pos) = random_elem (numeral_pos (tm2,[]))
        val tm3 = subst_pos (tm2,pos) ``x:num``
        val n = eval_ground subtm
      in
        (tm3, map Real.fromInt (bin_rep 1 n))
      end
;

fun accuracy_one (tm,rl) =
  let 
    val rl1 = infer_tnn tnn tm 
    val rl2 = combine (rl,rl1)
    fun test (x,y) = 0.5 > Real.abs (x - y)  
  in
    if all test rl2 then NONE else SOME tm
  end;

fun f k =
  let
    val testset = List.tabulate (1000, fn n => random_ex k);
    val l = List.mapPartial accuracy_one testset;
  in
    length l
  end

val l1 = map f [15,17,19,21];


tts “2 + 5 * 1 + 3”;

infer_tnn tnn ``2 + 5 * 1``;

infer_tnn tnn ``7 + 3``;



todo design good datasets for supervised learning.

make a dataset when you can evaluate a expression 
with binary output.

equations solving. 
?x. x * x = 3.
!a. a+b=b+a.
val s = mk_sucn;

infer_tnn ``^(s 5) + ^(s 3)``;


modular equations.
linear equations.
small non linear equation. 
diophantine equations.

*)





