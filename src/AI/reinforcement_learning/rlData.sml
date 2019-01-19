(* ========================================================================= *)
(* FILE          : rlData.sml                                              *)
(* DESCRIPTION   : Datasets                                                  *)
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

val ERR = mk_HOL_ERR "rlMiniEx"

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)

fun is_refl tm =
  let val (a,b) = dest_eq tm in a = b end handle HOL_ERR _ => false
fun ap_tac tm = (snd o only_hd o fst o AP_TERM_TAC) ([],tm);
fun sym_tac tm = let val (a,b) = dest_eq tm in mk_eq (b,a) end
val ax1 = ``x + 0 = x``;
val ax2 = ``x * 0 = 0``;
val ax3 = ``x + SUC y = SUC (x + y)``;
val ax4 = ``x * SUC y = x * y + x``;

val ax5 = sym_tac ax3;
val ax6 = sym_tac ax4;
val ax7 = sym_tac ax1;
val axl_glob = [ax1,ax2,ax3,ax4,ax5,ax6,ax7];

(* -------------------------------------------------------------------------
   Axioms
   ------------------------------------------------------------------------- *)

fun random_subset n l = first_n n (shuffle l)

fun gen_valeq d (n,m) (n1,n2) =
  let
    val (l1,l2) = (dfind n1 d, dfind n2 d)
    val l = random_subset (n+m) (cartesian_product l1 l2)
    val (train,test) = part_n n l
  in
    (map mk_eq train, map mk_eq test)
  end

fun term_to_int tm =
 assoc tm
   ([(``0``,0),(``1``,1),(``2``,2),(``3``,3),(``4``,4)] @
    [(``5``,5),(``6``,6),(``7``,7),(``8``,8),(``9``,9)]);



(* -------------------------------------------------------------------------
   Supervised learning
   ------------------------------------------------------------------------- *)

fun occurSUC tm = can (find_term (fn x => x = ``SUC``)) tm
fun int_of_bool a = if a then 1 else 0
fun bool_compare (a,b) = Int.compare (int_of_bool a, int_of_bool b)
fun nboccurSUC tm = length (find_terms (fn x => x = ``SUC``) tm);

(* Occurence of SUC *)
fun data_nboccurSUC () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size 10 (``:num``,cset)
    val tml1 = mapfilter (fn x => (nboccurSUC x,x)) tml0
    val tmld = dregroup Int.compare tml1
    val tml2 = filter (fn x => length (snd x) >= 100) (dlist tmld);
    fun f _ =
      let
        val (n,class) = hd (shuffle tml2)
        val r = Math.pow (0.5, Real.fromInt n)
        val trainex = (hd (shuffle class),r)
        val testex = (hd (shuffle class),r)
      in
        (trainex,testex)
      end
  in
    split (List.tabulate (8000,f))
  end

fun read_nboccur r = Math.ln r / Math.ln 0.5

(* Number of correct top symbols *)

(* Tree-edit distance *)

fun eval_ground tm = (rhs o concl o EVAL) tm

(* Ground *)
fun data_truth () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size 10 (``:num``,cset)
    val tml1 =
      mapfilter (fn x => (term_to_int (eval_ground x),x)) tml0
    val tmld = dregroup Int.compare tml1
    val nnl = cartesian_product [0,1,2,3,4] [0,1,2,3,4]
    val (nnT,nnF) = partition (fn (a,b) => a = b) nnl
    val (trainTl,testTl) = split (map (gen_valeq tmld (320,80)) nnT)
    val (trainT,testT) = (List.concat trainTl, List.concat testTl)
    val (trainFl,testFl) = split (map (gen_valeq tmld (80,20)) nnF)
    val (trainF,testF) = (List.concat trainFl, List.concat testFl)
    fun f r x = (x,r)
  in
    (map (f 1.0) trainT @ map (f 0.0) trainF,
     map (f 1.0) testT @ map (f 0.0) testF)
  end

(* test class of the polynomial by looking at this table *)

fun instx i tm = subst [{redex = ``x:num``, residue = i}] tm;

val inputl = [``0``,``1``,``2``,``3``,``4``,``5``,``6``,``7``,``8``,``9``];

fun graph_of tm = map (eval_ground o C instx tm) inputl

(* One universally quantified variable *)
fun data_truth_forallvar () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``,``x:num``]
    val tml0 = gen_term_size 10 (``:num``,cset)
    val tml1 = mapfilter (fn x => (graph_of x,x)) tml0
    val tmld = dregroup (list_compare Term.compare) tml1
    val tml2 = filter (fn x => length (snd x) >= 500) (dlist tmld);
    fun addT _ =
      let
        val class = snd (hd (shuffle tml2))
        val trainex = mk_eq (pair_of_list (first_n 2 (shuffle class)))
        val testex = mk_eq (pair_of_list (first_n 2 (shuffle class)))
      in
        (trainex,testex)
      end
    val (trainT,testT) = split (List.tabulate (8000,addT))
    fun addF _ =
      let
        val (class1,class2) =
          pair_of_list (map snd (first_n 2 (shuffle tml2)))
        val trainex = mk_eq (hd (shuffle class1), hd (shuffle class2))
        val testex =  mk_eq (hd (shuffle class1), hd (shuffle class2))
      in
        (trainex,testex)
      end
    val (trainF,testF) = split (List.tabulate (8000,addF))
    fun f r x = (x,r)
  in
    (map (f 1.0) trainT @ map (f 0.0) trainF,
     map (f 1.0) testT @ map (f 0.0) testF)
  end

(* One existentially quantified variable *)
fun real_of_bool b = if b then 1.0 else 0.0

fun data_truth_existsvar () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``,``x:num``]
    val tml0 = gen_term_size 10 (``:num``,cset)
    val tml1 = mapfilter (fn x => (graph_of x,x)) tml0
    val tmld = dregroup (list_compare Term.compare) tml1
    val tml2 = filter (fn x => length (snd x) >= 500) (dlist tmld);
    fun add bclass n =
      let
        val (graph1,class1) = hd (shuffle tml2)
        val (graph2,class2) = hd (shuffle tml2)
        val b = exists (op =) (combine (graph1,graph2))
        val trainex = mk_eq (hd (shuffle class1), hd (shuffle class2))
        val testex =  mk_eq (hd (shuffle class1), hd (shuffle class2))
      in
        if b = bclass
        then ((trainex,real_of_bool bclass),(testex,real_of_bool bclass))
        else add bclass 0
      end
    val (trainT,testT) = split (List.tabulate (8000,add true))
    val (trainF,testF) = split (List.tabulate (8000,add false))
    fun f r x = (x,r)
  in
    (trainT @ trainF, testT @ testF)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning targets for rlGameRewrite
   ------------------------------------------------------------------------- *)

(*
fun predata_mg2 () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``];
    val tml0 = gen_term_size 7 (``:num``,cset);
    val tml1 =
      mapfilter (fn x => ((term_to_int o rhs o concl o EVAL) x,x)) tml0
    val tmld = dregroup Int.compare tml1
    val eql = (fst o gen_valeq tmld (10000000,0)) (0,0)
    val onestepl = map_assoc all_rewrites eql
    val (p0,q0) = partition (is_refl o fst) onestepl
    val tb = mk_tb [] (p0,q0)
  in
    tl (fst tb)
  end

fun select_mg2 x = List.concat (map (random_subset 20) (first_n 5 x))

fun data_mg2 () = select_mg2 (predata_mg2 ())
*)

(* -------------------------------------------------------------------------
   Reinforcement learning targets for rlGameCopy
   ------------------------------------------------------------------------- *)

fun predata_copy () =
  let
    val cset = [``0``,``$+``,``SUC``]
    val tml0 = gen_term_size 15 (``:num``,cset)
    fun f x = (term_size x, x)
    val tmld = dregroup Int.compare (map f tml0)
  in
    map snd (dlist tmld)
  end

fun select_copy x = first_n 200 (List.concat (map (random_subset 20) x));

(* ground truth *)
fun data_copy () = select_copy (predata_copy ());

fun init_incdata () =
  let
    val cset = [``0``,``$+``,``SUC``]
    val tml0 = gen_term_size 10 (``:num``,cset)
  in
    ([],tml0)
  end

fun update_incdata provenl (pl,ul) =
  let
    val (targetl,ulr) = part_n 200 ul (* should match rlEnv value *)
    fun is_proven x = mem x provenl
    val (pl',ul') = partition is_proven targetl
  in
    (pl @ pl', ul' @ ulr)
  end












end (* struct *)

