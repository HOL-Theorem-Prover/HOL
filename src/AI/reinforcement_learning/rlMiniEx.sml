(* ========================================================================= *)
(* FILE          : rlMiniEx.sml                                              *)
(* DESCRIPTION   : Datasets                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniEx :> rlMiniEx =
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
   Tablebase (shortest proof)
   ------------------------------------------------------------------------- *)

fun sub_tac (tm,pos) ax =
  let val subtm = subtm_at_pos pos tm in
    if can (match_term (lhs ax)) subtm then
      let
        val (sub,_) = match_term (lhs ax) subtm
        val res = subst sub (rhs ax)
        val holetm = hole_position (tm,pos)
        val holesub = [{redex = numhole_var, residue = res}]
      in
        subst holesub holetm
      end
    else raise ERR "sub_tac" ""
  end

fun ax_rewrites (tm,pos) = mapfilter (sub_tac (tm,pos)) axl_glob

fun all_rewrites tm =
  let
    val posl = filter (not o null) (map fst (all_posred tm))
    fun f pos = ax_rewrites (tm,pos)
  in
    mk_fast_set Term.compare (List.concat (map f posl))
  end

fun is_provable d (_,l) = exists (fn x => dmem x d) l

fun mk_tb acc (p,q) =
  let
    val _ = print_endline (int_to_string (length p))
    val pdict = dnew Term.compare p
    val (p',q') = partition (is_provable pdict) q
  in
    if null p'
    then (rev acc, q)
    else mk_tb (map fst p' :: acc) (p',q')
  end

(* -------------------------------------------------------------------------
   Minigame 1
   ------------------------------------------------------------------------- *)

fun data_mg1 () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size 10 (``:num``,cset)
    val tml1 =
      mapfilter (fn x => ((term_to_int o rhs o concl o EVAL) x,x)) tml0
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

(* -------------------------------------------------------------------------
   Minigame 2
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Minigame 3
   ------------------------------------------------------------------------- *)

fun predata_mg3 () =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size 15 (``:num``,cset)
    fun f x = (term_size x, x)
    val tmld = dregroup Int.compare (map f tml0)
  in
    snd (part_n 4 (map snd (dlist tmld)))
  end

fun select_mg3 x = List.concat (map (random_subset 10) x)

fun data_mg3 () = select_mg3 (predata_mg3 ());




end (* struct *)






