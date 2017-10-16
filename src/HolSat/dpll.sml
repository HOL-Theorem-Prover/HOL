(* Taken from code by Michael Norrish to        *)
(* accompany Proof Tools chapter of the Manual. *)
(* Acts as a failsafe for SAT_TAUT_PROVE        *)
(* on trivial problems.                         *)
(* Ultimate entry-point is DPLL_TAUT            *)

structure dpll =
struct

open HolKernel Parse boolLib def_cnf satCommonTools satTools

datatype result = Unsat of thm | Sat of term -> term

fun count_vars ds acc =
    case ds of
      [] => acc
    | lit::lits => let
        val v = dest_neg lit handle HOL_ERR _ => lit
      in
        case Binarymap.peek (acc, v) of
          NONE => count_vars lits (Binarymap.insert(acc,v,1))
        | SOME n => count_vars lits (Binarymap.insert(acc,v,n + 1))
      end

fun getBiggest acc =
    #1 (Binarymap.foldl(fn (v,cnt,a as (bestv,bestcnt)) =>
                           if cnt > bestcnt then (v,cnt) else a)
                       (boolSyntax.T, 0)
                       acc)

(* The first unit we see, or the var that occurs most often *)
fun find_splitting_var phi = let
  fun recurse acc [] = getBiggest acc
    | recurse acc (c::cs) = let
        val ds = strip_disj c
      in
        case ds of
          [lit] => (dest_neg lit handle HOL_ERR _ => lit)
        | _ => recurse (count_vars ds acc) cs
      end
in
  recurse (Binarymap.mkDict Term.compare) (strip_conj phi)
end

fun casesplit v th = let (*th is [assignments, cnf] |- current *)
  val eqT = ASSUME (mk_eq(v, boolSyntax.T)) (* v = T |- v = T *)
  val eqF = ASSUME (mk_eq(v, boolSyntax.F)) (* v = F |- v = F *)
in
  (REWRITE_RULE [eqT] th, REWRITE_RULE [eqF] th) (* [assignments,v=T,cnf] |- cnf[T/v] ... *)
end

fun mk_satmap th = let
  val hyps = hypset th
  fun foldthis (t,acc) = let
    val (l,r) = dest_eq t
  in
    Binarymap.insert(acc,l,r)
  end handle HOL_ERR _ => acc
  val fmap = HOLset.foldl foldthis (Binarymap.mkDict Term.compare) hyps
in
  Sat (fn v => Binarymap.find(fmap,v)
          handle Binarymap.NotFound => boolSyntax.T)
end

fun CoreDPLL initial_th = let (* [ci] |- cnf *)
   fun recurse th = let (* [assigns, ci] |- curr *)
    val c = concl th (* current *)
  in
    if aconv c boolSyntax.T then
      mk_satmap th
    else if aconv c boolSyntax.F then
      Unsat th
    else let
        val v = find_splitting_var c
        val (l,r) = casesplit v th (*[assigns,v=T,ci]|- curr[T/v],[assigns,v=F,ci]|- curr[F/v]*)
      in
        case recurse l of
          Unsat l_false =>
          (case recurse r of
               Unsat r_false =>
               Unsat (DISJ_CASES (SPEC v BOOL_CASES_AX) l_false r_false)
	       (* [assignsr\v,assignsl\v,ci] |- F *)
            | x => x)
        | x => x
      end
  end
in
   recurse initial_th (* [ci] |-  F *)
end

fun doCNF neg_tm =  (* clauses is (ci,[~t] |- ci') pairs, where ci' is expanded ci *)
    let val (cnfv,vc,lfn,clauseth) = to_cnf false neg_tm
	val clauses = Array.foldr (fn ((c,th),l) => (c,th)::l) [] clauseth
	val cnf_thm = List.foldl (fn ((c,_),cnf) => CONJ (ASSUME c) cnf)(*[ci] |- cnf*)
				  (ASSUME (fst (hd clauses))) (tl clauses)
    in (cnfv,cnf_thm,lfn,clauses) end

fun undoCNF lfn clauses th = (* th is [ci] |-  F *)
    let val insts = RBM.foldl (fn (v,t,insts) => (v |-> t)::insts) [] lfn
	val inst_th = INST insts th
	val th0 = List.foldl (fn ((_,cth),th) => PROVE_HYP cth th) inst_th clauses (* ~t |- F *)
    in th0 end

fun mk_model_thm cnfv lfn t f =
    if isSome cnfv then let
	    val fvs = List.map fst (RBM.listItems lfn)
	    val model = List.map (fn v => if is_T (f v) then v else mk_neg v) fvs
	    val model2 = mapfilter (fn l => let val x = hd(free_vars l)
						val y = rbapply lfn x
					    in if is_var y then subst [x|->y] l
					       else failwith"" end) model
	in satCheck model2 (mk_neg t) end else
    let val fvs = free_vars t
	val model = List.map (fn v => if is_T (f v) then v else mk_neg v) fvs
    in satCheck model (mk_neg t) end

fun DPLL_TAUT t = let
  val (cnfv,cnf_thm,lfn,clauses) = doCNF (mk_neg t) (* cnf_thm is [ci] |- dCNF(~t) *)
in
  case CoreDPLL cnf_thm of
      Unsat cnf_entails_F =>  (* [ci] |- F *)
        undoCNF lfn clauses cnf_entails_F (* [~t] |- F *)
    | Sat f => mk_model_thm cnfv lfn t f (* |- model ==> ~t *)
end

(* implementation of DPLL ends *)

(* ----------------------------------------------------------------------
    Code below, due to John Harrison, generates tautologies stating that
    two different implementations of binary addition are equivalent
   ---------------------------------------------------------------------- *)

(*
fun halfsum x y = mk_eq(x,mk_neg y)
fun halfcarry x y = mk_conj(x,y)
fun ha x y s c = mk_conj(mk_eq(s,halfsum x y), mk_eq(c,halfcarry x y))

fun carry x y z = mk_disj(mk_conj(x,y), mk_conj(mk_disj(x,y), z))
fun sum x y z = halfsum (halfsum x y) z;
fun fa x y z s c = mk_conj(mk_eq(s,sum x y z), mk_eq(c,carry x y z))

fun list_conj cs = list_mk_conj cs handle HOL_ERR _ => boolSyntax.T

fun ripplecarry x y c out n =
    list_conj
      (List.tabulate(n, (fn i => fa (x i) (y i) (c i) (out i) (c (i + 1)))))

fun mk_index s i = mk_var(s ^ "_" ^ Int.toString i, bool)

val [x,y,out,c] = map mk_index ["X", "Y", "OUT", "C"]
val twobit_adder = ripplecarry x y c out 2

fun simp t =
    rhs (concl (QCONV (REWRITE_CONV [GSYM CONJ_ASSOC, GSYM DISJ_ASSOC]) t))

fun ripplecarry0 x y c out n =
    simp (ripplecarry x y (fn i => if i = 0 then boolSyntax.F
                                   else c i) out n)

fun ripplecarry1 x y c out n =
    simp (ripplecarry x y (fn i => if i = 0 then boolSyntax.T
                                   else c i) out n)

fun mux sel in0 in1 = mk_disj(mk_conj(mk_neg sel,in0), mk_conj(sel,in1))

fun offset n x i = x (n + i)
fun carryselect x y c0 c1 s0 s1 c s n k = let
  val k' = Int.min(n,k)
  val fm =
      mk_conj(mk_conj(ripplecarry0 x y c0 s0 k', ripplecarry1 x y c1 s1 k'),
              mk_conj(mk_eq(c k', mux (c 0) (c0 k') (c1 k')),
                      list_conj
                      (List.tabulate
                       (k',
                        (fn i => mk_eq(s i, mux (c 0) (s0 i) (s1 i)))))))
in
  if k' < k then fm
  else mk_conj(fm, carryselect (offset k x) (offset k y)
                               (offset k c0) (offset k c1)
                               (offset k s0) (offset k s1)
                               (offset k c) (offset k s)
                               (n - k) k)
end

(* call with positive n and k to generate tautologies *)
fun mk_adder_test n k = let
  val [x,y,c,s,c0,s0,c1,s1,c2,s2] =
      map mk_index ["x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2"]
in
  simp
    (mk_imp(mk_conj(mk_conj(carryselect x y c0 c1 s0 s1 c s n k, mk_neg (c 0)),
                    ripplecarry0 x y c2 s2 n),
            mk_conj(mk_eq(c n, c2 n),
                    list_conj(List.tabulate(n, (fn i => mk_eq(s i, s2 i)))))))
end

(* example in tutorial is *)

val example = gen_all (mk_adder_test 3 2)

*)
end
