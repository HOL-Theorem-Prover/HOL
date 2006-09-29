(* Taken from code by Michael Norrish to        *)
(* accompany Proof Tools chapter of the Manual. *)
(* Acts as a failsafe for SAT_TAUT_PROVE        *)
(* on trivial problems.                         *)
(* Ultimate entry-point is DPLL_TAUT            *)
open HolKernel Parse boolLib

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

fun casesplit v th = let
  val eqT = ASSUME (mk_eq(v, boolSyntax.T))
  val eqF = ASSUME (mk_eq(v, boolSyntax.F))
in
  (REWRITE_RULE [eqT] th, REWRITE_RULE [eqF] th)
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


fun CoreDPLL form = let
  val initial_th = ASSUME form
  fun recurse th = let
    val c = concl th
  in
    if c = boolSyntax.T then
      mk_satmap th
    else if c = boolSyntax.F then
      Unsat th
    else let
        val v = find_splitting_var c
        val (l,r) = casesplit v th
      in
        case recurse l of
          Unsat l_false => let
          in
            case recurse r of
              Unsat r_false =>
                Unsat (DISJ_CASES (SPEC v BOOL_CASES_AX) l_false r_false)
            | x => x
          end
        | x => x
      end
  end
in
  case (recurse initial_th) of
    Unsat th => Unsat (CONV_RULE (REWR_CONV IMP_F_EQ_F) (DISCH form th))
  | x => x
end
   fun DPLL t = let
     val (transform, body) = let
       val (vector, body) = dest_exists t
       fun transform body_eq_F = let
         val body_imp_F = CONV_RULE (REWR_CONV (GSYM IMP_F_EQ_F)) body_eq_F
         val fa_body_imp_F = GEN vector body_imp_F
         val ex_body_imp_F = CONV_RULE FORALL_IMP_CONV fa_body_imp_F
       in
         CONV_RULE (REWR_CONV IMP_F_EQ_F) ex_body_imp_F
       end
     in
       (transform, body)
     end handle HOL_ERR _ => (I, t)
   in
     case CoreDPLL body of
       Unsat body_eq_F => Unsat (transform body_eq_F)
     | x => x
   end
val NEG_EQ_F = prove(``(~p = F) = p``, REWRITE_TAC []);
val toCNF = defCNF.DEF_CNF_VECTOR_CONV
fun DPLL_UNIV t = let
  val (vs, phi) = strip_forall t
  val cnf_eqn = toCNF (mk_neg phi)
  val phi' = rhs (concl cnf_eqn)
in
  case DPLL phi' of
    Unsat phi'_eq_F => let
      val negphi_eq_F = TRANS cnf_eqn phi'_eq_F
      val phi_thm = CONV_RULE (REWR_CONV NEG_EQ_F) negphi_eq_F
    in
      EQT_INTRO (GENL vs phi_thm)
    end
  | Sat f => let
      val t_assumed = ASSUME t
      fun spec th =
          spec (SPEC (f (#1 (dest_forall (concl th)))) th)
          handle HOL_ERR _ => REWRITE_RULE [] th
    in
      CONV_RULE (REWR_CONV IMP_F_EQ_F) (DISCH t (spec t_assumed))
    end
end

fun dest_bool_eq t = let
  val (l,r) = dest_eq t
  val _ = type_of l = bool orelse
          raise mk_HOL_ERR "dpll" "dest_bool_eq" "Eq not on bools"
in
  (l,r)
end
fun var_leaves acc t = let
  val (l,r) = dest_conj t handle HOL_ERR _ =>
              dest_disj t handle HOL_ERR _ =>
              dest_imp t handle HOL_ERR _ =>
              dest_bool_eq t
in
  var_leaves (var_leaves acc l) r
end handle HOL_ERR _ =>
           if type_of t <> bool then
             raise mk_HOL_ERR "dpll" "var_leaves" "Term not boolean"
           else if t = boolSyntax.T then acc
           else if t = boolSyntax.F then acc
           else HOLset.add(acc, t)

fun DPLL_TAUT tm =
    let val (univs,tm') = strip_forall tm
        val insts = HOLset.listItems (var_leaves empty_tmset tm')
        val vars = map (fn t => genvar bool) insts
        val theta = map2 (curry (op |->)) insts vars
        val tm'' = list_mk_forall (vars,subst theta tm')
    in
      EQT_INTRO (GENL univs
                      (SPECL insts (EQT_ELIM (DPLL_UNIV tm''))))
    end



(* implementation of DPLL ends *)

(* ----------------------------------------------------------------------
    Code below, due to John Harrison, generates tautologies stating that
    two different implementations of binary addition are equivalent
   ---------------------------------------------------------------------- *)

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

(* test them here:
time DPLL_UNIV example;
time tautLib.TAUT_PROVE example;
time HolSatLib.SAT_TAUT_PROVE (#2 (strip_forall example));
*)
