(*****************************************************************************)
(* FILE          : solve_ineqs.sml                                           *)
(* DESCRIPTION   : Functions for solving inequalities.                       *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 7th August 1996                                           *)
(*****************************************************************************)

structure Solve_ineqs :> Solve_ineqs =
struct
  open Arbint HolKernel boolLib
       Int_extra Arith_cons Term_coeffs RJBConv Theorems Thm_convs
       Norm_arith Norm_ineqs reduceLib;

val << = String.<
infix << THENC ##;

val num_CONV = Num_conv.num_CONV;
val MATCH_MP = Drule.MATCH_MP;

fun failwith function = raise HOL_ERR{origin_structure = "Solve_ineqs",
                                      origin_function = function,
                                      message = ""};


(*===========================================================================*)
(* Multiplying normalized arithmetic expressions by a constant               *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* CONST_TIMES_ARITH_CONV : conv                                             *)
(*                                                                           *)
(* Converts the product of a constant and a normalized arithmetic expression *)
(* to a new normalized arithmetic expression.                                *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    CONST_TIMES_ARITH_CONV `3 * (1 + (3 * x) + (2 * y))`  --->             *)
(*    |- 3 * (1 + ((3 * x) + (2 * y))) = 3 + ((9 * x) + (6 * y))             *)
(*---------------------------------------------------------------------------*)

fun CONST_TIMES_ARITH_CONV tm =
 (let fun CONST_TIMES_VARS_CONV tm =
         if (is_mult (arg2 tm))
         then (MULT_ASSOC_CONV THENC
               (RATOR_CONV (RAND_CONV FAST_MULT_CONV))) tm
         else (LEFT_ADD_DISTRIB_CONV THENC
               (RATOR_CONV
                 (RAND_CONV
                   (MULT_ASSOC_CONV THENC
                    (RATOR_CONV (RAND_CONV FAST_MULT_CONV))))) THENC
               (RAND_CONV CONST_TIMES_VARS_CONV)) tm
      val tm' = arg2 tm
  in  if (is_num_const tm') then FAST_MULT_CONV tm
      else if (is_mult tm') then
         (MULT_ASSOC_CONV THENC
          (RATOR_CONV (RAND_CONV FAST_MULT_CONV))) tm
      else if (is_num_const (arg1 tm')) then
         (LEFT_ADD_DISTRIB_CONV THENC
          (RATOR_CONV (RAND_CONV FAST_MULT_CONV)) THENC
          (RAND_CONV CONST_TIMES_VARS_CONV)) tm
      else CONST_TIMES_VARS_CONV tm
  end
 ) handle (HOL_ERR _) => failwith "CONST_TIMES_ARITH_CONV";

(*---------------------------------------------------------------------------*)
(* MULT_LEQ_BY_CONST_CONV : term -> conv                                     *)
(*                                                                           *)
(* Multiplies both sides of a normalized inequality by a non-zero constant.  *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    MULT_LEQ_BY_CONST_CONV `3` `(1 + (3 * x) + (2 * y)) <= (3 * z)`  --->  *)
(*    |- (1 + ((3 * x) + (2 * y))) <= (3 * z) =                              *)
(*       (3 + ((9 * x) + (6 * y))) <= (9 * z)                                *)
(*---------------------------------------------------------------------------*)

fun MULT_LEQ_BY_CONST_CONV constant tm =
 (let val (tm1,tm2) = dest_leq tm
      and n = int_of_term constant
  in
  if (n = zero) then failwith "fail"
  else if (n = one) then ALL_CONV tm
  else let val constant' = term_of_int (n - one)
           val th = SYM (num_CONV constant)
           val th1 = SPEC constant' (SPEC tm2 (SPEC tm1 MULT_LEQ_SUC))
           val th2 =
              ((RATOR_CONV
                 (RAND_CONV (RATOR_CONV (RAND_CONV (fn _ => th))))) THENC
               (RAND_CONV (RATOR_CONV (RAND_CONV (fn _ => th)))))
              (rhs (concl th1))
       in  ((fn _ => TRANS th1 th2) THENC
            (ARGS_CONV CONST_TIMES_ARITH_CONV)) tm
       end
  end
 ) handle (HOL_ERR _) => failwith "MULT_LEQ_BY_CONST_CONV";

(*===========================================================================*)
(* Solving inequalities between constants                                    *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* LEQ_CONV : conv                                                           *)
(*                                                                           *)
(* Given a term of the form `a <= b` where a and b are constants, returns    *)
(* the theorem |- (a <= b) = T or the theorem |- (a <= b) = F depending on   *)
(* the values of a and b.                                                    *)
(*                                                                           *)
(* Optimized for when one or both of the arguments is zero.                  *)
(*---------------------------------------------------------------------------*)

val LEQ_CONV = reduceLib.LE_CONV

(*===========================================================================*)
(* Eliminating variables from sets of inequalities                           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* WEIGHTED_SUM :                                                            *)
(*    string ->                                                              *)
(*    ((int * (string * int) list) * (int * (string * int) list)) ->         *)
(*    ((int * (string * int) list) * (unit -> thm))                          *)
(*                                                                           *)
(* Function to eliminate a specified variable from two inequalities by       *)
(* forming their weighted sum. The inequalities must be given as bindings.   *)
(* The result is a pair. The first component is a binding representing the   *)
(* combined inequality, and the second component is a function. When applied *)
(* to ():unit this function returns a theorem which states that under the    *)
(* assumption that the two original inequalities are true, then the          *)
(* resultant inequality is true.                                             *)
(*                                                                           *)
(* The variable to be eliminated should be on the right-hand side of the     *)
(* first inequality, and on the left-hand side of the second.                *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    WEIGHTED_SUM `y` ((1,[(`x`, -3);(`y`, 1)]), (3,[(`x`, -3);(`y`, -1)])) *)
(*    --->                                                                   *)
(*    ((4, [(`x`, -6)]), -)                                                  *)
(*                                                                           *)
(*    snd it ()  --->                                                        *)
(*    (3 * x) <= (1 + (1 * y)), ((3 * x) + (1 * y)) <= 3 |- (6 * x) <= 4     *)
(*---------------------------------------------------------------------------*)

fun WEIGHTED_SUM name (coeffs1,coeffs2) =
 (let val coeff1 = assoc name (snd coeffs1)
      and coeff2 = zero - (assoc name (snd coeffs2))
      val mult = lcm (coeff1,coeff2)
      val mult1 = mult div coeff1
      and mult2 = mult div coeff2
      val coeffs1' =
         ((fn n => n * mult1) ## (map (fn (s,n) => (s,n * mult1)))) coeffs1
      and coeffs2' =
         ((fn n => n * mult2) ## (map (fn (s,n) => (s,n * mult2)))) coeffs2
      val (adds1,adds2) = diff_of_coeffs (coeffs1',coeffs2')
      val coeffs1'' = merge_coeffs adds1 (lhs_coeffs coeffs1')
      and coeffs2'' = merge_coeffs adds2 (rhs_coeffs coeffs2')
      val new_coeffs = merge_coeffs (negate_coeffs coeffs1'') coeffs2''
      fun thf () =
         let val th1 =
                RULE_OF_CONV
                ((if (mult1 = one)
                  then ALL_CONV
                  else MULT_LEQ_BY_CONST_CONV (term_of_int mult1)) THENC
                 (if (adds1 = (zero,[]))
                  then ALL_CONV
                  else (ADD_COEFFS_TO_LEQ_CONV adds1) THENC
                       (RAND_CONV (SORT_AND_GATHER_CONV THENC
                                    NORM_ZERO_AND_ONE_CONV))))
                (build_leq coeffs1)
             and th2 =
                RULE_OF_CONV
                ((if (mult2 = one)
                  then ALL_CONV
                  else MULT_LEQ_BY_CONST_CONV (term_of_int mult2)) THENC
                 (if (adds2 = (zero,[]))
                  then ALL_CONV
                  else (ADD_COEFFS_TO_LEQ_CONV adds2) THENC
                       (RATOR_CONV
                         (RAND_CONV (SORT_AND_GATHER_CONV THENC
                                      NORM_ZERO_AND_ONE_CONV)))))
                (build_leq coeffs2)
             val th = CONJ (UNDISCH (fst (EQ_IMP_RULE th1)))
                           (UNDISCH (fst (EQ_IMP_RULE th2)))
             val th1conv =
                if (adds1 = (zero,[]))
                then ALL_CONV
                else RATOR_CONV
                      (RAND_CONV
                        (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV))
             and th2conv =
                if (adds2 = (zero,[]))
                then ALL_CONV
                else RAND_CONV
                      (SORT_AND_GATHER_CONV THENC NORM_ZERO_AND_ONE_CONV)
         in  CONV_RULE (th1conv THENC th2conv THENC LESS_OR_EQ_GATHER_CONV)
                        (MATCH_MP LESS_EQ_TRANSIT th)
         end
  in  (new_coeffs,thf)
  end
 ) handle (HOL_ERR _) => failwith "WEIGHTED_SUM";

(*---------------------------------------------------------------------------*)
(* var_to_elim : ('a * (string * int) list) list -> string                   *)
(*                                                                           *)
(* Given a list of inequalities (as bindings), this function determines      *)
(* which variable to eliminate. Such a variable must occur in two            *)
(* inequalites on different sides. The variable chosen is the one that gives *)
(* rise to the least number of pairings.                                     *)
(*---------------------------------------------------------------------------*)

fun var_to_elim coeffsl =
 (let fun var_to_elim' bind =
         if (null bind)
         then ([],[])
         else let val (name,coeff) = hd bind
                  and (occsl,occsr) = var_to_elim' (tl bind)
              in  if (coeff < zero) then ((name, one)::occsl,occsr)
                  else if (coeff > zero) then (occsl,(name, one)::occsr)
                  else (occsl,occsr)
              end
      fun min_increase bind1 bind2 =
         let val (name1:string,num1:int) = hd bind1
             and (name2,num2) = hd bind2
         in  if (name1 = name2) then
                (let val increase = (num1 * num2) - (num1 + num2)
                 in  (let val (name,min) = min_increase (tl bind1) (tl bind2)
                      in  if (min < increase)
                          then (name,min)
                          else (name1,increase)
                      end)
                     handle _ => (name1,increase)
                 end)
             else if (name1 << name2) then min_increase (tl bind1) bind2
             else min_increase bind1 (tl bind2)
         end
      val merge =
         end_itlist (fn b1 => fn b2 => snd (merge_coeffs (zero,b1) (zero,b2)))
      val occs = map (var_to_elim' o snd) coeffsl
      val (occsl,occsr) = (merge ## merge) (split occs)
  in  fst (min_increase occsl occsr)
  end
 ) handle _ => failwith "var_to_elim";

(*---------------------------------------------------------------------------*)
(* VAR_ELIM : (int * (string * int) list) list -> (int list * (unit -> thm)) *)
(*                                                                           *)
(* Given a list of inequalities represented by bindings, this function       *)
(* returns a `lazy' theorem with false (actually an inequality between       *)
(* constants that can immediately be shown to be false) as its conclusion,   *)
(* and some of the inequalities as assumptions. A list of numbers is also    *)
(* returned. These are the positions in the argument list of the             *)
(* inequalities that are assumptions of the theorem. The function fails if   *)
(* the set of inequalities is satisfiable.                                   *)
(*                                                                           *)
(* The function assumes that none of the inequalities given are false, that  *)
(* is they either contain variables, or evaluate to true. Those that are     *)
(* true are filtered out. The function then determines which variable to     *)
(* eliminate and splits the remaining inequalities into three sets: ones in  *)
(* which the variable occurs on the left-hand side, ones in which the        *)
(* variable occurs on the right, and ones in which the variable does not     *)
(* occur.                                                                    *)
(*                                                                           *)
(* Pairings of the `right' and `left' inequalities are then made, and the    *)
(* weighted sum of each is determined, except that as soon as a pairing      *)
(* yields false, the process is terminated. It may well be the case that no  *)
(* pairing gives false. In this case, the new inequalities are added to the  *)
(* inequalities that did not contain the variable, and a recursive call is   *)
(* made.                                                                     *)
(*                                                                           *)
(* The list of numbers from the recursive call (representing assumptions) is *)
(* split into two: those that point to inequalities that were produced by    *)
(* doing weighted sums, and those that were not. The latter can be traced    *)
(* back so that their positions in the original argument list can be         *)
(* returned. The other inequalities have to be discharged from the theorem   *)
(* using the theorems proved by performing weighted sums. Each assumption    *)
(* thus gives rise to two new assumptions and the conclusion remains false.  *)
(* The positions of the two new assumptions in the original argument list    *)
(* are added to the list to be returned. Duplicates are removed from this    *)
(* list before returning it.                                                 *)
(*---------------------------------------------------------------------------*)

fun VAR_ELIM coeffsl =
 let fun upto from to =
        if (from > to)
        then []
        else from::(upto (from + one) to)
     fun left_ineqs var icoeffsl =
        let fun left_ineq icoeffs =
               not (null (filter
                          (fn (name,coeff) => (name = var) andalso (coeff < zero))
                          (snd (snd icoeffs))))
        in  filter left_ineq icoeffsl
        end
     fun right_ineqs var icoeffsl =
        let fun right_ineq icoeffs =
               not (null (filter
                          (fn (name,coeff) => (name = var) andalso (coeff > zero))
                          (snd (snd icoeffs))))
        in  filter right_ineq icoeffsl
        end
     fun no_var_ineqs var icoeffsl =
        let fun no_var_ineq icoeffs =
               null
                (filter
                 (fn (name,coeff) => (name = var) andalso (not (coeff = zero)))
                 (snd (snd icoeffs)))
        in  filter no_var_ineq icoeffsl
        end
     fun pair_ineqs (ricoeffs,licoeffs) =
        let fun pair (ricoeffs,licoeffs) =
               if (null ricoeffs)
               then []
               else (map (fn l => (hd ricoeffs,l)) licoeffs)::
                    (pair (tl ricoeffs,licoeffs))
        in  flatten (pair (ricoeffs,licoeffs))
        end
     fun weighted_sums var pairs =
        if (null pairs)
        then (false,[])
        else let val (success,rest) = weighted_sums var (tl pairs)
             in  if success
                 then (success,rest)
                 else let val ((lindex,lcoeffs),(rindex,rcoeffs)) = hd pairs
                          val ((const,bind),f) =
                                 WEIGHTED_SUM var (lcoeffs,rcoeffs)
                      in  if ((null bind) andalso (const < zero))
                          then (true,[((lindex,rindex),((const,bind),f))])
                          else (false,((lindex,rindex),((const,bind),f))::rest)
                      end
             end
     fun chain_assums ineqs thf indexl =
       if (null indexl) then ([],thf)
       else let
         val (prev_indexl,thf') = chain_assums ineqs thf (tl indexl)
         and ((lindex,rindex),(coeffs,f)) = el (toInt (hd indexl)) ineqs
       in  (lindex::rindex::prev_indexl,
            fn () => PROVE_HYP (f ()) (thf' ()))
       end
 in
 (let val icoeffsl = combine (upto one (fromInt (length coeffsl)), coeffsl)
      val icoeffsl' = filter (fn (i,(const,bind)) => not (null bind)) icoeffsl
      val var = var_to_elim (map snd icoeffsl')
      val ricoeffs = right_ineqs var icoeffsl'
      and licoeffs = left_ineqs var icoeffsl'
      and nicoeffs = no_var_ineqs var icoeffsl'
      val pairs = pair_ineqs (ricoeffs,licoeffs)
      val (success,new_ineqs) = weighted_sums var pairs
  in  if success
      then let val [((lindex,rindex),(coeffs,thf))] = new_ineqs
           in  ([lindex,rindex],thf)
           end
      else let val n = fromInt (length new_ineqs)
               and new_coeffs =
                  (map (fst o snd) new_ineqs) @ (map snd nicoeffs)
               val (indexl,thf) = VAR_ELIM new_coeffs
               val (prev_indexl,these_indexl) =
                  Lib.partition (fn i => i > n) indexl
               val prev_indexl' =
                  map (fn i => fst (el (toInt (i - n)) nicoeffs)) prev_indexl
               val (these_indexl',thf') =
                  chain_assums new_ineqs thf these_indexl
           in  (Lib.mk_set (these_indexl' @ prev_indexl'),thf')
           end
  end
 ) handle _ => failwith "VAR_ELIM"
 end;

end
