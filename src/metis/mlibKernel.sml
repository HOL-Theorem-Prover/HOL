(* ========================================================================= *)
(* A LCF-STYLE LOGICAL KERNEL FOR FIRST-ORDER CLAUSES                        *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

structure mlibKernel :> mlibKernel =
struct

open mlibUseful mlibTerm;

infixr |-> ::> oo;

type subst        = mlibSubst.subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* An ABSTRACT type for theorems.                                            *)
(* ------------------------------------------------------------------------- *)

datatype inference = Axiom | Refl | Assume | Inst | Factor | Resolve | Equality;

datatype thm = Thm of formula list * (inference * thm list);

(* ------------------------------------------------------------------------- *)
(* Destruction of theorems is fine.                                          *)
(* ------------------------------------------------------------------------- *)

fun dest_thm (Thm th) = th;

val clause = fst o dest_thm;

(* ------------------------------------------------------------------------- *)
(* But creation is only allowed by the primitive rules of inference.         *)
(* ------------------------------------------------------------------------- *)

fun AXIOM cl =
  if List.all is_literal cl then Thm (cl, (Axiom, []))
  else raise ERR "AXIOM" "argument not a list of literals";

fun REFL tm = Thm ([Atom ("=", [tm, tm])], (Refl, []));

fun ASSUME fm =
  if is_literal fm then Thm ([fm, negate fm], (Assume, []))
  else raise ERR "ASSUME" "argument not a literal";

fun INST env th =
  let val cl = map (formula_subst env) (clause th)
  in if cl = clause th then th else Thm (cl, (Inst, [th]))
  end;

fun FACTOR th =
  let val cl = rev (setify (clause th))
  in if cl = clause th then th else Thm (cl, (Factor, [th]))
  end;

fun RESOLVE fm th1 th2 =
  let
    val cl1  = clause th1
    val cl1' = List.filter (not o equal fm) cl1
    val cl2  = clause th2
    val cl2' = List.filter (not o equal (negate fm)) cl2
    val ()   =
      assert (cl1 <> cl1' orelse cl2 <> cl2')
      (ERR "RESOLVE" "resolvant does not feature in either clause")
  in
    Thm (cl1' @ cl2', (Resolve, [th1, th2]))
  end;

fun EQUALITY fm p res lr th =
  let
    val eq_lit =
      let
        val red = literal_subterm p fm
      in
        Not (Atom ("=", if lr then [red, res] else [res, red]))
      end
    val other_lits =
      let
        val l = clause th
      in
        case index (equal fm) l of NONE
          => raise ERR "EQUALITY" "literal does not occur in clause"
        | SOME n => update_nth (literal_rewrite (p |-> res)) n l
      end
  in
    Thm (eq_lit :: other_lits, (Equality, [th]))
  end;

end
