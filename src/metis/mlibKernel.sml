(* ========================================================================= *)
(* A LCF-STYLE LOGICAL KERNEL FOR FIRST-ORDER CLAUSES                        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
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

datatype thm = mlibThm of formula list * (inference * thm list);

(* ------------------------------------------------------------------------- *)
(* Destruction of theorems is fine.                                          *)
(* ------------------------------------------------------------------------- *)

fun dest_thm (mlibThm th) = th;

val clause = fst o dest_thm;

(* ------------------------------------------------------------------------- *)
(* But creation is only allowed by the primitive rules of inference.         *)
(* ------------------------------------------------------------------------- *)

fun AXIOM cl =
  if List.all is_literal cl then mlibThm (cl, (Axiom, []))
  else raise Error "AXIOM: argument not a list of literals";

fun REFL tm = mlibThm ([mk_eq (tm,tm)], (Refl, []));

fun ASSUME fm =
  if is_literal fm then mlibThm ([fm, negate fm], (Assume, []))
  else raise Error "ASSUME: argument not a literal";

fun INST env (th as mlibThm (cl, pr)) =
  let
    val cl' = map (formula_subst env) cl
  in
    if cl' = cl then th else
      case pr of (Inst, [th'])
        => if cl' = clause th' then th' else mlibThm (cl', (Inst, [th']))
      | _ => mlibThm (cl', (Inst, [th]))
  end;

fun FACTOR th =
  let val cl = rev (setify (clause th))
  in if cl = clause th then th else mlibThm (cl, (Factor, [th]))
  end;

fun RESOLVE fm th1 th2 =
  let
    val cl1  = clause th1
    val cl1' = List.filter (not o equal fm) cl1
    val cl2  = clause th2
    val cl2' = List.filter (not o equal (negate fm)) cl2
    val cl = cl1' @ cl2'
  in
    if cl = cl1 then th1
    else if cl = cl2 then th2
    else mlibThm (cl, (Resolve, [th1, th2]))
  end;

fun EQUALITY lit p r lr th =
  let
    val l = literal_subterm p lit
    val eq_lit = Not (mk_eq (if lr then (l,r) else (r,l)))
    val th_lits = clause th
    val other_lits =
      case index (equal lit) th_lits of
        NONE => literal_rewrite (p |-> r) lit :: th_lits
      | SOME n => update_nth (literal_rewrite (p |-> r)) n th_lits
  in
    mlibThm (eq_lit :: other_lits, (Equality, [th]))
  end;

end
