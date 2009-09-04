(* ========================================================================= *)
(* FIRST-ORDER LOGIC CANONICALIZATION                                        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibUseful", "mlibTerm"];
*)

structure mlibCanon :> mlibCanon =
struct

open mlibUseful mlibTerm;

infixr |-> ::>

type subst        = mlibSubst.subst;
val |<>|          = mlibSubst.|<>|;
val op ::>        = mlibSubst.::>;
val term_subst    = mlibSubst.term_subst;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun sym lit =
  let
    val (x,y) = dest_eq lit
    val () = assert (x <> y) (Error "sym: refl")
  in
    mk_eq (y,x)
  end;

(* ------------------------------------------------------------------------- *)
(* Simplification.                                                           *)
(* ------------------------------------------------------------------------- *)

fun simplify1 (Not False)           = True
  | simplify1 (Not True)            = False
  | simplify1 (Not (Not fm))        = fm
  | simplify1 (And (False, q))      = False
  | simplify1 (And (p,     False))  = False
  | simplify1 (And (True,  q))      = q
  | simplify1 (And (p,     True))   = p
  | simplify1 (Or  (False, q))      = q
  | simplify1 (Or  (p,     False))  = p
  | simplify1 (Or  (True,  q))      = True
  | simplify1 (Or  (p,     True))   = True
  | simplify1 (Imp (False, q))      = True
  | simplify1 (Imp (True,  q))      = q
  | simplify1 (Imp (p,     True))   = True
  | simplify1 (Imp (Not p, False))  = p
  | simplify1 (Imp (p,     False))  = Not p
  | simplify1 (Iff (True,  q))      = q
  | simplify1 (Iff (p,     True))   = p
  | simplify1 (Iff (False, Not q))  = q
  | simplify1 (Iff (False, q))      = Not q
  | simplify1 (Iff (Not p, False))  = p
  | simplify1 (Iff (p,     False))  = Not p
  | simplify1 (fm as Forall (x, p)) = if mem x (FV p) then fm else p
  | simplify1 (fm as Exists (x, p)) = if mem x (FV p) then fm else p
  | simplify1 fm                    = fm;

fun simplify (Not    p)      = simplify1 (Not (simplify p))
  | simplify (And    (p, q)) = simplify1 (And (simplify p, simplify q))
  | simplify (Or     (p, q)) = simplify1 (Or  (simplify p, simplify q))
  | simplify (Imp    (p, q)) = simplify1 (Imp (simplify p, simplify q))
  | simplify (Iff    (p, q)) = simplify1 (Iff (simplify p, simplify q))
  | simplify (Forall (x, p)) = simplify1 (Forall (x, simplify p))
  | simplify (Exists (x, p)) = simplify1 (Exists (x, simplify p))
  | simplify fm              = fm;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

fun nnf (And (p,q))     = And (nnf p, nnf q)
  | nnf (Or (p,q))      = Or (nnf p, nnf q)
  | nnf (Imp (p,q))     = Or (nnf' p, nnf q)
  | nnf (Iff (p,q))     = Or (And (nnf p, nnf q), And (nnf' p, nnf' q))
  | nnf (Forall (x,p))  = Forall (x, nnf p)
  | nnf (Exists (x,p))  = Exists (x, nnf p)
  | nnf (Not x)         = nnf' x
  | nnf fm              = fm
and nnf' True           = False
  | nnf' False          = True
  | nnf' (And (p,q))    = Or (nnf' p, nnf' q)
  | nnf' (Or (p,q))     = And (nnf' p, nnf' q)
  | nnf' (Imp (p,q))    = And (nnf p, nnf' q)
  | nnf' (Iff (p,q))    = Or (And (nnf p, nnf' q), And (nnf' p, nnf q))
  | nnf' (Forall (x,p)) = Exists (x, nnf' p)
  | nnf' (Exists (x,p)) = Forall (x, nnf' p)
  | nnf' (Not x)        = nnf x
  | nnf' fm             = Not fm;

(* ------------------------------------------------------------------------- *)
(* Prenex normal form.                                                       *)
(* ------------------------------------------------------------------------- *)

fun pullquants fm =
  (case fm of
     And (Forall (x,p), Forall (y,q)) => pullquant_2 fm Forall And x y p q
   | Or (Exists (x,p), Exists (y,q)) => pullquant_2 fm Exists Or x y p q
   | And (Forall (x,p), q) => pullquant_l fm Forall And x p q
   | And (p, Forall (x,q)) => pullquant_r fm Forall And x p q
   | Or (Forall (x,p), q) => pullquant_l fm Forall Or x p q
   | Or (p, Forall (x,q)) => pullquant_r fm Forall Or x p q
   | And (Exists (x,p), q) => pullquant_l fm Exists And x p q
   | And (p, Exists (x,q)) => pullquant_r fm Exists And x p q
   | Or (Exists (x,p), q) => pullquant_l fm Exists Or x p q
   | Or (p, Exists (x,q)) => pullquant_r fm Exists Or x p q
   | _ => fm)
and pullquant_l fm Q C x p q =
  let
    val x' = variant x (FV fm)
  in
    Q (x', pullquants (C (formula_subst ((x |-> Var x') ::> |<>|) p, q)))
  end
and pullquant_r fm Q C x p q =
  let
    val x' = variant x (FV fm)
  in
    Q (x', pullquants (C (p, formula_subst ((x |-> Var x') ::> |<>|) q)))
  end
and pullquant_2 fm Q C x y p q =
  let
    val x' = variant x (FV fm)
  in
    Q (x', pullquants(C (formula_subst ((x |-> Var x') ::> |<>|) p,
                         formula_subst ((x |-> Var x') ::> |<>|) q)))
  end;

fun prenex (Forall (x,p)) = Forall (x, prenex p)
  | prenex (Exists (x,p)) = Exists (x, prenex p)
  | prenex (And (p,q)) = pullquants (And (prenex p, prenex q))
  | prenex (Or (p,q)) = pullquants (Or (prenex p, prenex q))
  | prenex fm = fm;

val pnf = prenex o nnf o simplify;

(* ------------------------------------------------------------------------- *)
(* Skolemization function.                                                   *)
(* ------------------------------------------------------------------------- *)

fun skolem avoid (Exists (y,p)) =
  let
    val xs = subtract (FV p) [y]
    val f = variant (if null xs then "c_" ^ y else "f_" ^ y) avoid
  in
    skolem avoid (formula_subst ((y |-> Fn (f, map Var xs)) ::> |<>|) p)
  end
  | skolem avoid (Forall (x,p)) = Forall (x, skolem avoid p)
  | skolem avoid (And (p,q)) = skolem2 avoid And p q
  | skolem avoid (Or (p,q)) = skolem2 avoid Or p q
  | skolem _ fm = fm
and skolem2 avoid C p q =
  let
    val p' = skolem avoid p
    val q' = skolem (union (function_names p') avoid) q
  in
    C (p',q')
  end;

fun skolemize fm = skolem (function_names fm) fm;

val full_skolemize = specialize o prenex o skolemize o nnf o simplify;

(* ------------------------------------------------------------------------- *)
(* A tautology filter for clauses.                                           *)
(* ------------------------------------------------------------------------- *)

fun tautologous lits =
  let
    val (pos,neg) = List.partition positive lits
    val pos = List.mapPartial (total sym) pos @ pos
    val neg = map negate neg
  in
    not (null (intersect pos neg))
  end;

(* ------------------------------------------------------------------------- *)
(* Conjunctive Normal Form.                                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun distrib s1 s2 = cartwith union s1 s2;

  fun push (Or (p,q))  = distrib (push p) (push q)
    | push (And (p,q)) = union (push p) (push q)
    | push fm = [[fm]];
in
  fun simpcnf True = []
    | simpcnf False = [[]]
    | simpcnf fm = List.filter (non tautologous) (push fm);
end;

val clausal =
  List.concat o map (simpcnf o specialize o prenex) o flatten_conj o
  skolemize o nnf o simplify;

val purecnf = list_mk_conj o map list_mk_disj o simpcnf;

val cnf = list_mk_conj o map list_mk_disj o clausal;

val is_clause = List.all is_literal o strip_disj o snd o strip_forall;

val is_cnf = List.all is_clause o strip_conj;

(* ------------------------------------------------------------------------- *)
(* Categorizing sets of clauses.                                             *)
(* ------------------------------------------------------------------------- *)

datatype prop = Propositional | Effectively_propositional | Non_propositional;
datatype equal = Non_equality | Equality | Pure_equality;
datatype horn = Trivial | Unit | Both_horn | Horn | Negative_horn | Non_horn;
type category = {prop : prop, equal : equal, horn : horn};

fun categorize_clauses fms =
  let
    val cls = map (strip_disj o snd o strip_forall) fms
    val fm = list_mk_conj fms
    val rels = relations fm
    val funs = functions fm

    val prop =
      if List.all (fn (_,n) => n = 0) rels then Propositional
      else if List.all (fn (_,n) => n = 0) funs then Effectively_propositional
      else Non_propositional

    val eq =
      if not (mem eq_rel rels) then Non_equality
      else if rels = [eq_rel] then Pure_equality
      else Equality

    val horn =
      if List.exists null cls then Trivial
      else if List.all (fn cl => length cl = 1) cls then Unit
      else
        let
          val posl = map (length o List.filter positive) cls
          val negl = map (length o List.filter negative) cls
          val pos = List.all (fn n => n <= 1) posl
          val neg = List.all (fn n => n <= 1) negl
        in
          case (pos,neg) of (true,true) => Both_horn
          | (true,false) => Horn
          | (false,true) => Negative_horn
          | (false,false) => Non_horn
        end
  in
    {prop = prop, equal = eq, horn = horn}
  end;

local
  fun prop Propositional = "propositional"
    | prop Effectively_propositional = "effectively propositional"
    | prop Non_propositional = "non-propositional";

  fun eq Non_equality = "non-equality"
    | eq Equality = "equality"
    | eq Pure_equality = "pure equality";

  fun horn Trivial = "trivial"
    | horn Unit = "unit"
    | horn Both_horn = "horn (and negative horn)"
    | horn Horn = "horn"
    | horn Negative_horn = "negative horn"
    | horn Non_horn = "non-horn";
in
  fun category_to_string {prop = p, equal = e, horn = h} =
    prop p ^ ", " ^ eq e ^ ", " ^ horn h;
end;

end
