(* ========================================================================= *)
(* SUBSTITUTIONS ON FIRST-ORDER TERMS AND FORMULAS                           *)
(* Created by Joe Hurd, June 2002                                            *)
(* ========================================================================= *)

structure mlibSubst :> mlibSubst =
struct

open mlibUseful mlibTerm;

infixr 8 ++;
infixr 7 >>;
infixr 6 ||;
infixr |-> ::> @> oo ##;

structure M = Binarymap; local open Binarymap in end;

(* ------------------------------------------------------------------------- *)
(* The underlying representation.                                            *)
(* ------------------------------------------------------------------------- *)

datatype subst = Subst of (string, term) M.dict;

(* ------------------------------------------------------------------------- *)
(* Operations.                                                               *)
(* ------------------------------------------------------------------------- *)

val |<>| = Subst (M.mkDict String.compare);

fun (a |-> b) ::> (Subst d) = Subst (M.insert (d, a, b));

fun (Subst sub1) @> (Subst sub2) =
  Subst (M.foldl (fn (a, b, d) => M.insert (d, a, b)) sub2 sub1);

fun null (Subst s) = M.numItems s = 0;

fun find_redex r (Subst d) = M.peek (d, r);

local
  fun tm_subst sub (tm as Var x) =
    (case find_redex x sub of NONE => tm | SOME tm' => tm')
    | tm_subst sub (Fn (f, args)) = Fn (f, map (tm_subst sub) args);

  fun fm_subst _   False            = False
    | fm_subst _   True             = True
    | fm_subst sub (Atom (p, args)) = Atom (p, map (tm_subst sub) args)
    | fm_subst sub (Not p         ) = Not (fm_subst sub p)
    | fm_subst sub (And (p, q)    ) = And (fm_subst sub p, fm_subst sub q)
    | fm_subst sub (Or (p, q)     ) = Or (fm_subst sub p, fm_subst sub q)
    | fm_subst sub (Imp (p, q)    ) = Imp (fm_subst sub p, fm_subst sub q)
    | fm_subst sub (Iff (p, q)    ) = Iff (fm_subst sub p, fm_subst sub q)
    | fm_subst sub (Forall (x, p) ) = fm_substq sub Forall (x, p)
    | fm_subst sub (Exists (x, p) ) = fm_substq sub Exists (x, p)
  and fm_substq sub Q (x, p) =
    let val x' = variant x (FV (fm_subst ((x |-> Var x) ::> sub) p))
    in Q (x', fm_subst ((x |-> Var x') ::> sub) p)
    end;
in
  fun term_subst    env tm = if null env then tm else tm_subst env tm;
  fun formula_subst env fm = if null env then fm else fm_subst env fm;
end;
  
fun norm (sub as Subst dict) =
  let
    fun check (a, b, (c, d)) =
      if Var a = b then (true, fst (M.remove (d, a))) else (c, d)
    val (removed, dict') = M.foldl check (false, dict) dict
  in
    if removed then Subst dict' else sub
  end;

fun to_maplets (Subst s) = map (op|->) (M.listItems s);

fun from_maplets ms = foldl (op ::>) |<>| (rev ms);

fun restrict vs =
  from_maplets o List.filter (fn (a |-> _) => mem a vs) o to_maplets;

(* Note: this just doesn't work with cyclic substitutions! *)
fun refine (Subst sub1) sub2 =
  let
    fun f ((a, b), s) =
      let val b' = term_subst sub2 b
      in if Var a = b' then s else (a |-> b') ::> s
      end
  in
    foldl f sub2 (M.listItems sub1)
  end;

local
  exception QF
  fun rs (v, Var w, l) = if mem w l then raise QF else w :: l
    | rs (_, Fn _, _) = raise QF
in
  fun is_renaming (Subst sub) = (M.foldl rs [] sub; true) handle QF => false;
end;

val pp_subst =
  pp_map to_maplets
  (fn pp =>
   (fn [] => pp_string pp "|<>|"
     | l => pp_list (pp_maplet pp_string pp_term) pp l));

end