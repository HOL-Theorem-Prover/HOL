(* ========================================================================= *)
(* A STORE IN WHICH TO CACHE UNIT THEOREMS                                   *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load
 ["mlibUseful", "Mosml", "mlibTerm", "mlibThm", "mlibCanon", "mlibMatch"];
*)

(*
*)
structure mlibUnits :> mlibUnits =
struct

open mlibUseful mlibTerm mlibThm mlibMatch;

infix |-> ::> @> oo ##;

structure N = mlibLiteralnet; local open mlibLiteralnet in end;

val |<>| = mlibSubst.|<>|;
val formula_subst = mlibSubst.formula_subst;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions.                                                      *)
(* ------------------------------------------------------------------------- *)

fun lift_options f =
  let
    fun g res [] = SOME (rev res)
      | g res (x :: xs) = case f x of SOME y => g (y :: res) xs | NONE => NONE
  in
    g []
  end;

fun psym lit =
  let
    val (s, (x,y)) = (I ## dest_eq) (dest_literal lit)
    val () = assert (x <> y) (Error "psym: refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

(* ------------------------------------------------------------------------- *)
(* Operations on the raw unit cache.                                         *)
(* ------------------------------------------------------------------------- *)

type uns = thm N.literalnet;

val uempty : uns = N.empty {fifo = false};

fun usubsumes uns lit =
  List.find (fn t => can (match_literals (dest_unit t)) lit)
  (N.match uns lit);

fun ucontr uns th =
  let
    val th = FRESH_VARS th
    val lit = negate (dest_unit th)
    fun check t = (unify_literals |<>| (dest_unit t) lit, t)
  in
    case first (total check) (N.unify uns lit) of NONE => NONE
    | SOME (s,t) => SOME (RESOLVE (formula_subst s lit) (INST s t) (INST s th))
  end;

fun uadd th uns =
  let
    val l = dest_unit th
  in
    if Option.isSome (usubsumes uns l) then uns else
      (case total psym l of NONE => I | SOME l' => N.insert (l' |-> SYM l th))
      (N.insert (l |-> th) uns)
  end;

fun uprove uns =
  let
    fun pr lit =
      Option.map (fn th => INST (match_literals (dest_unit th) lit) th)
      (usubsumes uns lit)
  in
    lift_options pr
  end;

fun udemod uns =
  let
    fun demod (lit,th) =
      case uprove uns [negate lit] of NONE => th
      | SOME [dth] => RESOLVE lit th dth
      | SOME _ => raise Bug "unit_demod: corrupt"
  in
    fn th => foldl demod th (clause th)
  end;

(* ------------------------------------------------------------------------- *)
(* The user interface.                                                       *)
(* ------------------------------------------------------------------------- *)

type units = (thm,uns) sum;

val empty : units = INR uempty;

fun subsumes (INL th) = K (SOME th)
  | subsumes (INR uns) = usubsumes uns;

fun contr (INL th) _ = SOME th
  | contr (INR uns) th =
  if is_contradiction th then SOME th
  else Option.mapPartial (ucontr uns) (total UNIT_SQUASH th);

fun prove (INL th) lits = SOME (map (fn lit => CONTR lit th) lits)
  | prove (INR uns) lits = uprove uns lits;

fun demod (INL th) _ = th
  | demod (INR uns) th =
    let
      val th = udemod uns th
    in
      case first (fn lit => uprove uns [lit]) (clause th) of
        SOME [th] => th
      | _ => th
    end;

fun info ((INL _) : units) = "*"
  | info (INR uns) = int_to_string (N.size uns);

val pp_units = pp_map info pp_string;

(* Adding a theorem involves squashing it to a unit, if possible. *)

fun add _ (U as INL _) = U
  | add th (U as INR uns) =
  if is_contradiction th then INL th else
    case total UNIT_SQUASH th of NONE => U
    | SOME th => (case ucontr uns th of SOME c => INL c
                  | NONE => INR (uadd th uns));

val addl = C (foldl (uncurry add));

end
