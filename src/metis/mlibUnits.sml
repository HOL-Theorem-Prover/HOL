(* ========================================================================= *)
(* A STORE IN WHICH TO CACHE UNIT THEOREMS                                   *)
(* Created by Joe Hurd, November 2001                                        *)
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

structure N = mlibLiteralNet; local open mlibLiteralNet in end;

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

(* ------------------------------------------------------------------------- *)
(* Operations on the raw unit cache.                                         *)
(* ------------------------------------------------------------------------- *)

type uns = thm N.literal_map;

val uempty : uns = N.empty;

fun uadd th uns = N.insert (dest_unit th |-> th) uns;

fun usubsumes uns lit =
  List.find (can (C match_literals lit) o dest_unit)
  (rev (N.match uns lit));

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
    fun demod (lit, th) =
      case uprove uns [negate lit] of NONE => th
      | SOME [dth] => RESOLVE lit th dth
      | SOME _ => raise BUG "unit_demod" "corrupt"
  in
    fn th => foldl demod th (clause th)
  end;

(* ------------------------------------------------------------------------- *)
(* The user interface.                                                       *)
(* ------------------------------------------------------------------------- *)

type units = (thm, uns) sum;

val empty = INR uempty;

fun subsumes (INL th) = K (SOME th)
  | subsumes (INR uns) = usubsumes uns;

fun prove (INL th) = SOME o map (fn False => th | lit => CONTR lit th)
  | prove (INR uns) = uprove uns;

fun demod (INL th) = K th
  | demod (INR uns) = udemod uns;

fun info ((INL _) : units) = "*"
  | info (INR uns) = int_to_string (N.size uns);

val pp_units = pp_map info pp_string;

(* Adding a theorem involves squashing it to a unit, if possible. *)

fun add _ (U as INL _) = U
  | add th (U as INR uns) =
  if List.exists (Option.isSome o usubsumes uns) (clause th) then U
  else
    let
      val th = udemod uns th
    in
      if is_contradiction th then INL th
      else case total UNIT_SQUASH th of NONE => U | SOME th => INR (uadd th uns)
    end;

val addl = C (foldl (uncurry add));

end