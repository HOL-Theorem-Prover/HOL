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

structure N = mlibLiteralnet; local open mlibLiteralnet in end;

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
    val () = assert (x <> y) (ERR "psym" "refl")
  in
    mk_literal (s, mk_eq (y,x))
  end;

(* ------------------------------------------------------------------------- *)
(* Operations on the raw unit cache.                                         *)
(* ------------------------------------------------------------------------- *)

type uns = thm N.literalnet;

fun uempty () : uns = N.empty ();

fun usubsumes uns lit =
  List.find (fn t => can (match_literals (dest_unit t)) lit)
  (rev (N.match uns lit));

fun uadd th uns =
  let
    val l = dest_unit th
  in
    if Option.isSome (usubsumes uns l) then uns
    else
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

fun empty () : units = INR (uempty ());

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
