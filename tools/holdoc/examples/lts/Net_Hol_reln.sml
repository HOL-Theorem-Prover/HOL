structure Net_Hol_reln :> Net_Hol_reln =
struct

open Abbrev
open HolKernel boolLib

(* in abstract syntax term a, replace all occurrences of
     q <== p
   with
     p ==> q
*)
fun transfrom_revimp a = let
  open Absyn
  val t = transfrom_revimp
in
  case a of
    APP(l1, APP(l2, IDENT(l3, "revimp"), p), q) =>
      APP(l2, APP(l1, IDENT(l3, "==>"), t q), t p)
      (* locations are still wrong!  Should use Absyn.locn_of_absyn to recreate *)
  | APP(loc, f,x) => APP (loc, t f, t x)
  | LAM(loc, vs, x) => LAM(loc, vs, t x)
  | TYPED(loc, x, pty) => TYPED(loc, t x, pty)
  | _ => a
end

fun Net_Hol_reln q = let
  open IndDefLib
  val a0 = Parse.Absyn q
  val a = transfrom_revimp a0
  val tm = term_of_absyn a
in
  prim_Hol_reln InductiveDefinition.bool_monoset tm
end;




end (* struct *)
