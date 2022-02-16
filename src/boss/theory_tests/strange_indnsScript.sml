open HolKernel Parse boolLib bossLib;

val _ = new_theory "strange_indns";

Datatype:
  wtree = Nd wtree other | Lf num 'a ;
  other = OLf (num -> bool) | ONd num wtree wtree
End

Definition wsz_def:
  wsz (Nd w _) = 1 + wsz w /\
  wsz (Lf _ _) = 1
End

fun die t =
  (TextIO.output(TextIO.stdOut, "Failed on " ^ term_to_string t ^ "\n");
   TextIO.flushOut TextIO.stdOut;
   OS.Process.exit OS.Process.failure)
fun check t = case (DefnBase.lookup_userdef t, DefnBase.lookup_indn t) of
          (SOME d, SOME i) => (d,i)
        | _ => die t
val _ = check “wsz”

(* for reference: the use of the unit literal moves us out of what
    new_recursive_definition
   can handle, and so TFL takes over and proves the induction principle
   itself
*)
Definition wsz'_def:
  wsz' () (Nd w _) = 1 + wsz' () w /\
  wsz' _ _ = 1
End

val _ = check “wsz'”

Definition tradmrec_def:
  tradmrec2 n (OLf s) = n + CARD s /\
  tradmrec2 m (ONd n w1 w2) = tradmrec1 w1 + tradmrec1 w2 - n + m /\
  tradmrec1 (Nd w t) = tradmrec1 w + tradmrec2 0 t + 1 /\
  tradmrec1 (Lf n _) = n
End

val _ = check “tradmrec1”
val _ = check “tradmrec2”


Definition inst_single:
  wis (Nd w t) = 1 + wis w /\
  wis (Lf m n) = m + n
End

val _ = check “wis”

Definition inst_double:
  wis2 n (OLf s) = n + CARD s /\
  wis2 n (ONd m w1 w2) = wis1 (m * n) w1 n + wis1 (m DIV n) w2 m /\
  wis1 x (Nd w t) y = wis1 x w y + wis2 x t /\
  wis1 x (Lf a b) y = (x + a) * (b + y)
End

val _ = check “wis1”
val _ = check “wis2”;


Datatype:
  sterm = V num | SFn num (sterm list)
End

Definition fvs:
  fvs (V n) = {V n} /\
  fvs (SFn _ ts) = fvsl ts /\
  fvsl [] = {} /\
  fvsl (t::ts) = fvs t UNION fvsl ts
End

val _ = check “fvs”
val _ = check “fvsl”

val _ = export_theory();
