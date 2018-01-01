(* =========================================================================  *)
(* FILE          : hhsFeature.sml                                             *)
(* DESCRIPTION   : Transforming a prefix operator into an infix one           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsInfix :> hhsInfix =
struct

infix 0 hhs_infixl0_open hhs_infixl0_close
infix 1 hhs_infixl1_open hhs_infixl1_close
infix 2 hhs_infixl2_open hhs_infixl2_close
infix 3 hhs_infixl3_open hhs_infixl3_close
infix 4 hhs_infixl4_open hhs_infixl4_close
infix 5 hhs_infixl5_open hhs_infixl5_close
infix 6 hhs_infixl6_open hhs_infixl6_close
infix 7 hhs_infixl7_open hhs_infixl7_close
infix 8 hhs_infixl8_open hhs_infixl8_close
infix 9 hhs_infixl9_open hhs_infixl9_close

infixr 0 hhs_infixr0_open hhs_infixr0_close
infixr 1 hhs_infixr1_open hhs_infixr1_close
infixr 2 hhs_infixr2_open hhs_infixr2_close
infixr 3 hhs_infixr3_open hhs_infixr3_close
infixr 4 hhs_infixr4_open hhs_infixr4_close
infixr 5 hhs_infixr5_open hhs_infixr5_close
infixr 6 hhs_infixr6_open hhs_infixr6_close
infixr 7 hhs_infixr7_open hhs_infixr7_close
infixr 8 hhs_infixr8_open hhs_infixr8_close
infixr 9 hhs_infixr9_open hhs_infixr9_close

fun a hhs_infixl0_open f = fn x => f (a,x)  
fun g hhs_infixl0_close b = g b

fun f hhs_infixr0_close b = fn x => f (x,b)
fun a hhs_infixr0_open g = g a

val op hhs_infixl1_open = op hhs_infixl0_open
val op hhs_infixl2_open = op hhs_infixl0_open
val op hhs_infixl3_open = op hhs_infixl0_open
val op hhs_infixl4_open = op hhs_infixl0_open
val op hhs_infixl5_open = op hhs_infixl0_open
val op hhs_infixl6_open = op hhs_infixl0_open
val op hhs_infixl7_open = op hhs_infixl0_open
val op hhs_infixl8_open = op hhs_infixl0_open
val op hhs_infixl9_open = op hhs_infixl0_open

val op hhs_infixl1_close = op hhs_infixl0_close
val op hhs_infixl2_close = op hhs_infixl0_close
val op hhs_infixl3_close = op hhs_infixl0_close
val op hhs_infixl4_close = op hhs_infixl0_close
val op hhs_infixl5_close = op hhs_infixl0_close
val op hhs_infixl6_close = op hhs_infixl0_close
val op hhs_infixl7_close = op hhs_infixl0_close
val op hhs_infixl8_close = op hhs_infixl0_close
val op hhs_infixl9_close = op hhs_infixl0_close

val op hhs_infixr1_open = op hhs_infixr0_open
val op hhs_infixr2_open = op hhs_infixr0_open
val op hhs_infixr3_open = op hhs_infixr0_open
val op hhs_infixr4_open = op hhs_infixr0_open
val op hhs_infixr5_open = op hhs_infixr0_open
val op hhs_infixr6_open = op hhs_infixr0_open
val op hhs_infixr7_open = op hhs_infixr0_open
val op hhs_infixr8_open = op hhs_infixr0_open
val op hhs_infixr9_open = op hhs_infixr0_open

val op hhs_infixr1_close = op hhs_infixr0_close
val op hhs_infixr2_close = op hhs_infixr0_close
val op hhs_infixr3_close = op hhs_infixr0_close
val op hhs_infixr4_close = op hhs_infixr0_close
val op hhs_infixr5_close = op hhs_infixr0_close
val op hhs_infixr6_close = op hhs_infixr0_close
val op hhs_infixr7_close = op hhs_infixr0_close
val op hhs_infixr8_close = op hhs_infixr0_close
val op hhs_infixr9_close = op hhs_infixr0_close

datatype infixity_t = Inf_left of int | Inf_right of int

fun infix_pair infixity = case infixity of
    Inf_left n => 
    ("hhs_infixl" ^ Int.toString n ^ "_open",
     "hhs_infixl" ^ Int.toString n ^ "_close")
  | Inf_right n =>
    ("hhs_infixr" ^ Int.toString n ^ "_open",
     "hhs_infixr" ^ Int.toString n ^ "_close")

(*----------------------------------------------------------------------------
  Infixity from Overlay.sml. To add to the README to keep up-to-date.
  
  infix ++ && |-> THEN THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC
  THEN_TCL ORELSE_TCL ?> |>
infix THEN1

(* infixes for THEN shorthands *)
infix >> >- >| \\ >>> >>- ??

infixr ## $;
infixr 3 -->;
infix 8 via by suffices_by
  
  ----------------------------------------------------------------------------*)

(* becareful to escape \\ to \\\\ in the following list *)
val l0 = String.tokens Char.isSpace
  (
  String.concatWith " "
  ["++ && |-> THEN THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC",
   "THEN_TCL ORELSE_TCL ?> |>",
   "THEN1",
   ">> >- >| \\\\ >>> >>- ??"]
  )
val l1 = String.tokens Char.isSpace "## $"
val l2 = String.tokens Char.isSpace "via by suffices_by"

val overlay_infixity =
  map (fn x => (x,Inf_left 0)) l0 @
  map (fn x => (x,Inf_right 0)) l1 @
  map (fn x => (x,Inf_right 3)) ["-->"] @
  map (fn x => (x,Inf_left 8)) l2




end
