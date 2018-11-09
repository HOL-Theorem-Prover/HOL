(* ========================================================================  *)
(* FILE          : smlInfix.sml                                              *)
(* DESCRIPTION   : Transforming a prefix operator into an infix one          *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure smlInfix :> smlInfix =
struct

infix 0 sml_infixl0_open sml_infixl0_close
infix 1 sml_infixl1_open sml_infixl1_close
infix 2 sml_infixl2_open sml_infixl2_close
infix 3 sml_infixl3_open sml_infixl3_close
infix 4 sml_infixl4_open sml_infixl4_close
infix 5 sml_infixl5_open sml_infixl5_close
infix 6 sml_infixl6_open sml_infixl6_close
infix 7 sml_infixl7_open sml_infixl7_close
infix 8 sml_infixl8_open sml_infixl8_close
infix 9 sml_infixl9_open sml_infixl9_close

infixr 0 sml_infixr0_open sml_infixr0_close
infixr 1 sml_infixr1_open sml_infixr1_close
infixr 2 sml_infixr2_open sml_infixr2_close
infixr 3 sml_infixr3_open sml_infixr3_close
infixr 4 sml_infixr4_open sml_infixr4_close
infixr 5 sml_infixr5_open sml_infixr5_close
infixr 6 sml_infixr6_open sml_infixr6_close
infixr 7 sml_infixr7_open sml_infixr7_close
infixr 8 sml_infixr8_open sml_infixr8_close
infixr 9 sml_infixr9_open sml_infixr9_close

fun a sml_infixl0_open f = fn x => f (a,x)
fun g sml_infixl0_close b = g b

fun f sml_infixr0_close b = fn x => f (x,b)
fun a sml_infixr0_open g = g a

val op sml_infixl1_open = op sml_infixl0_open
val op sml_infixl2_open = op sml_infixl0_open
val op sml_infixl3_open = op sml_infixl0_open
val op sml_infixl4_open = op sml_infixl0_open
val op sml_infixl5_open = op sml_infixl0_open
val op sml_infixl6_open = op sml_infixl0_open
val op sml_infixl7_open = op sml_infixl0_open
val op sml_infixl8_open = op sml_infixl0_open
val op sml_infixl9_open = op sml_infixl0_open

val op sml_infixl1_close = op sml_infixl0_close
val op sml_infixl2_close = op sml_infixl0_close
val op sml_infixl3_close = op sml_infixl0_close
val op sml_infixl4_close = op sml_infixl0_close
val op sml_infixl5_close = op sml_infixl0_close
val op sml_infixl6_close = op sml_infixl0_close
val op sml_infixl7_close = op sml_infixl0_close
val op sml_infixl8_close = op sml_infixl0_close
val op sml_infixl9_close = op sml_infixl0_close

val op sml_infixr1_open = op sml_infixr0_open
val op sml_infixr2_open = op sml_infixr0_open
val op sml_infixr3_open = op sml_infixr0_open
val op sml_infixr4_open = op sml_infixr0_open
val op sml_infixr5_open = op sml_infixr0_open
val op sml_infixr6_open = op sml_infixr0_open
val op sml_infixr7_open = op sml_infixr0_open
val op sml_infixr8_open = op sml_infixr0_open
val op sml_infixr9_open = op sml_infixr0_open

val op sml_infixr1_close = op sml_infixr0_close
val op sml_infixr2_close = op sml_infixr0_close
val op sml_infixr3_close = op sml_infixr0_close
val op sml_infixr4_close = op sml_infixr0_close
val op sml_infixr5_close = op sml_infixr0_close
val op sml_infixr6_close = op sml_infixr0_close
val op sml_infixr7_close = op sml_infixr0_close
val op sml_infixr8_close = op sml_infixr0_close
val op sml_infixr9_close = op sml_infixr0_close

datatype infixity_t = Inf_left of int | Inf_right of int

fun infix_pair infixity = case infixity of
    Inf_left n =>
    ("sml_infixl" ^ Int.toString n ^ "_open",
     "sml_infixl" ^ Int.toString n ^ "_close")
  | Inf_right n =>
    ("sml_infixr" ^ Int.toString n ^ "_open",
     "sml_infixr" ^ Int.toString n ^ "_close")

(* -------------------------------------------------------------------------
   Infixity from src/thm/Overlay.sml.
   ------------------------------------------------------------------------- *)

val l0 = String.tokens Char.isSpace
  (
  String.concatWith " "
  [
   "++ && |-> THEN THEN1 THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC",
   "THEN_TCL ORELSE_TCL ?> |> |>> ||> ||->",
   ">> >- >| \\\\ >>> >>- ??", 
   "~~ !~ Un Isct -- IN"
  ]
  )
val l1 = String.tokens Char.isSpace "## $"
val l2 = String.tokens Char.isSpace "via by suffices_by"

val overlay_infixity =
  map (fn x => (x,Inf_left 0)) l0 @
  map (fn x => (x,Inf_right 0)) l1 @
  map (fn x => (x,Inf_right 3)) ["-->"] @
  map (fn x => (x,Inf_left 8)) l2


end
