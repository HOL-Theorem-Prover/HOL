(* =========================================================================  *)
(* FILE          : tttInfix.sml                                               *)
(* DESCRIPTION   : Transforming a prefix operator into an infix one           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttInfix :> tttInfix =
struct

infix 0 ttt_infixl0_open ttt_infixl0_close
infix 1 ttt_infixl1_open ttt_infixl1_close
infix 2 ttt_infixl2_open ttt_infixl2_close
infix 3 ttt_infixl3_open ttt_infixl3_close
infix 4 ttt_infixl4_open ttt_infixl4_close
infix 5 ttt_infixl5_open ttt_infixl5_close
infix 6 ttt_infixl6_open ttt_infixl6_close
infix 7 ttt_infixl7_open ttt_infixl7_close
infix 8 ttt_infixl8_open ttt_infixl8_close
infix 9 ttt_infixl9_open ttt_infixl9_close

infixr 0 ttt_infixr0_open ttt_infixr0_close
infixr 1 ttt_infixr1_open ttt_infixr1_close
infixr 2 ttt_infixr2_open ttt_infixr2_close
infixr 3 ttt_infixr3_open ttt_infixr3_close
infixr 4 ttt_infixr4_open ttt_infixr4_close
infixr 5 ttt_infixr5_open ttt_infixr5_close
infixr 6 ttt_infixr6_open ttt_infixr6_close
infixr 7 ttt_infixr7_open ttt_infixr7_close
infixr 8 ttt_infixr8_open ttt_infixr8_close
infixr 9 ttt_infixr9_open ttt_infixr9_close

fun a ttt_infixl0_open f = fn x => f (a,x)
fun g ttt_infixl0_close b = g b

fun f ttt_infixr0_close b = fn x => f (x,b)
fun a ttt_infixr0_open g = g a

val op ttt_infixl1_open = op ttt_infixl0_open
val op ttt_infixl2_open = op ttt_infixl0_open
val op ttt_infixl3_open = op ttt_infixl0_open
val op ttt_infixl4_open = op ttt_infixl0_open
val op ttt_infixl5_open = op ttt_infixl0_open
val op ttt_infixl6_open = op ttt_infixl0_open
val op ttt_infixl7_open = op ttt_infixl0_open
val op ttt_infixl8_open = op ttt_infixl0_open
val op ttt_infixl9_open = op ttt_infixl0_open

val op ttt_infixl1_close = op ttt_infixl0_close
val op ttt_infixl2_close = op ttt_infixl0_close
val op ttt_infixl3_close = op ttt_infixl0_close
val op ttt_infixl4_close = op ttt_infixl0_close
val op ttt_infixl5_close = op ttt_infixl0_close
val op ttt_infixl6_close = op ttt_infixl0_close
val op ttt_infixl7_close = op ttt_infixl0_close
val op ttt_infixl8_close = op ttt_infixl0_close
val op ttt_infixl9_close = op ttt_infixl0_close

val op ttt_infixr1_open = op ttt_infixr0_open
val op ttt_infixr2_open = op ttt_infixr0_open
val op ttt_infixr3_open = op ttt_infixr0_open
val op ttt_infixr4_open = op ttt_infixr0_open
val op ttt_infixr5_open = op ttt_infixr0_open
val op ttt_infixr6_open = op ttt_infixr0_open
val op ttt_infixr7_open = op ttt_infixr0_open
val op ttt_infixr8_open = op ttt_infixr0_open
val op ttt_infixr9_open = op ttt_infixr0_open

val op ttt_infixr1_close = op ttt_infixr0_close
val op ttt_infixr2_close = op ttt_infixr0_close
val op ttt_infixr3_close = op ttt_infixr0_close
val op ttt_infixr4_close = op ttt_infixr0_close
val op ttt_infixr5_close = op ttt_infixr0_close
val op ttt_infixr6_close = op ttt_infixr0_close
val op ttt_infixr7_close = op ttt_infixr0_close
val op ttt_infixr8_close = op ttt_infixr0_close
val op ttt_infixr9_close = op ttt_infixr0_close

datatype infixity_t = Inf_left of int | Inf_right of int

fun infix_pair infixity = case infixity of
    Inf_left n =>
    ("ttt_infixl" ^ Int.toString n ^ "_open",
     "ttt_infixl" ^ Int.toString n ^ "_close")
  | Inf_right n =>
    ("ttt_infixr" ^ Int.toString n ^ "_open",
     "ttt_infixr" ^ Int.toString n ^ "_close")

(*----------------------------------------------------------------------------
  Infixity from Overlay.sml. To add to the README to keep up-to-date.
  TacticToe automatically recognize infix tokens if they are declared within   
  the file it is reading. 
  ----------------------------------------------------------------------------*)

val l0 = String.tokens Char.isSpace
  (
  String.concatWith " "
  [
   "++ && |-> THEN THEN1 THENL THEN_LT THENC ORELSE ORELSE_LT ORELSEC",
   "THEN_TCL ORELSE_TCL ?> |> |>> ||> ||->",
  (* The next two lines of infix characters  are probably determined using
     PolyML.Namespace and isInfix function *)
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
