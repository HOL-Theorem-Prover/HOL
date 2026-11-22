(* ===================================================================== *)
(* FILE          : HOLmessage.sml                                        *)
(* DESCRIPTION   : Messages that carry HOL values rather than their      *)
(*                 printed form.                                         *)
(* ===================================================================== *)

structure HOLmessage :> HOLmessage =
struct

datatype message = Empty
                 | Txt of string
                 | PP of unit -> HOLPP.pretty
                 | Seq of message * message

val empty = Empty

fun txt "" = Empty
  | txt s = Txt s

fun pp f = PP f

fun op ^^ (Empty, m) = m
  | op ^^ (m, Empty) = m
  | op ^^ (m1, m2) = Seq (m1, m2)

fun concat [] = Empty
  | concat ms = List.foldr op ^^ Empty ms

fun isEmpty Empty = true
  | isEmpty (Txt s) = s = ""
  | isEmpty (PP _) = false
  | isEmpty (Seq (m1, m2)) = isEmpty m1 andalso isEmpty m2

fun isPlain (PP _) = false
  | isPlain (Seq (m1, m2)) = isPlain m1 andalso isPlain m2
  | isPlain _ = true

(* A message is rendered while something has already gone wrong, often
   while reporting it.  A value whose printer fails -- a term mentioning
   a type the ambient context no longer knows, say -- must not take the
   report down with it, so every forcing of a suspension is guarded.
   Interrupt is not an error and is let through. *)
fun force f ifFailed =
  f () handle Portable.Interrupt => raise Portable.Interrupt
             | _ => ifFailed

val unprintable = "<unprintable>"

val plain_renderer =
  ref (fn f => HOLPP.pp_to_string (!Globals.linewidth) (fn () => f ()) ())

(* The suspensions are collected right to left onto an accumulator so
   that a long left-nested `^^' chain does not build a deep stack. *)
fun parts (m, acc) =
  case m of
    Empty => acc
  | Txt s => HOLPP.add_string s :: acc
  | PP f => force f (HOLPP.add_string unprintable) :: acc
  | Seq (m1, m2) => parts (m1, parts (m2, acc))

fun toPretty m =
  case parts (m, []) of
    [] => HOLPP.add_string ""
  | [p] => p
  | ps => HOLPP.block HOLPP.INCONSISTENT 0 ps

(* Text is concatenated as it was given, never laid out again: see the
   signature.  Only the suspensions go through the pretty-printer, and
   each is laid out on its own so that one long term cannot re-flow the
   words around it. *)
fun toString m =
  let
    fun strings (m, acc) =
      case m of
        Empty => acc
      | Txt s => s :: acc
      | PP f => force (fn () => !plain_renderer f) unprintable :: acc
      | Seq (m1, m2) => strings (m1, strings (m2, acc))
  in
    case strings (m, []) of
      [] => ""
    | [s] => s
    | ss => String.concat ss
  end

end  (* HOLmessage *)

(* Poly/ML prints a value of an opaque type as `?', and `exnMessage' --
   which much of the tree reaches for when it reports an exception --
   answers from that generic printer.  Without this, a HOL error comes
   back as `message = ?' and the text it was raised with is simply
   gone, which is not what the string-valued interfaces promise.

   The registration has to sit outside the seal: inside, it would be
   against the representation, which Poly/ML holds to be a different
   type from the one everyone else sees, and is never found.  A
   registration is saved with the heap, so this reaches scripts run in
   batch -- which load no prelude -- as well as the REPL.  The quoting
   is Poly/ML's own rendering of a string, which is what this field
   printed as before it held a message. *)
val () =
    PolyML.addPrettyPrinter
      (fn _ => fn _ => fn (m : HOLmessage.message) =>
          PolyML.PrettyString
            ("\"" ^ String.toString (HOLmessage.toString m) ^ "\""))
