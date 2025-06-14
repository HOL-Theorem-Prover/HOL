val z = 1 handle
(* a comment before the opt bar *) | e => () | f => () | other => raise other

val z = 1 handle | e => () | f => () | other => raise other

val y = fn | () => a | () => b

val x =
  case foo of
  (* first *)
  | first => () (* yup *)

  (* second *)
  | second =>

  (* sure *) (* what *)
  () (* okay *)

signature X =
sig
  datatype ('a, 'b) either =
| Left of 'a
| Right of 'b
end

datatype ('a, 'b) either =
| Left of 'a
| Right of 'b

fun 'a
  | foo ([] : 'a list) = 0
  | foo (x :: xs) =
      case xs of
      | [] => 1
      | _ => 1 + foo xs

val bar =
  fn
   | [] => true
   | x :: xs => false

signature X =
sig
  datatype ('a, 'b) either =
  | Left of 'a  (* in first branch of datatype spec *)
  | Right of 'b
end

datatype ('a, 'b) either =
| Left of 'a  (* in first branch of datatype declaration *)
| Right of 'b

(* hello *)
fun 'a
  | foo ([]: 'a list) = 0  (* in first branch of 'fun' declaration *)
  | foo (x :: xs) =
      case xs of
      | [] => 1  (* in first branch of 'case' expression *)
      | _ => 1 + foo xs

val bar =
  fn
   | [] => true  (* in first branch of anonymous function *)
   | x :: xs => false

val x =
  foo ()
  handle
  | Subscript => ()  (* in first branch of 'handle' expression *)
  | Option => ()
  | other => raise other