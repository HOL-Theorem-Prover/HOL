structure Listener :> Listener =
struct

open Unsynchronized
type 'a t = (string * ('a -> unit)) list ref
exception DUP of string

fun new_listener () : 'a t = ref []

fun add_listener (r:'a t) (sf as (s,f)) =
    let
      val t = !r
    in
      case List.find (fn (s', _) => s' = s) t of
        NONE => r := sf :: t
      | SOME _ => raise DUP s
    end

fun remove_listener (r:'a t) s =
    let
      val t = !r
      val (fopt, rest) =
          Portable.trypluck' (fn (s',f) => if s' = s then SOME f else NONE) t
    in
      r := rest;
      fopt
    end

fun listeners (t:'a t) = (!t)

fun call_listener (t:'a t) v =
    let
      fun foldthis (kf as (k,f), A) =
          case Exn.capture f v of
              Exn.Res () => A
            | Exn.Exn e => (k,f,e) :: A
    in
      List.foldr foldthis [] (!t)
    end

fun without_one (r:'a t) s f x =
    let
      val t = !r
      val (_, t') =
          Portable.trypluck' (fn (s',f) => if s' = s then SOME () else NONE) t
    in
      setmp r t' f x
    end

fun without_all r f x = setmp r [] f x

end (* struct *)
