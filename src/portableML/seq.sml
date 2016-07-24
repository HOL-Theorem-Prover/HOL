(* Copyright University of Cambridge 1999 *)
(* Author: Michael Norrish *)
(* $Id$ *)

structure seq :> seq = struct
datatype 'a seq =
  LNIL |
  LCONS of ('a * 'a seq) |
  LDELAYREF of  'a seq ref |
  LDELAYED of (unit -> 'a seq)

fun delay f = LDELAYREF (ref (LDELAYED f))
fun force s =
  case s of
    LDELAYREF (r as ref (LDELAYED f)) => let
      val new = f ()
    in
      r := new; new
    end
  | LDELAYREF (ref x) => x
  | x => x

fun cons x xs = LCONS(x, xs)

fun null LNIL = true
  | null (LCONS _) = false
  | null (LDELAYED _) = raise Fail "seq - shouldn't happen"
  | null (x as LDELAYREF _) = null (force x)

fun cases LNIL = NONE
  | cases (LCONS (e, es)) = SOME (e, es)
  | cases (LDELAYED f) = raise Fail "seq - shouldn't happen"
  | cases (x as LDELAYREF _) = cases (force x)

fun fcases LNIL  (n, c) = n
  | fcases (LCONS(e, es)) (n, c) = c (e, es)
  | fcases (LDELAYED f) _ = raise Fail "seq - shouldn't happen"
  | fcases x (n, c) = fcases (force x) (n, c)

fun append LNIL x = x
  | append (LCONS (e, es)) x = delay (fn () => LCONS (e, append es x))
  | append (LDELAYED f) x = raise Fail "seq - shouldn't happen"
  | append x y = delay (fn () => append (force x) y)

fun result x = LCONS(x, LNIL)

fun fresult f = let
  fun listfn () = let
    val element = f ()
  in
    case element of
      NONE => LNIL
    | SOME x => LCONS(x, delay listfn)
  end
in
  delay listfn
end

fun map f LNIL = LNIL
  | map f (LCONS(e, es)) = delay (fn () => LCONS(f e, map f es))
  | map f (LDELAYED x) = raise Fail "seq - shouldn't happen"
  | map f x = delay (fn () => map f (force x))

fun mapPartial f s =
  case s of
    LNIL => LNIL
  | LCONS(e, es) => delay (fn () => case f e of
                                      NONE => mapPartial f es
                                    | SOME x => LCONS(x, mapPartial f es))
  | LDELAYED x => raise Fail "seq - shouldn't happen"
  | x => delay (fn () => mapPartial f (force x))

fun filter P = mapPartial (fn x => if P x then SOME x else NONE)

fun flatten LNIL = LNIL
  | flatten (LCONS(e, es)) = delay (fn () => append e (flatten es))
  | flatten (LDELAYED _) = raise Fail "seq - shouldn't happen"
  | flatten x = delay (fn () => flatten (force x))

fun bind LNIL f = LNIL
  | bind (LCONS(e, es)) f = delay (fn () => append (f e) (flatten (map f es)))
  | bind (LDELAYED _) _ = raise Fail "seq - shouldn't happen"
  | bind x f = delay (fn () => bind (force x) f)

val empty = LNIL

fun hd LNIL = raise Fail "seq - hd of nil"
  | hd (LCONS(e, _)) = e
  | hd (LDELAYED _) = raise Fail "seq - shouldn't happen"
  | hd x = hd (force x)

fun tl LNIL = raise Fail "seq - tl of nil"
  | tl (LCONS(e, es)) = force es
  | tl (LDELAYED _) = raise Fail "seq - shouldn't happen"
  | tl x = tl (force x)

fun fromList [] = LNIL
  | fromList (e::es) = delay (fn () => LCONS(e, fromList es))

fun take' 0 _ = []
  | take' _ LNIL = []
  | take' n (LCONS(e, es)) = e::take' (n - 1) es
  | take' _ (LDELAYED _) = raise Fail "seq.take - shouldn't happen"
  | take' n x = take' n (force x)

fun take n l =
  if n < 0 then raise Fail "seq.take - negative amount"
  else take' n l

fun drop' 0 s = s
  | drop' _ LNIL = LNIL
  | drop' n (LCONS(e, es)) = drop' (n - 1) es
  | drop' _ (LDELAYED _) = raise Fail "seq.drop - shouldn't happen"
  | drop' n x = drop' n (force x)

fun drop n l =
  if n < 0 then raise Fail "seq.drop - negative amount"
  else drop' n l

fun length LNIL = 0
  | length (LCONS(e, es)) = 1 + length (force es)
  | length (LDELAYED _) = raise Fail "seq - shouldn't happen"
  | length x = length (force x)

end
