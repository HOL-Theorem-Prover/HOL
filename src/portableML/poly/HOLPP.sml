(* PP -- Oppen-style prettyprinters.
 *
 * Modified for Moscow ML from SML/NJ Library version 0.2
 *
 * COPYRIGHT (c) 1992 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *)

(* the functions and data for actually doing printing. *)
structure HOLPP :> HOLPP =
struct

datatype pretty = datatype PolyML.pretty
type ppstream = pretty list

type ('a,'st) printer = 'st -> 'a * 'st * ppstream

datatype break_style =
    CONSISTENT
  | INCONSISTENT

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
type 'a quotation = 'a frag list

val prettyPrint = PolyML.prettyPrint

fun pp_to_string w f x =
  let
    val sbuf = ref [] : string list ref
    fun app s = (sbuf := s :: !sbuf)
  in
    prettyPrint (app,w) (f x);
    String.concat (List.rev (!sbuf))
  end

val add_string = PrettyString
val add_break = PrettyBreak
val NL = add_break(1000000, 0)
fun bs2b bs = bs = CONSISTENT
fun block bs i ps = PrettyBlock(i, bs2b bs, [], ps)

fun pr_list f b [] = []
  | pr_list f b [e] = [f e]
  | pr_list f b (e::es) = (f e :: b) @ pr_list f b es
fun tabulateWith f b c =
  if c < 0 then raise Fail "tabulateWith: negative argument"
  else
    let
      fun recurse acc n =
        if n = 0 then f 0 :: acc
        else recurse (b @ f n :: acc) (n - 1)
    in
      if c = 0 then [] else recurse [] (c - 1)
    end

end; (* struct *)
