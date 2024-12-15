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

datatype pretty = datatype PrettyImpl.pretty
type 'a pprinter = 'a -> pretty

datatype break_style =
    CONSISTENT
  | INCONSISTENT

datatype frag = datatype quotation_dtype.frag
type 'a quotation = 'a frag list

val prettyPrint = PrettyImpl.prettyPrint

fun pp_to_string w f x =
  let
    open Uref
    val sbuf = Uref.new [] : string list Uref.t
    fun app s = (sbuf := s :: !sbuf)
    val _ = prettyPrint (app,w) (f x)
    val strings =
        case !sbuf of
            [] => []
          | "\n" :: rest => rest
          | ss => ss
  in
    String.concat (List.rev strings)
  end

val fint = FixedInt.fromInt
val add_string = PrettyString
fun add_stringsz(s,sz) = PrettyStringWithWidth(s,fint sz)
fun add_break(m,n) = PrettyBreak(fint m, fint n)
val NL = PrettyLineBreak
val add_newline = NL
fun bs2b bs = bs = CONSISTENT
fun block bs i ps = PrettyBlock(fint i, bs2b bs, [], ps)

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

fun pp_pretty p =
  case p of
      PrettyBreak(m,n) => if m = 1 andalso n = 0 then add_string "SPC"
                          else add_string ("BRK(" ^ FixedInt.toString m ^ "," ^
                                           FixedInt.toString n ^")")
    | PrettyString s =>
        add_string ("PrettyString \"" ^ String.toString s ^ "\"")
    | PrettyStringWithWidth (s,i) => add_string ("S \""^s^"\"")
    | PrettyBlock(i, cp, c, ps) =>
      PrettyBlock(2, true, [],
                  add_string ((if cp then "C" else "IC") ^ "-" ^
                              FixedInt.toString i ^ " {") ::
                  add_break(1,0) ::
                  pr_list pp_pretty [add_string ",", add_break(1,0)] ps @
                  [add_break(1,~2), add_string "}"])
    | PrettyLineBreak => add_string "NL"


end; (* struct *)
