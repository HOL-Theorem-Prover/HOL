structure parse_glob :> parse_glob =
struct

open regexpMatch

type sbuf = string * int

datatype t = RE of regexpMatch.regexp | CHAR of char

fun current(s,i) = SOME(String.sub(s,i)) handle Subscript => NONE
fun advance (s,i) = (s, i + 1)
fun new s = (s,0)

fun negate_set cset = let
  fun foldthis (remove, acc) = Binaryset.delete(acc, remove)
in
  Binaryset.foldl foldthis univ_cset cset
end

fun dot_rassociate re = let
  val dra = dot_rassociate
  fun merge (Dot(re1, re2)) re3 = merge re1 (merge re2 re3)
    | merge re1             re3 = Dot(re1, re3)
in
  case re of
      Not re0 => Not (dra re0)
    | Sum(re1, re2) => Sum(dra re1, dra re2)
    | And (re1, re2) => And(dra re1, dra re2)
    | Dot(re1, re2) => merge re1 (dra re2)
    | Star re0 => Star (dra re0)
    | _ => re
end

infix >-
fun (st >- f) s =
    case st s of
        NONE => NONE
      | SOME(r, s') => f r s'

infix ++
fun (st1 ++ st2) s =
    case st1 s of
        NONE => st2 s
      | x => x

fun lift st f s =
    case st s of
        NONE => NONE
      | SOME(r, s') => SOME(f r, s')

fun return s sb = SOME(s,sb)
fun sing c = Symbs (Binaryset.singleton Char.compare c)

fun toRegexp1 (CHAR c) = sing c
  | toRegexp1 (RE re) = re

fun toRegexp [] = Epsilon
  | toRegexp [e] = toRegexp1 e
  | toRegexp (e :: rest) = Dot(toRegexp1 e, toRegexp rest)

fun ADVANCE sb = SOME((), advance sb)

fun CURRENT sb =
    Option.map (fn c => (c, sb)) (current sb)

fun oncurrent f = CURRENT >- f

fun grab_word sl (s, i) = let
  val rest = String.extract(s, i, NONE)
in
  case List.find (fn p => String.isPrefix p rest) sl of
      NONE => NONE
    | SOME p => SOME(p, (s, i + size p))
end

infix >>
fun (st1 >> st2) = st1 >- (fn _ => st2)
fun fail s = NONE

fun consume v sb = SOME(v, advance sb)

(* ignores LC_COLLATE, thereby pretending it's "C" *)
fun range_finisher start = let
  fun doit c =
      case c of
          #"]" => return (Binaryset.addList(empty_cset, [start, #"-"]))
        | _ => let
          val c_i = Char.ord c and start_i = Char.ord start
        in
          if c_i >= start_i then
            consume
              (Binaryset.addList(empty_cset,
                                 List.tabulate(c_i - start_i + 1,
                                               fn i => Char.chr (i + start_i))))
          else
            consume empty_cset
        end
in
  oncurrent doit
end

val classnames =
    map (fn s => ":" ^ s ^ ":]")
        ["alnum", "alpha", "ascii", "blank", "cntrl",
         "digit", "graph", "lower", "print", "punct",
         "space", "upper", "xdigit", "word"]

val maybe_named_classes = let
  fun check s =
      case s of
          ":alnum:]" => return POSIX.alnum_set
        | ":alpha:]" => return POSIX.alpha_set
        | ":ascii:]" => return POSIX.ascii_set
        | ":blank:]" => return POSIX.blank_set
        | ":cntrl:]" => return POSIX.cntrl_set
        | ":digit:]" => return POSIX.digit_set
        | ":graph:]" => return POSIX.graph_set
        | ":lower:]" => return POSIX.lower_set
        | ":print:]" => return POSIX.print_set
        | ":punct:]" => return POSIX.punct_set
        | ":space:]" => return POSIX.space_set
        | ":up1per:]" => return POSIX.upper_set
        | ":xdigit:]" => return POSIX.xdigit_set
        | ":word:]" => return POSIX.word_set
        | _ => return empty_cset
in
  grab_word classnames >- check
end

fun MIF st1 stf2 st3 sb =
    case st1 sb of
        NONE => st3 sb
      | SOME (r, sb') => stf2 r sb'

fun parse_cset_nextchar prev = let
  fun meld s1 = lift parse_cset_comp (fn s2 => Binaryset.union(s1, s2))
  fun default c =
      ADVANCE >> lift (parse_cset_nextchar c) (fn s => Binaryset.add(s, prev))
  fun doit c =
      case (prev, c) of
          (_, #"-") => ADVANCE >> (range_finisher prev >- meld)
        | (_, #"]") => consume (Binaryset.singleton Char.compare prev)
        | (#"[", #":") => MIF maybe_named_classes meld (default c)
        | _ => default c
in
  oncurrent doit
end
and parse_cset_comp sb = let
  fun doit c =
      case c of
          #"]" => consume empty_cset
        | _ => ADVANCE >> parse_cset_nextchar c
in
  oncurrent doit sb
end

val parse_cset_comps1 = oncurrent (fn c => ADVANCE >> parse_cset_nextchar c)

val parse_cset = let
  fun doit c =
      case c of
          #"^" => ADVANCE >> lift parse_cset_comps1 (Symbs o negate_set)
        | #"!" => ADVANCE >> lift parse_cset_comps1 (Symbs o negate_set)
        | _ => lift parse_cset_comps1 Symbs
in
  oncurrent doit
end

val parse_component = let
  fun doit c =
      case c of
          #"*" => consume (RE (Not (Symbs empty_cset)))
        | #"?" => consume (RE (Symbs univ_cset))
        | #"[" => (ADVANCE >> lift parse_cset RE) ++ consume (CHAR #"[")
        | #"\\" => ADVANCE >>
                   (oncurrent (consume o CHAR) ++ return (CHAR #"\\"))
        | _  => consume (CHAR c)
in
  oncurrent doit
end

fun parse_components sb = let
  fun meld r = lift parse_components (fn rs => r::rs)
in
  (parse_component >- meld) ++ return []
end sb

fun parse_glob_components s =
    case parse_components (new s) of
        SOME (l, _) => l
      | NONE => raise Fail "parse_glob_components failed"

fun parse_glob s = toRegexp (parse_glob_components s)

end
