structure fragstr :> fragstr =
struct

open optmonad monadic_parse
infix >- >> ++ >->

fun member x [] = false
  | member x (y::ys) = x = y orelse member x ys

fun is_antiq (ANTIQUOTE _) = true
  | is_antiq _ = false

fun string s = let
  fun handle_it (ANTIQUOTE _) = fail
    | handle_it (QUOTE s') = let
      in
        if (s = s') then
          return s
        else
          if String.isPrefix s s' then
            pushback (QUOTE (String.extract(s', size s, NONE))) >> return s
          else
            if String.isPrefix s' s then
              (string (String.extract(s, size s', NONE)) >> return s)
            else
              fail
      end
in
  (if s = "" then return "" else fail) ++ (get >- handle_it)
end


fun strip_eqs strm = let
  fun f (QUOTE s) = s = ""
    | f _ = false
in
  many (itemP f) strm
end

fun pushback_ss ss =
  if not (Substring.isEmpty ss) then pushback (QUOTE (Substring.string ss))
  else ok

fun many_charP P = let
  fun return_slist acc = return (concat (List.rev acc))
  fun recurse acc (current: 'a frag) =
    case current of
      ANTIQUOTE _ => pushback current >> return_slist acc
    | QUOTE s =>
        if s = "" then (get >- recurse acc) ++ return_slist acc
        else let
          open Substring
          val ss = all s
          val (l,r) = splitl P ss
        in
          if isEmpty l then pushback_ss r >> return_slist acc
          else
            if isEmpty r then ((get >- recurse (s :: acc)) ++
                               return_slist (s :: acc))
            else pushback_ss r >> return_slist (string l :: acc)
        end
in
  (get >- recurse []) ++ (return "")
end

fun many1_charP P =
  many_charP P >- (fn s => if s <> "" then return s else fail)

fun identP0 P = let
  fun h (ANTIQUOTE _) = return ""
    | h (QUOTE s) = let
        open Substring
        val (l,r) = splitl P (all s)
      in
        (if size r > 0 then pushback (QUOTE (string r)) else ok) >>
        return (string l)
      end
in
  strip_eqs >> ((get >- h) ++ return "")
end

fun itemP P = let
  fun handle_it (ANTIQUOTE _) = fail
    | handle_it (QUOTE s) = let
        open Substring
        val (c, ss) = valOf (getc (all s))
      in
        if P c then
          (if size ss <> 0 then pushback (QUOTE (string ss)) else ok)  >>
          return c
        else
          fail
      end
in
  strip_eqs >> get >- handle_it
end

fun item c = itemP (fn c' => c = c')


infixr >+
fun (c >+ P) x = x = c orelse P x

fun normal_alpha_ident strm  =
  (strip_eqs >> itemP Char.isAlpha >-                (fn c1 =>
   identP0 (#"'" >+ #"_" >+ Char.isAlphaNum) >-      (fn cs =>
   return (String.concat [implode [c1], cs])))) strm

fun antiq s = let
  fun h (ANTIQUOTE a) = return a
    | h x = pushback x >> fail
in
  (strip_eqs >> get >- h) s
end

fun drop_upto stopats strm = let
  fun c1 s = Option.map #1 (Substring.getc (Substring.all s))
  val fsts = List.mapPartial c1 stopats
in
  (many ((monadic_parse.itemP is_antiq >> ok) ++
         (many1_charP (fn c => not (member c fsts)) >> ok)) >>
   ((tryall string stopats) ++
    (itemP (fn c => true) >> drop_upto stopats))) strm
end

fun nonempty P = P >- (fn s => if s = "" then fail else return s)
fun grab_whitespace strm = (many1_charP Char.isSpace >> ok) strm

fun comment strm = let
  fun comment_internals strm' =
    ((drop_upto ["(*", "*)"] ++
      (fn x => (print "WARNING: Unterminated comment.\n";
                ([], SOME "*)")))) >-
     (fn s =>
      if s = "(*" then
        pushback (QUOTE "(*") >> comment >> comment_internals
      else
        ok)) strm'
in
  (string "(*" >> comment_internals) strm
end


fun token Prser = many (grab_whitespace ++ comment) >> strip_eqs >> Prser


fun symbol s = token (string s)

fun eof cs =
  case cs of
    [] => ([], SOME ())
  | x =>
      if List.all (fn QUOTE s => size s = 0 | ANTIQUOTE _ => false) x then
        ([], SOME ())
      else
        (x, NONE)

fun parse P =
  P >-> (many (grab_whitespace ++ comment) >> eof)

end
