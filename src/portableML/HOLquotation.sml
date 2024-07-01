structure HOLquotation :> HOLquotation =
struct

open quotation_dtype

fun norm_quote [] = []
  | norm_quote [x] = [x]
  | norm_quote (QUOTE s1 :: QUOTE s2 :: rst) =
      norm_quote (QUOTE (s1 ^ s2) :: rst)
  | norm_quote (h :: rst) = h :: norm_quote rst


fun dest_last_string s =
    let
      open Substring
      val ss0 = dropr Char.isSpace (full s)
      val sz0 = size ss0
    in
      if sz0 >= 2 then
        let
          val last2 = slice (ss0, sz0 - 2, NONE)
          fun scanback i depth =
              if i >= 1 then
                if sub(ss0, i) = #"*" andalso sub(ss0,i-1) = #"(" then
                  if depth = 0 then
                    ([QUOTE (string (slice(ss0, 0, SOME (i - 1))))],
                     SOME (string (slice (ss0, i+1, SOME (sz0 - i - 3)))))
                  else scanback (i - 1) (depth - 1)
                else if sub(ss0,i) = #")" andalso sub(ss0,i-1) = #"*" then
                  scanback (i - 2) (depth + 1)
                else
                  scanback (i - 1) depth
              else ([QUOTE s], NONE)
        in
          if string last2 = "*)" then scanback (sz0 - 3) 0
          else ([QUOTE s], NONE)
        end
      else ([QUOTE s], NONE)
    end


fun dest_last_comment q =
    case q of
        [] => (q, NONE)
      | [ANTIQUOTE a] => (q, NONE)
      | [QUOTE s] => dest_last_string s
      | f::fs => let val (fs', copt) = dest_last_comment fs
                 in
                   (f::fs', copt)
                 end


end
