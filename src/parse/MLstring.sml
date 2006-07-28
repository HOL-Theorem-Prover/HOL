structure MLstring :> MLstring =
struct

  exception stringerror of int * string
  fun numread s i base basestring size = let
    val digits = String.substring(s,i,size)
    fun read i = if i < size then SOME(String.sub(digits,i), i + 1)
                 else NONE
    val value = Int.scan base read 0
    val error = "Illegal "^Int.toString size^"-digit "^
                basestring^" constant: "^ digits
  in
    case value of
      SOME(v, pos) =>
      if pos <> size then raise stringerror(i + 1, error)
      else if v > 255 then
        raise stringerror(i + 1, "Character code is too large")
      else chr v
    | NONE => raise stringerror(i + 1, error)
  end handle Subscript =>
             raise stringerror(i + 1, "Unterminated "^basestring^"-literal")

  fun scanMLstring s = let
    fun scan' acc i = let
      val c = String.sub(s,i)
    in
      if not (Char.isPrint c) then
        raise stringerror(i,"Unprintable char "^String.toString (str c))
      else
        case c of
          #"\"" => raise stringerror(i, "Double-quote (\") not permitted")
        | #"\\" => do_backslash acc (i + 1)
        | _ => scan' (c::acc) (i + 1)
    end handle Subscript => String.implode (List.rev acc)
    and do_backslash acc i  =
        case String.sub(s,i) of
          #"a" => scan' (#"\a" :: acc) (i + 1)
        | #"b" => scan' (#"\b" :: acc) (i + 1)
        | #"t" => scan' (#"\t" :: acc) (i + 1)
        | #"n" => scan' (#"\n" :: acc) (i + 1)
        | #"v" => scan' (#"\v" :: acc) (i + 1)
        | #"f" => scan' (#"\f" :: acc) (i + 1)
        | #"r" => scan' (#"\r" :: acc) (i + 1)
        | #"^" =>
          (let
             val c = String.sub(s, i + 1)
             val cord = ord c
           in
             if 64 <= cord andalso cord <= 95 then
               scan' (chr (cord - 64) :: acc) (i + 2)
             else
               raise stringerror(i + 1, "Illegal control character spec")
           end handle Subscript =>
                      raise stringerror(i,
                                        "Unterminated control character spec"))
        | #"\"" => scan' (#"\"" :: acc) (i + 1)
        | #"\\" => scan' (#"\\" :: acc) (i + 1)
        | #"u" => let
            val c = numread s (i + 1) StringCvt.HEX "hex" 4
          in
            scan' (c::acc) (i + 5)
          end
        | c => if Char.isDigit c then let
                   val c' = numread s i StringCvt.DEC "decimal" 3
                 in
                   scan' (c'::acc) (i + 3)
                 end
               else if Char.isSpace c then let
                   fun recurse i =
                       (if Char.isSpace(String.sub(s,i)) then
                          recurse (i + 1)
                        else i)
                   val i' = recurse (i + 1)
                 in
                   if String.sub(s,i') = #"\\" then scan' acc (i' + 1)
                   else raise stringerror(i, "Ill-formed escape sequence")
                 end handle Subscript =>
                            raise stringerror(i, "Ill-formed escape sequnce")
               else raise stringerror(i, "Ill-formed escape sequnce")
  in
    scan' [] 0
  end

end (* struct *)
