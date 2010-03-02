structure TermCoding :> TermCoding=
struct

open Lib Feedback HolKernel

fun encode t = let
  val fvs = free_vars t
  fun all P s =
      case UTF8.getChar s of
        NONE => true
      | SOME ((cs,_), rest) => P cs andalso all P rest
  fun check v = let
    val (nm, _) = dest_var v
  in
    nm <> "" andalso (all UnicodeChars.isAlphaNum nm orelse
                      all UnicodeChars.isSymbolic nm)
  end
  val _ = case List.find (not o check) fvs of
            NONE => ()
          | SOME v =>
            raise mk_HOL_ERR "TermCoding"
                             "encode"
                             ("Variable \""^String.toString (#1 (dest_var v))^
                              "\" unparseable.")
  val fvs_sorted = Listsort.sort (inv_img_cmp (#1 o dest_var) String.compare)
                                 fvs
  fun dupcheck [] = NONE
    | dupcheck [_] = NONE
    | dupcheck (v1::v2::rest) = if #1 (dest_var v1) = #1 (dest_var v2) then
                                  SOME (#1 (dest_var v1))
                                else dupcheck (v2::rest)
  val _ = case dupcheck fvs_sorted of
            NONE => ()
          | SOME s => raise mk_HOL_ERR "TermCoding" "encode"
                            ("Term has two free variables named \""^
                             String.toString s^"\" but at different types.")
  val printer0 = term_pp.pp_term term_grammar.min_grammar
                                 type_grammar.min_grammar
                                 PPBackEnd.raw_terminal
  fun printer pps = printer0 pps
                             |> trace ("types", 1)
                             |> trace ("Unicode", 0)
  val base0 = PP.pp_to_string 1000000 printer t
  val base = String.toString base0
in
  Coding.IntData.encode (size base) ^ base
end

val reader = let
  fun base_decode s = let
    val p0 = TermParse.term NONE term_grammar.min_grammar
                            type_grammar.min_grammar
    val p = p0 |> trace ("show_typecheck_errors", 0)
               |> trace ("syntax_error", 0)
               |> trace ("notify type variable guesses", 0)
  in
    SOME (p [Portable.QUOTE (valOf (String.fromString s))])
    handle HOL_ERR _ => NONE
         | Option => NONE
  end
in
  Coding.length_encoded base_decode
end

val decode = Coding.lift reader

end (* struct *)