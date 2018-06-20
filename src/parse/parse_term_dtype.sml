structure parse_term_dtype =
struct

datatype stack_terminal =
         STD_HOL_TOK of string
       | BOS
       | EOS
       | Id
       | TypeColon
       | TypeTok
       | EndBinding
       | VS_cons
       | ResquanOpTok

fun STi st =
    case st of
      STD_HOL_TOK _ => 0
    | BOS => 1
    | EOS => 2
    | Id => 3
    | TypeColon => 4
    | TypeTok => 5
    | EndBinding => 6
    | VS_cons => 7
    | ResquanOpTok => 8
fun ST_compare (p as (st1,st2)) =
    case p of
      (STD_HOL_TOK s1, STD_HOL_TOK s2) => String.compare(s1,s2)
    | _ => Lib.measure_cmp STi p

(* not used externally, but can be useful for debugging *)
datatype mx_src = Ifx | Pfx | MS_Other | MS_Multi
datatype mx_order = PM_LESS of mx_src
                  | PM_GREATER of mx_src
                  | PM_EQUAL
                  | PM_LG of {pfx:order,ifx:order}

end
