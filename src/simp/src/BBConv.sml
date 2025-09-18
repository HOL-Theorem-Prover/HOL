structure BBConv :> BBConv =
struct

open HolKernel boolLib Abbrev

type bbconv = thm -> thm
fun NO_BBCONV th = raise mk_HOL_ERR "BBConv" "NO_BBCONV" ""

fun FIRST_BBCONV bbcs th =
    case bbcs of
        [] => NO_BBCONV th
      | bbc :: rest => bbc th handle HOL_ERR _ => FIRST_BBCONV rest th

fun BBCONV_RULE c th = EQ_MP (c (REFL (concl th))) th

fun ORELSEBBC (c1, c2) th = c1 th handle HOL_ERR _ => c2 th

(* map a normal conversion into a bbconv *)
fun c2bbc c th0 =
    let val th = c (rhs (concl th0))
    in
      TRANS th0 th
    end

end (* struct *)
