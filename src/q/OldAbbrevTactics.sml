structure OldAbbrevTactics :> OldAbbrevTactics =
struct

open HolKernel boolLib

fun ABB l r =
    CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
                (Thm.EXISTS(mk_exists(l, mk_eq(r, l)), r) (Thm.REFL r))

fun ABBREV_TAC q (g as (asl,w)) =
    let val ctxt = free_varsl(w::asl)
     val (lhs,rhs) = dest_eq (Parse.parse_in_context ctxt q)
 in
    ABB lhs rhs g
 end

fun PAT_ABBREV_TAC q (g as (asl, w)) =
    let val fv_set = FVL (w::asl) empty_tmset
        val ctxt = HOLset.listItems fv_set
        val (l,r) = dest_eq(Parse.parse_in_context ctxt q)
        fun matchr t = raw_match [] fv_set r t ([],[])
        val l = variant (HOLset.listItems (FVL [r] fv_set)) l
        fun finder t = not (is_var t orelse is_const t) andalso can matchr t
    in
      case Lib.total (find_term finder) w of
        NONE => raise mk_HOL_ERR "OldAbbrevTactics"
                                 "PAT_ABBREV_TAC" "No matching term found"
      | SOME t => ABB l t g
    end


fun UNABBREV_TAC [QUOTE s] = let
  val s' = Lib.deinitcomment s
in
  FIRST_ASSUM(SUBST1_TAC o SYM o
              assert(curry op = s' o fst o dest_var o rhs o concl)) THEN
  BETA_TAC
end
  | UNABBREV_TAC _ = raise mk_HOL_ERR "OldAbbrevTactics"
                                      "UNABBREV_TAC" "unexpected quote format"

end;