open HolKernel Parse boolLib bossLib;

open register_indnATheory

val _ = new_theory "register_indnB";

Theorem foo_ind =
        case DefnBase.lookup_indn “register_indnA$foo” of
          SOME (th,_) => th
        | NONE => raise mk_HOL_ERR "register_indnB" "foo_ind"
                        "No ind'n stored for foo"

Theorem bar_ind =
        case DefnBase.lookup_indn “register_indnA$bar” of
          NONE => TRUTH
        | SOME _ => raise mk_HOL_ERR "register_indnB" "bar_ind"
                           "Ind'n incorrectly stored for bar"

Theorem baz_ind =
        case DefnBase.lookup_indn “register_indnA$baz” of
          NONE => TRUTH
        | SOME _ => raise mk_HOL_ERR "register_indnB" "baz_ind"
                           "Ind'n incorrectly stored for baz"


val _ = export_theory();
