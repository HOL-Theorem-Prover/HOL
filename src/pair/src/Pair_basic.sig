(*****************************************************************************)
(* Hi Mike,                                                                  *)
(*                                                                           *)
(*   I spent a little time making Pair_basic work in Kananaskis-0. This      *)
(* includes PBETA_CONV, PALPHA_CONV, GEN_PALPHA_CONV and some other useful   *)
(* things. Pair_basic is at the bottom of the Grundy hierarchy, so it        *)
(* doesn't depend on other things. Probably, you should just compile it in   *)
(* your development directory.                                               *)
(*                                                                           *)
(* In the following, Pair_basic.sig comes before Pair_basic.sml.             *)
(*                                                                           *)
(* Konrad.                                                                   *)
(*****************************************************************************)


signature Pair_basic =
sig
  include Abbrev

        val MK_PAIR : thm * thm -> thm
        val PABS : term -> thm -> thm
        val PABS_CONV : conv -> conv
        val PSUB_CONV : conv -> conv
        val CURRY_CONV : conv
        val UNCURRY_CONV : conv
        val PBETA_CONV : conv
        val PBETA_RULE : thm -> thm
        val PBETA_TAC : tactic
        val RIGHT_PBETA : thm -> thm
        val LIST_PBETA_CONV : conv
        val RIGHT_LIST_PBETA : thm -> thm
        val LEFT_PBETA : thm -> thm
        val LEFT_LIST_PBETA : thm -> thm
        val UNPBETA_CONV : term -> conv
        val PETA_CONV : conv
        val PALPHA_CONV : term -> conv
        val GEN_PALPHA_CONV : term -> conv
        val PALPHA : term -> conv
        val paconv : term -> term -> bool
        val PAIR_CONV : conv -> conv
    end;

