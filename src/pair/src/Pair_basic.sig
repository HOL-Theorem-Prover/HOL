signature Pair_basic =
    sig
   type term  = Term.term
   type thm   = Thm.thm
   type conv  = Abbrev.conv
   type tactic = Abbrev.tactic

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
