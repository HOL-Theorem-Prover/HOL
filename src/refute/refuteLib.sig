signature refuteLib =
sig
  include Abbrev

    val AC : (thm * thm) -> term -> thm
    val AC_CANON_GEN_CONV : (thm * thm) -> (term * term -> order) -> conv
    val AC_CANON_CONV : (thm * thm) -> conv
    val ASSOC_CONV : thm -> conv
    val CONJ_ACI : term -> thm
    val DISTRIB_CONV : thm * thm -> conv

    val ONEWAY_SKOLEM_CONV : term list -> conv
    val NNF_CONV : conv -> bool -> conv
    val NNF_SKOLEM_CONV : conv -> bool -> conv
    val DISJPATH_CONV : term -> thm
    val RATSKOL : thm -> thm
    val SKELIM : term list -> thm -> thm
    val REFUTE : conv -> conv -> bool -> conv -> conv
    val CONV_THEN_REFUTE: conv -> conv -> conv
    val PRENEX_CONV : conv
    val DEPTH_BINOP_CONV : term -> conv -> conv
    val BODY_CONV : conv -> conv
    val PROP_CNF_CONV : conv
    val PROP_DNF_CONV : conv
    val CNF_CONV : conv
    val DNF_CONV : conv
    val CNF_THEN_REFUTE : (thm list -> thm) -> conv
    val CNF_REFUTE : conv -> conv -> (thm list -> thm) -> conv
    val CONV_OF_PROVER : conv -> thm list -> conv

    val FOL_CONV : conv
    val UNLAMB_CONV : conv
    val EQ_ABS_CONV : conv

    val latest :  (thm * thm * term) option ref;

end
