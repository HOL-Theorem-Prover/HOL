signature leakageLib =
sig

   include Abbrev

   val REPEAT_SAFE_EVAL                         : term -> thm
   val FIND_CONV                                : term -> (term -> thm) -> conv
   val ONCE_FIND_CONV                           : term -> (term -> thm) -> conv
   val UNFOLD_CONV                              : (thm list) -> (term -> thm) -> conv
   val MAKE_ALL_DISTINCT_CONV                   : (term -> thm) -> conv
   val MEM_CONV                                 : (term -> thm) -> conv
   val F_UNCHANGED_CONV                         : (term -> thm) -> conv
   val T_UNCHANGED_CONV                         : (term -> thm) -> conv
   val T_F_UNCHANGED_CONV                       : (term -> thm) -> conv
   val LEAKAGE_COMPUTE_PROVE_FINITE             : term -> thm list -> thm
   val LEAKAGE_COMPUTE_FINITE_HLR               : term * term * term -> thm list -> thm list
   val LEAKAGE_COMPUTE_CROSS_NOT_EMPTY          : term * term * term -> thm list -> thm
   val LEAKAGE_COMPUTE_INITIAL_REDUCE           : term * term * term -> thm list -> conv
   val COMPUTE_CARD                             : term -> (term -> thm) -> (term -> thm) -> thm
   val COMPUTE_HLR_CARDS                        : term * term * term -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> thm list
   val LEAKAGE_COMPUTE_REDUCE_CARDS             : term * term * term -> thm list -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> conv
   val LEAKAGE_COMPUTE_HLR_CROSS                : term * term * term -> thm list -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> conv
   val LEAKAGE_COMPUTE_IMAGE_HLR_CROSS          : term * term * term -> thm list -> thm list -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> conv
   val RECURSIVE_UNWIND_SUM                     : (term -> thm) -> (term -> thm) -> term -> thm
   val LEAKAGE_COMPUTE_UNWIND_OUTER_SUM         : (term -> thm) -> (term -> thm) -> (term -> thm) -> conv
   val LEAKAGE_COMPUTE_UNWIND_INNER_SUM         : term * term -> thm list -> thm list -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> conv
   val LEAKAGE_COMPUTE_CONV                     : term * term * term -> thm list -> thm list -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> (term -> thm) -> conv

end
