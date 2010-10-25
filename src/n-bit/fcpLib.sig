signature fcpLib =
sig
    include Abbrev

    val index_type    : Arbnum.num -> hol_type
    val index_to_num  : hol_type -> Arbnum.num

    val INDEX_CONV    : conv
    val DIMINDEX      : Arbnum.num -> thm
    val FINITE        : Arbnum.num -> thm
    val SIZE          : Arbnum.num -> thm
    val FCP_ss        : simpLib.ssfrag

    val inst_fcp_lengths : term -> term
end
