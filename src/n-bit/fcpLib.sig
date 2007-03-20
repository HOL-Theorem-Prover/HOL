signature fcpLib =
sig
    include Abbrev

    val index_type    : Arbnum.num -> hol_type
    val INDEX_CONV    : conv
    val DIMINDEX      : Arbnum.num -> thm
    val FINITE        : Arbnum.num -> thm
    val SIZE          : Arbnum.num -> thm
    val FCP_ss        : simpLib.ssfrag

    val guess_fcp_lengths : term -> term
    val guess_lengths : unit -> unit
end
