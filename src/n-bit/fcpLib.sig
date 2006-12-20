signature fcpLib =
sig
    include Abbrev

    val index_type    : int -> hol_type
    val mk_index_type : int -> thm * thm * thm
    val FCP_ss        : simpLib.ssfrag
end
