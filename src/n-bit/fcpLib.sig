signature fcpLib =
sig
    include Abbrev

    val mk_index_type : int -> thm * thm * thm
    val FCP_ss        : simpLib.ssfrag
end
