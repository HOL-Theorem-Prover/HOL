signature fcpLib =
sig
    include Abbrev

    val mk_index_type : int -> unit
    val mk_index_type_thm : int -> thm * thm
    val FCP_ss        : simpLib.ssfrag
end
