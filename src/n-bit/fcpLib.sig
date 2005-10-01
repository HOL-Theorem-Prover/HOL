signature fcpLib =
sig
    include Abbrev

    val mk_index_type : int -> unit

    val FCP_ss        : simpLib.ssfrag
end
