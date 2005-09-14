signature wordsLib =
sig
    include Abbrev

    val words_compset : unit -> computeLib.compset

    val mk_index_type : int -> unit
end
