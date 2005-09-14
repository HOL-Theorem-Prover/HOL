signature machine_wordsLib =
sig
    include Abbrev

    val WORD_CONV : conv

    val machine_words_compset : unit -> computeLib.compset
end
