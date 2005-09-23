signature wordsLib =
sig
    include Abbrev

    val words_compset : unit -> computeLib.compset

    val mk_index_type : int -> unit

    val Cases_on_word : term -> tactic
    val Cases_word    : tactic
end
