signature arm_core_decompLib =
sig

    val l3_triple: string -> (Thm.thm * int * int option) *
                             (Thm.thm * int * int option) option
    val swap_primes: Term.term -> Term.term

end
