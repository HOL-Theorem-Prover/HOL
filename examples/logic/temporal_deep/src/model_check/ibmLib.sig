signature ibmLib =
sig

val ibm_to_ks : Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm
val ibm_to_ks_total : Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm ->
Abbrev.thm
val ibm_to_ks_total_cheat : Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm

val ibm_to_ks_clock_total : Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm ->
Abbrev.thm
val ibm_to_ks_clock_total_cheat : Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm

val make_total_thm : Abbrev.term -> Abbrev.thm
val model_check_ibm : bool -> Abbrev.term -> Abbrev.term -> Abbrev.term -> Abbrev.thm option


end

