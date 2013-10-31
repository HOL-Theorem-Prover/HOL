signature ARM_prover_toolsLib =
sig
    val priv_mode_constraints_def : Thm.thm
    val add_to_simplist : Theory.thm -> unit
    val update_mode_changing_comp_list : Parse.term -> unit
    val save_comb_thm : string * Theory.thm * Parse.term -> Theory.thm
    val get_trans_thm : Parse.term -> Abbrev.thm
    val get_reflex_thm : Parse.term -> Abbrev.thm
    val get_sim_reflex_thm : Parse.term -> Abbrev.thm
    val get_unt_def : Parse.term -> Abbrev.thm
    val get_sim_def : Parse.term -> Abbrev.thm
    val prove_it :  Hol_pp.term ->   Parse.term ->  Parse.term -> Parse.term -> Parse.term -> Abbrev.thm * Abbrev.tactic
    val obtain_proofs : unit -> Abbrev.thm
    val GO_ON_TAC : unit -> Abbrev.tactic
    val go_on : int -> proofManagerLib.proof
    val go_on_p : int -> proofManagerLib.proof
    val thm_prove : Hol_pp.term -> Abbrev.thm
    val thm_proveP : Hol_pp.term -> Abbrev.thm
    val thm_proveS : Hol_pp.term -> Abbrev.thm
    val prove_and_save : Hol_pp.term * string -> Theory.thm
    val prove_and_save_e : Hol_pp.term * string -> Theory.thm
    val prove_and_save_s : Hol_pp.term * string -> Theory.thm
    val prove_and_save_p : Hol_pp.term * string * Parse.term -> Theory.thm
    val prove_and_save_p_helper : Hol_pp.term * string -> Theory.thm
    val MODE_MIX_TAC : Term.term ->  Abbrev.term list * Abbrev.term -> Abbrev.goal list * Abbrev.validation
    val LITTLE_MODE_MIX_TAC : Term.term ->  Abbrev.term list * Abbrev.term -> Abbrev.goal list * Abbrev.validation
end

