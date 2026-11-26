signature blastLib =
sig
    (* BIT_BLAST_CONV performs internal tree scans, so callers must use it
       only on separately bounded inputs (for example, small schematic
       terms). *)
    val BIT_BLAST_CONV   : Conv.conv
    (* The word normalizer before bit-blasting, with the given fragment in
       place of wordsLib.WORD_CANCEL_ss. *)
    val WORD_SIMP_CONV_WITH_CANCEL : simpLib.ssfrag -> Conv.conv
    val BBLAST_CONV      : Conv.conv
    (* BBLAST_CONV with the given word normalizer, and a wrapper (e.g. a
       profiler) around the propositional phase. *)
    val BBLAST_CONV_WITH_PROFILES :
      Conv.conv -> (Conv.conv -> Conv.conv) -> Conv.conv
    val BBLAST_CONV_WITH_STAGES :
      {word_simp : Conv.conv,
       bit_blast : Conv.conv -> Term.term list -> Thm.thm list,
       rewrite : Thm.thm list -> Conv.conv,
       prover : Conv.conv -> Conv.conv} -> Conv.conv
    val BBLAST_PROVE_WITH_CONVERSION : Conv.conv -> Conv.conv
    val BBLAST_PROVE     : Conv.conv
    val BBLAST_PROVE_TAC : Tactic.tactic
    val BBLAST_RULE      : Conv.rule
    val BBLAST_TAC       : Tactic.tactic
    val FULL_BBLAST_TAC  : Tactic.tactic
    val MP_BLASTABLE_TAC : Tactic.tactic

    val trace                 : HOLFlags.flag
    val print_counterexamples : HOLFlags.bflag
    val multiply_limit        : HOLFlags.flag
end
