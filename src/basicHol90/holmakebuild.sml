structure holmakebuild =
struct

  open Exception

  val holmake_tag = Tag.read "tactic_failed"

  fun basic_prover (t, tac: Abbrev.tactic) =
    Tactical.default_prover(t, tac)
    handle (e as HOL_ERR _) =>
      (print ("*** Proof of \n  "^Parse.term_to_string t^"\n*** failed.\n");
       Exception.print_HOL_ERR e;
       Thm.mk_oracle_thm holmake_tag ([], t))

  val _ = Tactical.set_prover basic_prover

end;
