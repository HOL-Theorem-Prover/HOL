structure fastbuild =
struct
  (* this structure is used by Holmake to provide a "fast" mode of
     running theory scripts.  It toggles the prover that sits behind the
     prove (and store_thm) function to be a call to mk_thm, so proofs
     that require many cycles should now run very quickly.  Of course,
     the tactic value still has to be evaluated before it is then
     discarded.  But use of this can definitely speed slow scripts up
     considerably. *)

  val fast_proof_tag = Tag.read "fast_proof"

  fun fast_prover (t, tac: Abbrev.tactic) =
    Thm.mk_oracle_thm fast_proof_tag ([], t);

  fun first_fast_prover (t, tac : Abbrev.tactic) = let
  in
    Lib.mesg true "WARNING: using fast prover - proofs unchecked";
    Tactical.set_prover fast_prover;
    Thm.mk_oracle_thm fast_proof_tag ([], t)
  end;


  val _ = Tactical.set_prover first_fast_prover;

end