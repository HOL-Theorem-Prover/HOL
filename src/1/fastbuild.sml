(*---------------------------------------------------------------------------*)
(* This structure is used by Holmake to provide a "fast" mode of running     *)
(* theory scripts.  It toggles the prover that sits behind the prove         *)
(* (and store_thm) function to be a call to mk_thm, so proofs that require   *)
(* many cycles should now run very quickly.  Of course, the tactic value     *)
(* still has to be evaluated before it is then discarded.  But use of this   *)
(* can definitely speed slow scripts up considerably.                        *)
(*---------------------------------------------------------------------------*)

structure fastbuild =
struct

local open Feedback Thm
in

val fast_proof_tag = "fast_proof"

fun fast_prover (t, tac:Abbrev.tactic) = mk_oracle_thm fast_proof_tag ([], t)

fun first_fast_prover (t, tac:Abbrev.tactic) =
 let in
    HOL_MESG "using fast prover - proofs unchecked";
    Tactical.set_prover fast_prover;
    mk_oracle_thm fast_proof_tag ([], t)
  end;


val _ = Tactical.set_prover first_fast_prover;

end end;
