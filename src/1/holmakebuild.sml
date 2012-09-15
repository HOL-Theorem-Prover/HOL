structure holmakebuild =
struct

local
   open Feedback

   val holmake_tag = "tactic_failed"

   fun basic_prover (t, tac: Abbrev.tactic) =
     Tactical.default_prover (t, tac)
     handle (e as HOL_ERR _) =>
        (HOL_MESG
           ("*** Proof of \n  " ^ Parse.term_to_string t ^ "\n*** failed.\n")
         ; HOL_MESG (exn_to_string e)
         ; Thm.mk_oracle_thm holmake_tag ([], t))
in
   val () = Tactical.set_prover basic_prover
end

end
