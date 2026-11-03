structure holmakebuild =
struct

local
   open Feedback

   val holmake_tag = "tactic_failed"

   fun basic_prover ctxt (g, tac: Abbrev.tactic) =
     Tactical.TAC_PROOF_in ctxt (g, tac)
     handle (e as HOL_ERR _) =>
        (HOL_MESG
           ("*** Proof of \n  " ^ Parse.term_to_string (#2 g) ^
            "\n*** failed (used CHEAT).\n")
         ; HOL_MESG (exn_to_string e)
         ; if !Globals.dumpheap_on_failure andalso
              not (!Globals.interactive)
           then
             (case boolLib.dump_failure_state
                     (boolLib.current_thm_name ctxt, g) of
                  NONE => ()
                | SOME file =>
                  HOL_MESG ("Heap saved to " ^ file ^
                            "; resume with: bin/hol --holstate=" ^ file))
           else ()
         ; Thm.mk_oracle_thm holmake_tag g)
in
   val () = Tactical.set_prover basic_prover
end

end
