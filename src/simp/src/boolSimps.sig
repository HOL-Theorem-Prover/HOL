signature boolSimps =
sig
     val bool_ss : simpLib.simpset
     val BOOL_ss : simpLib.ssdata       (* boolean rewrites and
                                           beta conversion *)
     val CONG_ss : simpLib.ssdata       (* congruence rules for ==> and
                                           if-then-else *)
     val CONJ_ss : simpLib.ssdata       (* congruence rules for /\; not
                                           included in bool_ss, but
                                           occasionally useful *)
     val NOT_ss : simpLib.ssdata        (* rewrites that move negations
                                           inwards, included in bool_ss *)
     val COND_elim_ss : simpLib.ssdata  (* eliminates if-then-else's;
                                           not in bool_ss *)
     val LIFT_COND_ss : simpLib.ssdata  (* lifts conds high in a term, but
                                           doesn't eliminate them; can merge
                                           those of the same guard or
                                           opposing guards *)
     val UNWIND_ss : simpLib.ssdata     (* "pointwise" elimination for
                                            ? and !, included in bool_ss *)
     val ETA_ss : simpLib.ssdata        (* eta conversion;
                                           not included in bool_ss *)

     val LET_ss : simpLib.ssdata        (* writes out let terms, using a
                                           congruence to evaluate the
                                           second argument first *)

     val DNF_ss : simpLib.ssdata
        (* converts a term to DNF at the level of propositional logic, and
           also moves quantifiers around to give them maximum useful scope
           over their bodies:
               (?x. P x) /\ Q   -->  ?x. P x /\ Q
               P /\ (?x. Q x)   -->  ?x. P /\ Q x
               (?x. P x) ==> Q  -->  !x. P x ==> Q
               P ==> !x. Q x    -->  !x. P ==> Q x
               !x. P x /\ Q x   -->  (!x. P x) /\ (!x. Q x)
               ?x. P x \/ Q x   -->  (?x. P x) \/ (?x. Q x)
           Think of this simpset fragment as attempting to achieve as
           much as possible of STRIP_TAC within a single goal.

           Note that it leaves ==> alone, but includes the following
           extra rewrites:
               P \/ Q ==> R     -->  (P ==> R) /\ (Q ==> R)
               P ==> Q /\ R     -->  (P ==> Q) /\ (P ==> R)

           This simpset fragment will give UNWIND_ss maximum opportunity to
           eliminate equalities. *)

end

