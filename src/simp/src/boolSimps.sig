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
                                           second argument fully first *)
     val LET_COMP_ss : simpLib.ssdata
     (* traverses let terms but doesn't allow the beta redex unless
        the RHS is T or F.  Add theorems of the form
           LET f (I v) = ...
        to allow additional forms looking like v to be treated as values. *)


end

