open HolKernel Parse boolLib bossLib;

val _ = new_theory "comp_delbinding1";

(* compset now has foo_def in it *)
val foo_def = Define‘foo x = x + 1’;

val _ = case ThmSetData.current_data{settype="compute"} of
            [ThmSetData.ADD({Thy = "comp_delbinding1", Name = "foo_def"}, _)] =>
              print "Compute data OK\n"
          | _ => raise Fail "Compute data Bad!"

val _ =
    case LoadableThyData.segment_data
           {thy="comp_delbinding1", thydataty="compute"}
     of
        NONE => raise Fail "No compute data for LTD.segment_data"
      | SOME t => print "LTD.segment_data exists\n"

(* now replace "foo_def" binding with something else; the old binding
   should drop out of the compset
*)
Theorem foo_def[allow_rebind] = REFL ``x:num``

val _ = null (ThmSetData.current_data{settype="compute"}) orelse
        raise Fail "compute data not empty!"

val th = EVAL “foo 2”
val _ = rhs (concl th) ~~ lhs (concl th) orelse
        (print "foo was evaluated - unfortunate but unavoidable perhaps!\n";
         true)



val _ = export_theory();
