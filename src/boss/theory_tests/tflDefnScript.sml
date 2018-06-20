open HolKernel Parse boolLib bossLib;

val _ = new_theory "tflDefn";

val _ = Datatype`expr = C1 num expr | C2 num`

val _ = new_constant("do_log", ``:num -> expr list option``)

val evaluate_defn = Hol_defn "evaluate" `
  evaluate (C1 n e1) =
    case evaluate e1 of
      INL v1 => (* if the v1 is replaced by _ or v, the definition succeeds *)
        (case do_log n of
             SOME [e] => evaluate e
           | _ => INR T)
     | res => res`

val _ = export_theory();
