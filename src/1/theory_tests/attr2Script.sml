open HolKernel Parse boolLib

open attr1Theory

val _ = new_theory "attr2";

val data = ThmSetData.theory_data {settype = "test", thy = "attr1"}
val exn = mk_HOL_ERR "attr2Script" "testfunction" "ThmSetData malformed"
val th =
    case data of
        [ThmSetData.Addition(nm,th)] =>
          if nm <> "attr1.PP" orelse concl th !~ “P ==> P” then
            raise exn
          else th
      | _ => raise exn

val _ = save_thm("PP2", th)

val _ = export_theory();
