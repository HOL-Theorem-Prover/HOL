open HolKernel Parse boolLib

open attr1Theory

val _ = new_theory "attr2";

val data = ThmSetData.theory_data {settype = "test", thy = "attr1"}
val _ = if length data <> 1 orelse
           #1 (hd data) <> "attr1.PP" orelse
           not (aconv (concl (#2 (hd data))) ``P ==> P``)
        then
          raise mk_HOL_ERR "attr2Script" "testfunction"
                "ThmSetData malformed"
        else ()

val _ = save_thm("PP2", #2 (hd data))

val _ = export_theory();
