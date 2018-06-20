open HolKernel Parse boolLib

open SGAUnicodeMergeA1Theory SGAUnicodeMergeA2Theory

val _ = new_theory "SGAUnicodeMergeB";
val _ = set_grammar_ancestry ["SGAUnicodeMergeA1", "SGAUnicodeMergeA2"]


val numfails = ref 0

val thm1 = store_thm(
  "thm1",
  ``INTER A1 A2 = ∩ A1 A2``, (* UOK *)
  REWRITE_TAC[]) handle HOL_ERR _ => (numfails := 1; TRUTH)

val thm2 = store_thm(
  "thm2",
  ``FUNION f1 f2 = f1 ⊌ f2``,  (* UOK *)
  REWRITE_TAC[]) handle HOL_ERR _ => (numfails := !numfails + 1; TRUTH)

val _ = if !numfails > 0 then
          raise mk_HOL_ERR "SGA Unicode Test" ""
                (Int.toString (!numfails) ^ " failures")
        else ()

val _ = export_theory();
