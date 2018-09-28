open HolKernel Parse boolLib bossLib;

val _ = new_theory "regexSemantics";



(* 3.1 basic regular expression semantics *)
(* -------------------------------------------------------------------------------------------------- *)
val _ = Datatype regexDatatypes.Reg_datatype_quot;

val language_of_def = Define `
         (language_of (Eps)        = {[]}                                                       ) /\
	 (language_of (Sym (c:'a)) = {[c]}                                                      ) /\
	 (language_of (Alt r1 r2)  = { w      | w IN (language_of r1) \/ w IN (language_of r2) }) /\
	 (language_of (Seq r1 r2)  = { u ++ v | u IN (language_of r1) /\ v IN (language_of r2) }) /\
         (language_of (Rep r)      = { FLAT l | EVERY (\w. w IN (language_of r)) l }            )
`;




(* rewrite theorems *)
(* ----------------------------------------------------------------------------- *)
val language_of_DEFs = store_thm ("language_of_DEFs", ``
         (        language_of (Eps)        = {[]}                                                       ) /\
	 (!c.     language_of (Sym c)      = {[c]}                                                      ) /\
	 (!r1 r2. language_of (Alt r1 r2)  = { w      | w IN (language_of r1) \/ w IN (language_of r2) }) /\
	 (!r1 r2. language_of (Seq r1 r2)  = { u ++ v | u IN (language_of r1) /\ v IN (language_of r2) }) /\
         (!r.     language_of (Rep r)      = { FLAT l | EVERY (\w. w IN (language_of r)) l }            )
``,

  REWRITE_TAC [language_of_def]
);




(* sanity check and helper lemmata *)
(* ----------------------------------------------------------------------------- *)
val language_of_Alt_OR = store_thm ("language_of_Alt_OR", ``
	 (!w r1 r2. w IN language_of (Alt r1 r2) <=> w IN language_of r1 \/ w IN language_of r2)
``,

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [language_of_DEFs, pred_setTheory.IN_UNION]
);

(* val IN_GSPEC_IFF_GEN = Q.GENL [`P`, `y`] pred_setTheory.IN_GSPEC_IFF; *)
val language_of_Seq_APPEND = store_thm ("language_of_Seq_APPEND", ``
	 (!u v r1 r2. (u IN language_of r1 /\ v IN language_of r2) ==> (u ++ v) IN language_of (Seq r1 r2))
``,

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [language_of_DEFs] >>
  METIS_TAC []
);

val language_of_Rep_empty = store_thm ("language_of_Rep_empty", ``
	 (!r. [] IN language_of (Rep r))
``,

  SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [language_of_DEFs] >>
  GEN_TAC >> Q.EXISTS_TAC `[]` >>
  SIMP_TAC list_ss []
);

(* ok, but not quite all - just 2 *)
val language_of_Rep_APPEND2 = store_thm ("language_of_Rep_APPEND2", ``
	 (!u v r. (u IN language_of r /\ v IN language_of r) ==> (u ++ v) IN language_of (Rep r))
``,

  REPEAT STRIP_TAC >>
  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [language_of_DEFs] >>
  Q.EXISTS_TAC `[u;v]` >>
  ASM_SIMP_TAC list_ss []
);

val language_of_Rep_APPEND_rec = store_thm ("language_of_Rep_APPEND_rec", ``
	 (!u v r. (u IN language_of (Rep r) /\ v IN language_of (Rep r)) ==> (u ++ v) IN language_of (Rep r))
``,

  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (bool_ss++pred_setSimps.PRED_SET_ss) [language_of_DEFs, GSYM rich_listTheory.FLAT_FOLDL] >>
  rename1 `FLAT l1 ++ FLAT l2` >>

  Q.LIST_EXISTS_TAC [`l1++l2`] >>
  ASM_SIMP_TAC list_ss []
);










val _ = export_theory();
