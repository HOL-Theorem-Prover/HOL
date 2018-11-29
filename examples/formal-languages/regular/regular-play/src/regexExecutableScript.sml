open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory combinTheory;
open pred_setTheory;

val _ = new_theory "regexExecutable";

open regexSemanticsTheory;


(* 3.2 executable semantics *)
(* -------------------------------------------------------------------------------------------------- *)

(* here, we use the datatype from regexDatatypes.Reg_datatype_quot *)

val split_def = Define `
         (split []      = [([],[])]                                            ) /\
         (split (c::cs) = ([],c::cs)::(MAP (\s. (c::(FST s),SND s)) (split cs)))
`;

val parts_def = Define `
         (parts []      = [[]]                                                                      ) /\
         (parts [c]     = [[[c]]]                                                                   ) /\
         (parts (c::cs) = FLAT (MAP (\ps. [(c::(HD ps))::(TL ps);[c]::(HD ps)::(TL ps)]) (parts cs)))
`;

val accept_def = Define `
         (accept (Eps) u     = (u = [])                                                            ) /\
         (accept (Sym c) u   = (u = [c])                                                           ) /\
         (accept (Alt p q) u = accept p u \/ accept q u                                            ) /\
         (accept (Seq p q) u = EXISTS (\u_12. accept p (FST u_12) /\ accept q (SND u_12)) (split u)) /\
         (accept (Rep r) u   = EXISTS (\ps. EVERY (\u_i. accept r u_i) ps) (parts u)               )
`;













(* rewrite theorems *)
(* ----------------------------------------------------------------------------- *)
val split_DEFs = store_thm ("split_DEFs", ``
         (       split []      = [([],[])]                                            ) /\
         (!c cs. split (c::cs) = ([],c::cs)::(MAP (\s. (c::(FST s),SND s)) (split cs)))
``,

  REWRITE_TAC [split_def]
);

val parts_DEFs = store_thm ("parts_DEFs", ``
         (                        parts []      = [[]]                                                                      ) /\
         (!c.                     parts [c]     = [[[c]]]                                                                   ) /\
         (!c1 c2 cs. parts (c1::c2::cs) = FLAT (MAP (\ps. [(c1::(HD ps))::(TL ps);[c1]::(HD ps)::(TL ps)]) (parts (c2::cs))))
``,

  REWRITE_TAC [parts_def]
);

val accept_DEFs = store_thm ("accept_DEFs", ``
         (!u.     accept (Eps) u     = (u = [])                                                            ) /\
         (!c u.   accept (Sym c) u   = (u = [c])                                                           ) /\
         (!p q u. accept (Alt p q) u = accept p u \/ accept q u                                            ) /\
         (!p q u. accept (Seq p q) u = EXISTS (\u_12. accept p (FST u_12) /\ accept q (SND u_12)) (split u)) /\
         (!r u.   accept (Rep r) u   = EXISTS (\ps. EVERY (\u_i. accept r u_i) ps) (parts u)               )
``,

  REWRITE_TAC [accept_def]
);






(* sanity and helper lemmata *)
(* ----------------------------------------------------------------------------- *)
val split_APPEND_thm = store_thm ("split_APPEND_thm", ``
         (!w u v. (MEM (u, v) (split w)) <=> (w = u ++ v))
``,

  Induct_on `w` >> (
    SIMP_TAC list_ss [split_DEFs, MEM_MAP] >>

    Cases_on `u` >> (
      ASM_SIMP_TAC (list_ss++QI_ss++boolSimps.EQUIV_EXTRACT_ss) []
    )
  )
);

(*
val parts_DEF_c_alt_thm = Ho_Rewrite.REWRITE_RULE [concat_DEF, FLAT_FOLDL, FOLDL_MAP, boolTheory.BETA_THM] parts_DEF_c;
*)

val parts_FLAT_thm = store_thm ("parts_FLAT_thm", ``
         (!w l. (MEM l (parts w)) <=> ((w = FLAT l) /\ (~MEM [] l)))
``,

  Cases_on `w` >- (
    SIMP_TAC (list_ss) [parts_DEFs, FLAT_EQ_NIL, boolTheory.EQ_IMP_THM] >>

    REPEAT STRIP_TAC >>
    Cases_on `l` >> (
      FULL_SIMP_TAC (list_ss) []
    )
  ) >>

  Q.ID_SPEC_TAC `h` >> Q.ID_SPEC_TAC `t` >>
  Induct_on `t` >- (
    SIMP_TAC (list_ss) [parts_DEFs, FLAT_EQ_NIL, boolTheory.EQ_IMP_THM] >>

    REPEAT STRIP_TAC >>
    Cases_on `l` >- FULL_SIMP_TAC (list_ss) [] >>

    FULL_SIMP_TAC (list_ss) [] >>
    Cases_on `h'` >- FULL_SIMP_TAC (list_ss) [] >>

    FULL_SIMP_TAC (list_ss) [] >>
    Cases_on `t` >- REWRITE_TAC [] >>
    FULL_SIMP_TAC (list_ss) []
  ) >>

  ASM_SIMP_TAC (list_ss) [parts_DEFs, MEM_FLAT, MEM_MAP] >>
  POP_ASSUM (K ALL_TAC) >>

  REPEAT STRIP_TAC >>
  Ho_Rewrite.REWRITE_TAC [boolTheory.PULL_EXISTS] >>
  rename1 `(h1::h2::t = FLAT l)` >>

  SIMP_TAC (list_ss++QI_ss) [boolTheory.EQ_IMP_THM] >>
  STRIP_TAC >- (
    REPEAT STRIP_TAC >> (
      Cases_on `ps` >> REV_FULL_SIMP_TAC list_ss []
    )
  ) >>

  STRIP_TAC >>

  Cases_on `l` >- FULL_SIMP_TAC list_ss [] >>
  rename1 `h1::h2::t = FLAT (hl::tl)` >>

  Cases_on `hl = [h1]` >- (
    Q.EXISTS_TAC `(HD tl)::(TL tl)` >>
    Cases_on `tl` >> FULL_SIMP_TAC list_ss []
  ) >>

  Cases_on `hl` >- FULL_SIMP_TAC list_ss [] >>
  rename1 `h1::h2::t = FLAT ((hlh::hlt)::tl)` >>

  Cases_on `hlt` >- FULL_SIMP_TAC list_ss [] >>
  rename1 `h1::h2::t = FLAT ((hlh1::hlh2::hlt)::tl)` >>

  Q.EXISTS_TAC `(h2::hlt)::tl` >>
  FULL_SIMP_TAC list_ss []
);


(*
fun POP_N_ASSUM_TOP_tac n =
    POP_ASSUM_LIST (fn al => (List.foldl (fn (thm,tac) => ASSUME_TAC thm >> tac) ALL_TAC (List.take (al, (List.length al) - n))))
;
*)

val FLAT_NIL_thm = prove(``
         (!l. (~MEM [] l) ==> (FLAT l = []) ==> (l = []))
``,

  Cases_on `l` >> FULL_SIMP_TAC list_ss [FLAT_EQ_NIL]
);

val FLAT_SINGLE_thm = prove(``
         (!l c. (~MEM [] l) ==> (FLAT l = [c]) ==> (l = [[c]]))
``,

  Cases_on `l` >- FULL_SIMP_TAC list_ss [] >>

  Cases_on `h` >> FULL_SIMP_TAC list_ss [FLAT_NIL_thm]
);

val FLAT_FILTER_EMPTY_thm = store_thm ("FLAT_FILTER_EMPTY_thm", ``
         (!l. (FLAT (FILTER (\x. x <> []) l)) = (FLAT l))
``,

  Induct_on `l` >- SIMP_TAC list_ss [] >>

  Cases_on `h` >> ASM_SIMP_TAC list_ss [FILTER, FLAT]
);

val FILTER_NIL_NONIL_thm = prove (``
         (!l m. (l = (FILTER (\x. x <> []) m)) ==> (~MEM [] l))
``,

  Induct_on `m` >- SIMP_TAC list_ss [] >>

  Cases_on `h` >> ASM_SIMP_TAC list_ss []
);

val NONIL_FILTER_NIL_EQ_thm = prove (``
         (!l. (~MEM [] l) ==> (l = (FILTER (\x. x <> []) l)))
``,

  Induct >> FULL_SIMP_TAC list_ss []
);

val parts_FLAT_FILTER_EMPTY_thm = prove(``
         (!l m. (l = (FILTER (\x. x <> []) m)) ==> (MEM l (parts (FLAT l))))
``,

  METIS_TAC [FLAT_FILTER_EMPTY_thm, FILTER_NIL_NONIL_thm, NONIL_FILTER_NIL_EQ_thm, parts_FLAT_thm]
);

val APPEND_parts_EMPTY_thm = store_thm ("APPEND_parts_EMPTY_thm", ``
         (!l. MEM (FILTER (\x. x <> []) l) (parts (FLAT l)))
``,

  SIMP_TAC (pure_ss++QI_ss) [parts_FLAT_FILTER_EMPTY_thm, Once (GSYM FLAT_FILTER_EMPTY_thm)]
);









(* correctness of definition *)
(* ----------------------------------------------------------------------------- *)
val accept_correctness_thm = store_thm("accept_correctness_thm", ``!r w. accept r w <=> w IN (language_of r)``,

  Induct_on `r` >> (
    ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++QI_ss) [accept_DEFs, language_of_DEFs, GSYM split_APPEND_thm, parts_FLAT_thm, EXISTS_MEM, EVERY_MEM]
  ) >>

  (* case with Rep regex *)
  POP_ASSUM (K ALL_TAC) >>

  REWRITE_TAC [boolTheory.EQ_IMP_THM] >>
  REPEAT STRIP_TAC >- (
    Q.EXISTS_TAC `ps` >> ASM_REWRITE_TAC []
  ) >>

  Q.EXISTS_TAC `(FILTER (\x. x <> []) l)` >>
  ASM_SIMP_TAC list_ss [FLAT_FILTER_EMPTY_thm, MEM_FILTER]
);





val _ = export_theory();
