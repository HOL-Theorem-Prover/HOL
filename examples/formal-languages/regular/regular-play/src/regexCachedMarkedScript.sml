open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory combinTheory;
open pred_setTheory;

val _ = new_theory "regexCachedMarked";


open regexSemanticsTheory;
open regexExecutableTheory;
open regexMarkedTheory;



(* definitions *)
(* ----------------------------------------------------------------------------- *)
val _ = Datatype regexDatatypes.CMReg_datatype_quot;

(* this could possibly part of the theory file *)
val CMReg_rws = type_rws ``:'a CMReg``;
val CMReg_rw  = LIST_CONJ CMReg_rws;
val CMReg_ss  = rewrites CMReg_rws;


val cempty_def = Define `
         (cempty (CMEps)         = T) /\
         (cempty (CMSym _ _)     = F) /\
         (cempty (CMAlt e _ _ _) = e) /\
         (cempty (CMSeq e _ _ _) = e) /\
         (cempty (CMRep   _ _)   = T)
`;

val cfinal_def = Define `
         (cfinal (CMEps)         = F) /\
         (cfinal (CMSym b _)     = b) /\
         (cfinal (CMAlt _ f _ _) = f) /\
         (cfinal (CMSeq _ f _ _) = f) /\
         (cfinal (CMRep   f _)   = f)
`;

val cmEps_def = Define `
         (cmEps     = CMEps)
`;
val cmSym_def = Define `
         (cmSym b c = CMSym b c)
`;
val cmAlt_def = Define `
         (cmAlt p q = CMAlt ((cempty p) \/ (cempty q)) ((cfinal p) \/ (cfinal q)) p q)
`;
val cmSeq_def = Define `
         (cmSeq p q = CMSeq ((cempty p) /\ (cempty q)) (((cfinal p) /\ (cempty q)) \/ (cfinal q)) p q)
`;
val cmRep_def = Define `
         (cmRep r   = CMRep (cfinal r) r)
`;



val CACHE_REG_def = Define `
         (CACHE_REG (MEps)          = cmEps                            ) /\
         (CACHE_REG (MSym b (c:'a)) = cmSym b c                        ) /\
         (CACHE_REG (MAlt p q)      = cmAlt (CACHE_REG p) (CACHE_REG q)) /\
         (CACHE_REG (MSeq p q)      = cmSeq (CACHE_REG p) (CACHE_REG q)) /\
         (CACHE_REG (MRep r)        = cmRep (CACHE_REG r)              )
`;

val UNCACHE_REG_def = Define `
         (UNCACHE_REG (CMEps)            = MEps                                ) /\
         (UNCACHE_REG (CMSym b (c:'a))   = MSym b c                            ) /\
         (UNCACHE_REG (CMAlt _ _ p q)    = MAlt (UNCACHE_REG p) (UNCACHE_REG q)) /\
         (UNCACHE_REG (CMSeq _ _ p q)    = MSeq (UNCACHE_REG p) (UNCACHE_REG q)) /\
         (UNCACHE_REG (CMRep   _ r)      = MRep (UNCACHE_REG r)                )
`;



val cshift_def = Define `
         (cshift _ (CMEps)            _ = cmEps                                                            ) /\
         (cshift m (CMSym _ (x:'a))   c = cmSym (m /\ (x = c)) x                                           ) /\
         (cshift m (CMAlt _ _ p q)    c = cmAlt (cshift m p c) (cshift m q c)                              ) /\
         (cshift m (CMSeq _ _ p q)    c = cmSeq (cshift m p c) (cshift ((m /\ (cempty p)) \/ cfinal p) q c)) /\
         (cshift m (CMRep   _ r)      c = cmRep (cshift (m \/ (cfinal r)) r c)                             )
`;



val acceptCM_def = Define `
         (acceptCM r []           = cempty r                                   ) /\
         (acceptCM r ((c:'a)::cs) = cfinal (FOLDL (cshift F) (cshift T r c) cs))
`;












(* rewrite theorems *)
(* ----------------------------------------------------------------------------- *)
(* rewrites for cempty and cfinal *)
val cempty_DEF = store_thm ("cempty_DEF", ``
         (          cempty (CMEps)         = T) /\
         (!b c.     cempty (CMSym b c)     = F) /\
         (!e f p q. cempty (CMAlt e f p q) = e) /\
         (!e f p q. cempty (CMSeq e f p q) = e) /\
         (!  f r.   cempty (CMRep   f r)   = T)
``,

  REWRITE_TAC [cempty_def]
);
val cfinal_DEF = store_thm ("cfinal_DEF", ``
         (          cfinal (CMEps)         = F) /\
         (!b c.     cfinal (CMSym b c)     = b) /\
         (!e f p q. cfinal (CMAlt e f p q) = f) /\
         (!e f p q. cfinal (CMSeq e f p q) = f) /\
         (!  f r.   cfinal (CMRep   f r)   = f)
``,

  REWRITE_TAC [cfinal_def]
);

(* rewrites for cmEps, cmSym, cmAlt, cmSeq, and cmRep *)
val cmX_DEF = store_thm ("cmX_DEF", ``
         (      cmEps     = CMEps                                                                          ) /\
         (!b c. cmSym b c = CMSym b c                                                                      ) /\
         (!p q. cmAlt p q = CMAlt ((cempty p) \/ (cempty q)) ((cfinal p) \/ (cfinal q)) p q                ) /\
         (!p q. cmSeq p q = CMSeq ((cempty p) /\ (cempty q)) (((cfinal p) /\ (cempty q)) \/ (cfinal q)) p q) /\
         (!r.   cmRep r   = CMRep (cfinal r) r                                                             )
``,

  REWRITE_TAC [cmEps_def, cmSym_def, cmAlt_def, cmSeq_def, cmRep_def]
);

(* rewrites for CACHE_REG and UNCACHE_REG *)
val CACHE_REG_DEF = store_thm ("CACHE_REG_DEF", ``
         (      CACHE_REG (MEps)          = cmEps                            ) /\
         (!b c. CACHE_REG (MSym b (c:'a)) = cmSym b c                        ) /\
         (!p q. CACHE_REG (MAlt p q)      = cmAlt (CACHE_REG p) (CACHE_REG q)) /\
         (!p q. CACHE_REG (MSeq p q)      = cmSeq (CACHE_REG p) (CACHE_REG q)) /\
         (!r.   CACHE_REG (MRep r)        = cmRep (CACHE_REG r)              )
``,

  REWRITE_TAC [CACHE_REG_def]
);
val UNCACHE_REG_DEF = store_thm ("UNCACHE_REG_DEF", ``
         (        UNCACHE_REG (CMEps)              = MEps                                ) /\
         (!b c.   UNCACHE_REG (CMSym b (c:'a))     = MSym b c                            ) /\
         (!e f p q. UNCACHE_REG (CMAlt e f p q)    = MAlt (UNCACHE_REG p) (UNCACHE_REG q)) /\
         (!e f p q. UNCACHE_REG (CMSeq e f p q)    = MSeq (UNCACHE_REG p) (UNCACHE_REG q)) /\
         (!  f r.   UNCACHE_REG (CMRep   f r)      = MRep (UNCACHE_REG r)                )
``,

  REWRITE_TAC [UNCACHE_REG_def]
);

(* rewrites for cshift *)
val cshift_DEF = store_thm ("cshift_DEF", ``
         (!m c.         cshift m (CMEps)            c = cmEps                                                            ) /\
         (!m b x c.     cshift m (CMSym b (x:'a))   c = cmSym (m /\ (x = c)) x                                           ) /\
         (!m e f p q c. cshift m (CMAlt e f p q)    c = cmAlt (cshift m p c) (cshift m q c)                              ) /\
         (!m e f p q c. cshift m (CMSeq e f p q)    c = cmSeq (cshift m p c) (cshift ((m /\ (cempty p)) \/ cfinal p) q c)) /\
         (!m   f r c.   cshift m (CMRep   f r)      c = cmRep (cshift (m \/ (cfinal r)) r c)                             )
``,

  REWRITE_TAC [cshift_def]
);

(* rewrites for acceptCM *)
val acceptCM_DEF = store_thm ("acceptCM_DEF", ``
         (!r.      acceptCM r []           = cempty r                                   ) /\
         (!r c cs. acceptCM r ((c:'a)::cs) = cfinal (FOLDL (cshift F) (cshift T r c) cs))
``,

  REWRITE_TAC [acceptCM_def]
);











(* helper definitions *)
(* ----------------------------------------------------------------------------- *)
val CMREG_SUBEXP_def = Define `
         (CMREG_SUBEXP s (CMEps)         = F                                                             ) /\
         (CMREG_SUBEXP s (CMSym _ _)     = F                                                             ) /\
         (CMREG_SUBEXP s (CMAlt _ _ p q) = (s = p) \/ (s = q) \/ (CMREG_SUBEXP s p) \/ (CMREG_SUBEXP s q)) /\
         (CMREG_SUBEXP s (CMSeq _ _ p q) = (s = p) \/ (s = q) \/ (CMREG_SUBEXP s p) \/ (CMREG_SUBEXP s q)) /\
         (CMREG_SUBEXP s (CMRep   _ r)   = (s = r) \/ (CMREG_SUBEXP s r)                                 )
`;

(*
val CMREG_WELLFORMED_SUB_def = Define `
         (CMREG_WELLFORMED_SUB r = !s. ((s = r) \/ CMREG_SUBEXP s r) ==> 
             ((cempty s = (empty (UNCACHE_REG s))) /\ (cfinal s = (final (UNCACHE_REG s))))
         )
`;
*)

val CMREG_WELLFORMED_def = Define `
         (CMREG_WELLFORMED (CMEps)         = T                                                             ) /\
         (CMREG_WELLFORMED (CMSym _ _)     = T                                                             ) /\
         (CMREG_WELLFORMED (CMAlt e f p q) = (e = empty (UNCACHE_REG p) \/ empty (UNCACHE_REG q)) /\ (f = final (UNCACHE_REG p) \/ final (UNCACHE_REG q)) /\ CMREG_WELLFORMED p /\ CMREG_WELLFORMED q) /\
         (CMREG_WELLFORMED (CMSeq e f p q) = (e = empty (UNCACHE_REG p) /\ empty (UNCACHE_REG q)) /\ (f = (final (UNCACHE_REG p) /\ empty (UNCACHE_REG q)) \/ final (UNCACHE_REG q)) /\ CMREG_WELLFORMED p /\ CMREG_WELLFORMED q) /\
         (CMREG_WELLFORMED (CMRep   f r)   = (f = final (UNCACHE_REG r)) /\ CMREG_WELLFORMED r)
`;


val CMREG_SUBEXP_WELLFORMED_thm = store_thm ("CMREG_SUBEXP_WELLFORMED_thm", ``
         (!cmr s. (CMREG_WELLFORMED cmr) ==> (CMREG_SUBEXP s cmr) ==> (CMREG_WELLFORMED s))
``,

  Induct_on `cmr` >> (
    ASM_REWRITE_TAC [CMREG_WELLFORMED_def, CMREG_SUBEXP_def] >>
    METIS_TAC [CMREG_WELLFORMED_def, CMREG_SUBEXP_def]
  )
);










(* sanity and helper lemmata *)
(* ----------------------------------------------------------------------------- *)
(*
- CACHE/UNCACHE are inverse and wellformedness is established by CACHE_REG
- cshift preserves wellformedness and "has the same effect as shift", i.e. the cmX functions preserve wellformedness
- assuming a WELLFORMED&UNMARKED cmr, acceptCM does the same as acceptM
*)


(* CACHE/UNCACHE inverses and wellformedness *)
val CACHE_UNCACHE_thm = store_thm ("CACHE_UNCACHE_thm", ``
         (!mr. (UNCACHE_REG (CACHE_REG mr)) = mr)
``,

  Induct_on `mr` >> (
    ASM_REWRITE_TAC [CACHE_REG_DEF, cmX_DEF, UNCACHE_REG_DEF]
  )
);

val WELLFORMED_cempty_thm = store_thm ("WELLFORMED_cempty_thm", ``
         (!cmr. (CMREG_WELLFORMED cmr) ==> ((cempty cmr) = empty (UNCACHE_REG cmr)))
``,

  Induct_on `cmr` >> (
    METIS_TAC [CMREG_WELLFORMED_def, cempty_DEF, empty_DEFs, UNCACHE_REG_DEF]
  )
);

val WELLFORMED_cfinal_thm = store_thm ("WELLFORMED_cfinal_thm", ``
         (!cmr. (CMREG_WELLFORMED cmr) ==> ((cfinal cmr) = final (UNCACHE_REG cmr)))
``,

  Induct_on `cmr` >> (
    METIS_TAC [CMREG_WELLFORMED_def, cfinal_DEF, final_DEFs, UNCACHE_REG_DEF]
  )
);

val UNCACHE_CACHE_thm = store_thm ("UNCACHE_CACHE_thm", ``
         (!cmr. (CMREG_WELLFORMED cmr) ==> ((CACHE_REG (UNCACHE_REG cmr)) = cmr))
``,

  Induct_on `cmr` >> (
    ASM_SIMP_TAC (std_ss++CMReg_ss) [UNCACHE_REG_DEF, CACHE_REG_DEF, cmX_DEF] >>
    METIS_TAC [CMREG_WELLFORMED_def, WELLFORMED_cempty_thm, WELLFORMED_cfinal_thm]
  )
);

val CACHE_REG_WELLFORMED_thm = store_thm ("CACHE_REG_WELLFORMED_thm", ``
         (!mr. CMREG_WELLFORMED (CACHE_REG mr))
``,

  Induct_on `mr` >> (
    ASM_REWRITE_TAC [CACHE_REG_DEF, cmX_DEF, CMREG_WELLFORMED_def] >>
    METIS_TAC [CMREG_WELLFORMED_def, WELLFORMED_cempty_thm, WELLFORMED_cfinal_thm]
  )
);


(* cshift preserves wellformedness, and relation to shift *)
val WELLFORMED_INV_and_cshift_shift_thm = store_thm ("WELLFORMED_INV_and_cshift_shift_thm", ``
         (!cmr m c. (CMREG_WELLFORMED cmr) ==> (
                                    (CMREG_WELLFORMED (cshift m cmr c)) /\
                                    ((shift m (UNCACHE_REG cmr) c) = (UNCACHE_REG (cshift m cmr c)))
         ))
``,

  Induct_on `cmr` >> (
    ASM_REWRITE_TAC [UNCACHE_REG_DEF, shift_DEFs, cshift_DEF, cmX_DEF, CMREG_WELLFORMED_def] >>
    ASM_SIMP_TAC (std_ss) [CMREG_WELLFORMED_def, WELLFORMED_cempty_thm, WELLFORMED_cfinal_thm]
  )
);

(* acceptCM, relation to accept, if WELLFORMED&UNMARKED cmr *)
val WELLFORMED_INV_and_FOLDL_cshift_shift_thm = store_thm ("WELLFORMED_INV_and_FOLDL_cshift_shift_thm", ``
         (!cmr m cs. (CMREG_WELLFORMED cmr) ==> (
                                    (CMREG_WELLFORMED (FOLDL (cshift m) cmr cs)) /\
                                    ((FOLDL (shift m) (UNCACHE_REG cmr) cs) = (UNCACHE_REG (FOLDL (cshift m) cmr cs)))
         ))
``,

  Induct_on `cs` >> (
    ASM_SIMP_TAC list_ss [WELLFORMED_INV_and_cshift_shift_thm]
  )
);

val WELLFORMED_acceptCM_acceptM_thm = store_thm ("WELLFORMED_acceptCM_acceptM_thm", ``
         (!cmr w. (CMREG_WELLFORMED cmr) ==> ((acceptCM cmr w) <=> (acceptM (UNCACHE_REG cmr) w)))
``,

  Cases_on `w` >> (
    REWRITE_TAC [acceptM_DEFs, acceptCM_DEF, WELLFORMED_cempty_thm] >>
    METIS_TAC [WELLFORMED_INV_and_cshift_shift_thm, WELLFORMED_INV_and_FOLDL_cshift_shift_thm, WELLFORMED_cfinal_thm]
  )
);









(* correctness of definition *)
(* ----------------------------------------------------------------------------- *)
val acceptCM_acceptM_thm = store_thm("acceptCM_acceptM_thm", ``!mr w. acceptCM (CACHE_REG mr) w <=> acceptM mr w``,

  METIS_TAC [WELLFORMED_acceptCM_acceptM_thm, CACHE_UNCACHE_thm, CACHE_REG_WELLFORMED_thm]
);

val acceptM_correctness_thm = store_thm("acceptM_correctness_thm", ``!r w. acceptCM (CACHE_REG (MARK_REG r)) w <=> w IN (language_of r)``,

  REWRITE_TAC [acceptCM_acceptM_thm, acceptM_accept_thm, accept_correctness_thm]
);






val _ = export_theory();
