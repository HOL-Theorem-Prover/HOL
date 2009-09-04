(* interactive use:

quietdec := true;
loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: !loadPath;

app load ["pred_setSimps","pred_setTheory","whileTheory","finite_mapTheory","rich_listTheory","prim_recTheory", "wordsTheory", "wordsLib", "preARMTheory"];

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory wordsLib
     arithmeticTheory wordsTheory pairTheory listTheory whileTheory finite_mapTheory preARMTheory;

val _ = new_theory "ARMComposition";

val _ = Globals.priming := NONE;

(*------------------------------------------------------------------------------------------------------*)
(* Additional theorems for finite maps                                                                  *)
(*------------------------------------------------------------------------------------------------------*)


val fupdate_normalizer =
 let val thm = SPEC_ALL FUPDATE_LT_COMMUTES
     val pat = lhs(snd(dest_imp(concl thm)))
 in
   {name = "Finite map normalization",
    trace = 2,
    key = SOME([],pat),
    conv = let fun reducer tm =
                 let val (theta,ty_theta) = match_term pat tm
                     val thm' = INST theta (INST_TYPE ty_theta thm)
                     val constraint = fst(dest_imp(concl thm'))
                     val cthm = EQT_ELIM(reduceLib.REDUCE_CONV constraint)
                 in MP thm' cthm
                 end
           in
               K (K reducer)
           end}
 end;

val finmap_conv_frag =
 simpLib.SSFRAG
     {convs = [fupdate_normalizer],
      rewrs = [], ac=[],filter=NONE,dprocs=[],congs=[]};

val finmap_ss = bossLib.std_ss ++ finmap_conv_frag
                               ++ rewrites [FUPDATE_EQ, FAPPLY_FUPDATE_THM];

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*      termination                                                                *)
(*---------------------------------------------------------------------------------*)

val terminated = Define `
   terminated arm =
     !(s:STATEPCS) iB.
	   stopAt (\s':STATEPCS. FST (FST s') = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s`;

val TERMINATED_THM = Q.store_thm (
   "TERMINATED_THM",
   `!arm. terminated arm ==>
        !s iB. FST (FST (runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s)) = FST (FST s) + LENGTH arm`,
   RW_TAC std_ss [terminated, UNROLL_RUNTO] THEN
   METIS_TAC [Q.SPECL [`s:STATEPCS`, `\s':STATEPCS. FST (FST s') = FST (FST (s:STATEPCS)) + LENGTH arm`,
		       `step (upload arm iB (FST (FST (s:STATEPCS))))`] (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_STOP)]
   );

(*---------------------------------------------------------------------------------*)
(*      Closed segment of codes                                                    *)
(*---------------------------------------------------------------------------------*)

val closed = Define `
    closed arm =
        !s iB. (!x. x IN SND (runTo (upload arm iB (FST s)) (FST s + LENGTH arm) (s,({}))) ==> FST s <= x /\ x < FST s + LENGTH arm)`;

val CLOSED_THM = Q.store_thm (
   "CLOSED_THM",
   `!m arm s iB pos. closed arm ==>
          stopAt  (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s /\
          m < shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s
          ==>
          FST (FST s) <= FST (FST (FUNPOW (step (upload arm iB (FST (FST s)))) m s)) /\
	  FST (FST (FUNPOW (step (upload arm iB (FST (FST s)))) m s)) < FST (FST s) + LENGTH arm
   `,
   REPEAT GEN_TAC THEN
   `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [closed] THEN
   NTAC 2 STRIP_TAC THEN
   Q.PAT_ASSUM `!s iB x.p` (MP_TAC o Q.SPECL [`s0`, `iB`, `FST (FST (FUNPOW (step (upload arm iB (FST s0))) m (s0,pcS0)))`]) THEN
   IMP_RES_TAC (Q.SPECL [`pcS0`, `{}`] STOPAT_ANY_PCS_2) THEN
   IMP_RES_TAC UNROLL_RUNTO THEN
   ASM_REWRITE_TAC [] THEN
   NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
   IMP_RES_TAC RUNTO_PCS_MEMBERS_2 THEN
   `shortest (\s'. FST (FST s') = FST s0 + LENGTH arm) (step (upload arm iB (FST s0))) (s0,pcS0) =
    shortest (\s'. FST (FST s') = FST s0 + LENGTH arm) (step (upload arm iB (FST s0))) (s0,{})`
        by METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`(s0,pcS0)`,`(s0,({}))`] SHORTEST_INDEPENDENT_OF_PCS)] THEN
   STRIP_TAC THEN
   METIS_TAC []
   );


(*---------------------------------------------------------------------------------*)
(*      Running of closed codes                                                    *)
(*---------------------------------------------------------------------------------*)

val CLOSED_MIDDLE_STEP_LEM = Q.store_thm (
   "CLOSED_MIDDLE_STEP_LEM",
   `!arm arm' arm'' pos iB pos (s:STATEPCS).
       (pos + LENGTH arm' <= FST (FST s)) /\ (FST (FST s) < pos + LENGTH arm' + LENGTH arm) ==>
           (step (upload (arm' ++ arm ++ arm'') iB pos) s = step (upload arm iB (pos + LENGTH arm')) s)`,
   RW_TAC std_ss [] THEN
   `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
   FULL_SIMP_TAC std_ss [step_def] THEN
   `?k. k < LENGTH arm /\ (FST s0 = pos + LENGTH arm' + k)` by (Q.EXISTS_TAC `FST s0 - pos - LENGTH arm'` THEN RW_TAC arith_ss []) THEN
   RW_TAC std_ss [] THEN
   `LENGTH arm' + k < LENGTH (arm' ++ arm ++ arm'')` by RW_TAC list_ss [] THEN
   IMP_RES_TAC UPLOAD_LEM THEN
   `EL (k + LENGTH arm') (arm' ++ arm ++ arm'') = EL k arm` by ALL_TAC THENL [
       NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
       Induct_on `arm'` THENL [
           RW_TAC list_ss [rich_listTheory.EL_APPEND1],
           RW_TAC list_ss [] THEN
           `k + SUC (LENGTH arm') = SUC (k + LENGTH arm')` by RW_TAC arith_ss [] THEN
           RW_TAC list_ss [rich_listTheory.EL_APPEND1, APPEND_ASSOC] THEN
           NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
           Induct_on `arm'` THENL [
               RW_TAC list_ss [],
               `k + SUC (LENGTH arm') = SUC (k + LENGTH arm')` by RW_TAC arith_ss [] THEN
               RW_TAC list_ss [rich_listTheory.EL_APPEND1]
           ]
        ],
    RW_TAC std_ss [] THEN
    METIS_TAC [ADD_ASSOC, ADD_SYM]
    ]
   );


val CLOSED_MIDDLE_LEM = Q.store_thm (
   "CLOSED_MIDDLE_LEM",
   `!arm arm' arm'' pos iB (s:STATEPCS) s'.
	   closed arm /\ terminated arm /\ (pos + LENGTH arm' = FST (FST s)) /\ (instB = upload arm iB (FST (FST s))) /\
           (?m. (s' = FUNPOW (step instB) m (s)) /\ m <= shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s)
            ==>
	       (runTo (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) s' =
		    runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s')`,

   RW_TAC std_ss [] THEN
   Q.ABBREV_TAC `instB = upload arm iB (FST (FST s))` THEN
   Cases_on `m = shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` THENL [
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [STOPAT_THM, terminated] THEN
           `FST (FST (FUNPOW (step instB) m s)) = FST (FST s) + LENGTH arm` by ( FULL_SIMP_TAC std_ss [stopAt_def, shortest_def] THEN
           METIS_TAC [Q.SPEC `\n.FST (FST (FUNPOW (step instB) n s)) = FST (FST s) + LENGTH arm` LEAST_INTRO]) THEN
           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE] THEN
           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE],

       `m < shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
       Q.PAT_ASSUM `~p` (K ALL_TAC) THEN
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` by METIS_TAC [STOPAT_THM, terminated] THEN
       RW_TAC std_ss [UNROLL_RUNTO] THEN
       Induct_on `shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` THENL [
           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               Q.ABBREV_TAC `s' = FUNPOW (step instB) m s` THEN
	       `FST (FST s') = FST (FST s) + LENGTH arm` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) = FST (FST s) + LENGTH arm`]
							  (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)] THEN
               `?s0 pcS0. s' = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
	       METIS_TAC [RUNTO_ADVANCE, FST, SND],

           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               IMP_RES_TAC SHORTEST_INDUCTIVE THEN
               `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [terminated] THEN
               `SUC m <= shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
               `v + SUC m = shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [FUNPOW_SUC, ADD_SYM,
	           (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_THM)] THEN
               `step (upload (arm' ++ arm ++ arm'') iB pos) (FUNPOW (step instB) m s)  =
	             step instB (FUNPOW (step instB) m s)` by (Q.UNABBREV_TAC `instB` THEN
							       METIS_TAC [CLOSED_THM, CLOSED_MIDDLE_STEP_LEM]) THEN

               Cases_on `v` THENL [
	           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE, FUNPOW] THENL [
                       METIS_TAC [],
                       RW_TAC std_ss [Once RUNTO_EXPAND_ONCE, FUNPOW] THEN
                       Q.ABBREV_TAC `s' = step instB (FUNPOW (step instB) m s)` THEN
                       `(FST (FST s') = FST (FST s) + LENGTH arm)` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) =
			   FST (FST s) + LENGTH arm`] (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)]
                   ],

                   Q.PAT_ASSUM `!s.p` (ASSUME_TAC o SIMP_RULE std_ss [FUNPOW_SUC] o Q.SPECL [`s`,`arm`,`instB`,`SUC m`]) THEN
                   `SUC m < shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
                   RW_TAC std_ss [Once RUNTO_EXPAND_ONCE] THEN
                   METIS_TAC []
               ]
        ]
   ]
  );


val CLOSED_MIDDLE = Q.store_thm (
   "CLOSED_MIDDLE",
   `!arm arm' arm'' pos iB (s:STATEPCS).
	   closed arm /\ terminated arm /\ (pos + LENGTH arm' = FST (FST s)) ==>
	       (runTo (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) s =
		    runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s)`,
   REPEAT STRIP_TAC THEN
   `(?m. (FUNPOW (step (upload arm iB (FST (FST s)))) 0 s = FUNPOW (step (upload arm iB (FST (FST s)))) m s) /\
          m <= shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s) ==>
          (runTo (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) (FUNPOW (step (upload arm iB (FST (FST s)))) 0 s) =
           runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) (FUNPOW (step (upload arm iB (FST (FST s)))) 0 s))`
	      by METIS_TAC [(SIMP_RULE std_ss [] o Q.SPECL [`arm`,`arm'`,`arm''`,`pos`,`iB`,`s`,`FUNPOW (step instB) 0 s`] o
			     SIMP_RULE std_ss []) CLOSED_MIDDLE_LEM] THEN
    `0 <= shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s` by RW_TAC arith_ss [] THEN
   RES_TAC THEN
   METIS_TAC [FUNPOW]
  );


val CLOSED_PREFIX = Q.store_thm (
   "CLOSED_PREFIX",
   `!arm arm' pos iB (s:STATEPCS).
	   closed arm /\ terminated arm /\ (pos + LENGTH arm' = FST (FST s)) ==>
	       (runTo (upload (arm' ++ arm) iB pos) (FST (FST s) + LENGTH arm) s =
		    runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s)`,
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (Q.SPECL [`arm`,`arm'`,`[]`] CLOSED_MIDDLE) THEN
   FULL_SIMP_TAC list_ss []
  );


val CLOSED_SUFFIX = Q.store_thm (
   "CLOSED_SUFFIX",
   `!arm arm' iB instB (s:STATEPCS).
	   closed arm /\ terminated arm  ==>
	       (runTo (upload (arm ++ arm') iB (FST (FST s))) (FST (FST s) + LENGTH arm) s =
		    runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s)`,
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (Q.SPECL [`arm`,`[]`,`arm'`] CLOSED_MIDDLE) THEN
   FULL_SIMP_TAC list_ss []
  );

(*---------------------------------------------------------------------------------*)
(*      Terimination information of closed codes                                   *)
(*---------------------------------------------------------------------------------*)

val TERMINATED_MIDDLE_LEM = Q.store_thm (
   "TERMINATED_MIDDLE_LEM",
    `!arm arm' arm'' pos iB (s:STATEPCS) s'.
	   closed arm /\ terminated arm /\ (pos + LENGTH arm' = FST (FST s)) /\ (instB = upload arm iB (FST (FST s))) /\
           (?m. (s' = FUNPOW (step instB) m (s)) /\ m <= shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s)
         ==>
	 terd (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) s'`,

   RW_TAC std_ss [terd_def] THEN
   Q.ABBREV_TAC `instB = upload arm iB (FST (FST s))` THEN
   Cases_on `m = shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` THENL [
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [STOPAT_THM, terminated] THEN
       `FST (FST (FUNPOW (step instB) m s)) = FST (FST s) + LENGTH arm` by ( FULL_SIMP_TAC std_ss [stopAt_def, shortest_def] THEN
           METIS_TAC [Q.SPEC `\n.FST (FST (FUNPOW (step instB) n s)) = FST (FST s) + LENGTH arm` LEAST_INTRO]) THEN
           RW_TAC std_ss [stopAt_def] THEN
	   Q.EXISTS_TAC `0` THEN
           RW_TAC std_ss [FUNPOW],

       `m < shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
       Q.PAT_ASSUM `~p` (K ALL_TAC) THEN
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` by METIS_TAC [STOPAT_THM, terminated] THEN
       Induct_on `shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` THENL [
           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               Q.ABBREV_TAC `s' = FUNPOW (step instB) m s` THEN
	       `FST (FST s') = FST (FST s) + LENGTH arm` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) = FST (FST s) + LENGTH arm`]
							  (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)] THEN
               RW_TAC std_ss [stopAt_def] THEN
               Q.EXISTS_TAC `0` THEN
               RW_TAC std_ss [FUNPOW],

           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               IMP_RES_TAC SHORTEST_INDUCTIVE THEN
               `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [terminated] THEN
               `SUC m <= shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
               `v + SUC m = shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [FUNPOW_SUC, ADD_SYM,
	           (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_THM)] THEN
	       `step (upload (arm' ++ arm ++ arm'') iB pos) (FUNPOW (step instB) m s)  =
	             step instB (FUNPOW (step instB) m s)` by (Q.UNABBREV_TAC `instB` THEN
							       METIS_TAC [CLOSED_THM, CLOSED_MIDDLE_STEP_LEM]) THEN
               Cases_on `v` THENL [
	           RW_TAC std_ss [stopAt_def] THEN
                       Q.ABBREV_TAC `s' = step instB (FUNPOW (step instB) m s)` THEN
                       `(FST (FST s') = FST (FST s) + LENGTH arm)` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) =
			   FST (FST s) + LENGTH arm`] (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)] THEN
                       Q.EXISTS_TAC `SUC 0` THEN
                       RW_TAC std_ss [FUNPOW],

                   Q.PAT_ASSUM `!s.p` (ASSUME_TAC o SIMP_RULE std_ss [FUNPOW_SUC] o Q.SPECL [`s`,`arm`,`instB`,`SUC m`]) THEN
                       `SUC m < shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
                       RES_TAC THEN
                       FULL_SIMP_TAC std_ss [stopAt_def] THEN
                       Q.EXISTS_TAC `SUC n''''` THEN
                       RW_TAC std_ss [FUNPOW]
               ]
        ]
   ]
  );

val TERMINATED_MIDDLE = Q.store_thm (
   "TERMINATED_MIDDLE",
   `!arm arm' arm'' pos iB instB (s:STATEPCS).
	   closed arm /\ terminated arm /\ (pos + LENGTH arm' = FST (FST s)) ==>
               terd (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) s`,

    REPEAT STRIP_TAC THEN
    `(?m. (FUNPOW (step (upload arm iB (FST (FST s)))) 0 s = FUNPOW (step (upload arm iB (FST (FST s)))) m s) /\
          m <= shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s) ==>
          terd (upload (arm' ++ arm ++ arm'') iB pos) (FST (FST s) + LENGTH arm) (FUNPOW (step (upload arm iB (FST (FST s)))) 0 s)`
	      by METIS_TAC [(SIMP_RULE std_ss [] o Q.SPECL [`arm`,`arm'`,`arm''`,`pos`,`iB`,`s`,`FUNPOW (step (upload arm iB (FST (FST s)))) 0 s`] o
			     SIMP_RULE std_ss []) TERMINATED_MIDDLE_LEM] THEN
   `0 <= shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step (upload arm iB (FST (FST s)))) s` by RW_TAC arith_ss [] THEN
   RES_TAC THEN
   METIS_TAC [FUNPOW]
  );

(*---------------------------------------------------------------------------------*)
(*      Sequential Composition witin a context                                     *)
(*      arm' and arm'' represent the context                                       *)
(*---------------------------------------------------------------------------------*)

val CLOSED_SEQUENTIAL_COMPOSITION = Q.store_thm (
   "CLOSED_SEQUENTIAL_COMPOSITION",
   `!arm1 arm2 arm' arm'' pos iB (s:STATEPCS).
         closed arm1 /\ terminated arm1 /\ closed arm2 /\ terminated arm2 /\
         (pos + LENGTH arm' = FST (FST s)) /\ ~(FST (FST s) + LENGTH arm1 + LENGTH arm2 IN SND s) ==>
          stopAt (\s'. FST (FST s') = FST (FST s) + LENGTH arm1 + LENGTH arm2) (step (upload (arm' ++ arm1 ++ arm2 ++ arm'') iB pos)) s
          /\
         (runTo (upload (arm' ++ arm1 ++ arm2 ++ arm'') iB pos) (FST (FST s) + LENGTH arm1 + LENGTH arm2) s =
          runTo (upload arm2 iB (FST (FST s) + LENGTH arm1)) (FST (FST s) + LENGTH arm1 + LENGTH arm2)
	               (runTo (upload arm1 iB (FST (FST s))) (FST (FST s) + LENGTH arm1) s))`,

    NTAC 8 STRIP_TAC THEN
    Cases_on `LENGTH arm2 = 0` THENL [
        IMP_RES_TAC LENGTH_NIL THEN
            FULL_SIMP_TAC list_ss [CLOSED_MIDDLE] THEN
            Q.ABBREV_TAC `s' = runTo (upload arm1 iB (FST (FST s))) (FST (FST s) + LENGTH arm1) s` THEN
            `FST (FST s') = FST (FST s) + LENGTH arm1` by (Q.UNABBREV_TAC `s'` THEN METIS_TAC [TERMINATED_THM]) THEN
            RW_TAC list_ss [Once RUNTO_EXPAND_ONCE] THEN
            METIS_TAC [TERMINATED_MIDDLE, terd_def],

        Q.ABBREV_TAC `insts2 = arm2 ++ arm''` THEN
        `~(LENGTH insts2 = 0) /\ (arm' ++ arm1 ++ arm2 ++ arm'' = arm' ++ arm1 ++ insts2)` by
				      (Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [] THEN METIS_TAC [APPEND_ASSOC]) THEN
        ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
        `?s1 pcS1. (s1,pcS1) = runTo (upload (arm' ++ arm1 ++ insts2) iB pos) (FST (FST s) + LENGTH arm1) s` by METIS_TAC [ABS_PAIR_THM] THEN
        `~(FST (FST s) + LENGTH arm1 + LENGTH arm2 IN (FST (FST s) INSERT pcS1))` by ALL_TAC THENL [
            POP_ASSUM MP_TAC THEN
                RW_TAC std_ss [SIMP_RULE std_ss [] (Q.SPECL [`arm1`,`arm'`,`insts2`,`pos`,`iB`, `s:STATEPCS`] CLOSED_MIDDLE)] THEN
            `pcS1 = SND (runTo (upload arm1 iB (FST (FST (s:STATEPCS)))) (FST (FST s) + LENGTH arm1) ((FST s,{}):STATEPCS)) UNION SND s`  by METIS_TAC
		 [terminated, Q.SPEC `(FST (s:STATEPCS),SND s)` (INST_TYPE [alpha |-> Type`:STATEPCS`] RUNTO_PCS_UNION), SND, FST, ABS_PAIR_THM] THEN
            `!x. x IN SND (runTo (upload arm1 iB (FST (FST s))) (FST (FST s) + LENGTH arm1) (FST s,{})) ==>
			 FST (FST s) <= x /\ x < FST (FST s) + LENGTH arm1` by METIS_TAC [closed,FST] THEN
            Q.UNABBREV_TAC `insts2` THEN
            FULL_SIMP_TAC set_ss [] THEN FULL_SIMP_TAC arith_ss [] THEN
            STRIP_TAC THEN RES_TAC THEN
            FULL_SIMP_TAC arith_ss [],

        `terd (upload (arm' ++ arm1 ++ insts2) iB pos) (FST (FST s) + LENGTH arm1) (FST s,SND s) /\
            ((s1,pcS1) = runTo (upload (arm' ++ arm1 ++ insts2) iB pos) (FST (FST s) + LENGTH arm1) (FST s,SND s))`
                    by METIS_TAC [FST, SND, TERMINATED_MIDDLE, ABS_PAIR_THM] THEN
            IMP_RES_TAC RUNTO_COMPOSITION THEN
            FULL_SIMP_TAC std_ss [] THEN STRIP_TAC THENL [
                RW_TAC std_ss [stopAt_def] THEN
                Q.ABBREV_TAC `instB = upload (arm' ++ arm1 ++ insts2) iB pos` THEN
                Q.EXISTS_TAC `shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm1 + LENGTH arm2) (step instB) (s1,pcS1)  +
			      shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm1) (step instB) s` THEN
                RW_TAC std_ss [GSYM FUNPOW_FUNPOW] THEN
                FULL_SIMP_TAC std_ss [terd_def,
                  REWRITE_RULE [Once EQ_SYM_EQ] (Q.SPECL [`instB`,`FST (FST (s:STATEPCS)) + LENGTH arm1`, `s:STATEPCS`] (GSYM UNROLL_RUNTO))] THEN
                  Q.UNABBREV_TAC `instB` THEN
                  `runTo (upload arm1 iB (FST (FST s))) (FST (FST s) + LENGTH arm1) s = (s1,pcS1)` by
                         METIS_TAC [terd_def, FST, CLOSED_PAIR_EQ,CLOSED_MIDDLE] THEN
                  Q.PAT_ASSUM `(s1,pcS1) = x` (ASSUME_TAC o GSYM) THEN
                  FULL_SIMP_TAC std_ss [] THEN
                  Q.UNABBREV_TAC `insts2` THEN
                  REWRITE_TAC [APPEND_ASSOC, ADD_ASSOC] THEN
                  `pos + LENGTH (arm' ++ arm1) = FST (FST (s1,pcS1))` by METIS_TAC [TERMINATED_THM, FST, LENGTH_APPEND, ADD_ASSOC] THEN
                  `terd (upload (arm' ++ arm1 ++ arm2 ++ arm'') iB pos) (FST (FST s) + LENGTH arm1 + LENGTH arm2) (s1,pcS1)`
		               by METIS_TAC [FST, SND, TERMINATED_MIDDLE, ABS_PAIR_THM, LENGTH_APPEND, ADD_ASSOC] THEN
                  FULL_SIMP_TAC list_ss [terd_def, REWRITE_RULE [Once EQ_SYM_EQ] (Q.SPECL [`upload (arm' ++ arm1 ++ arm2 ++ arm'') iB pos`,
				`FST (FST (s:STATEPCS)) + LENGTH arm1 + LENGTH arm2`, `(s1,pcS1):STATEPCS`] (GSYM UNROLL_RUNTO))] THEN
                  FULL_SIMP_TAC std_ss [ADD_ASSOC] THEN
                  `runTo (upload (arm' ++ arm1 ++ arm2 ++ arm'') iB pos) (FST (FST s) + LENGTH arm1 + LENGTH arm2) (s1,pcS1) =
		      runTo (upload arm2 iB (FST s1)) (FST s1 + LENGTH arm2) (s1,pcS1)` by METIS_TAC [FST,
                       (REWRITE_RULE [ADD_ASSOC] o SIMP_RULE list_ss [])
                            (Q.SPECL [`arm2`,`arm' ++ arm1`,`arm''`, `pos`,`iB`,`(s1,pcS1):STATEPCS`] CLOSED_MIDDLE)] THEN
                  METIS_TAC [TERMINATED_THM],

                 POP_ASSUM (K ALL_TAC) THEN
                 POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
                 `runTo (upload arm1 iB (FST (FST s))) (FST (FST s) + LENGTH arm1) s = (s1,pcS1)` by METIS_TAC [FST, CLOSED_PAIR_EQ,CLOSED_MIDDLE] THEN
                 FULL_SIMP_TAC std_ss [] THEN
                 Q.UNABBREV_TAC `insts2` THEN
                 REWRITE_TAC [APPEND_ASSOC, ADD_ASSOC] THEN
                 `pos + LENGTH (arm' ++ arm1) = FST (FST (s1,pcS1))` by METIS_TAC [TERMINATED_THM, FST, LENGTH_APPEND, ADD_ASSOC] THEN
                 METIS_TAC [CLOSED_MIDDLE, FST, ADD_ASSOC, LENGTH_APPEND]
           ]
        ]
    ]
  );

(*---------------------------------------------------------------------------------*)
(*      pc- and cpsr-independent codes                                             *)
(*      The result data excluding the cpsr and pc is independent of pc and cpsr    *)
(*      of the source state                                                        *)
(*---------------------------------------------------------------------------------*)

val get_st = Define `
   get_st (s:STATEPCS) =
       SND (SND (FST s))`;

val status_independent = Define `
    status_independent arm =
        !st pos0 pos1 cpsr0 cpsr1 iB.
            get_st (runTo (upload arm iB pos0) (pos0 + LENGTH arm) ((pos0,cpsr0,st),({}))) =
            get_st (runTo (upload arm iB pos1) (pos1 + LENGTH arm) ((pos1,cpsr1,st),({})))`;

val _ = type_abbrev("DSTATE", Type`:(REGISTER |-> DATA) # (ADDR |-> DATA)`);


val DSTATE_IRRELEVANT_PCS = Q.store_thm
  ("DSTATE_IRRELEVANT_PCS",
  `!arm pcS0 pcS1 iB s.
            terminated arm ==>
            (get_st (runTo (upload arm iB (FST s)) (FST s + LENGTH arm) (s,pcS0)) =
	     get_st (runTo (upload arm iB (FST s)) (FST s + LENGTH arm) (s,pcS1)))`,
  RW_TAC std_ss [terminated, get_st] THEN
  Cases_on `LENGTH arm` THENL [
       RW_TAC std_ss [Once RUNTO_EXPAND_ONCE] THEN
           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE],
        METIS_TAC [FST, RUNTO_STATE_PCS_SEPERATE]
  ]
  );

val DSTATE_COMPOSITION = Q.store_thm (
   "DSTATE_COMPOSITION",
   `!arm arm' pos0 pos1 pos2 cpsr0 cpsr1 cpsr2 iB (st:DSTATE).
       closed arm /\ terminated arm /\ status_independent arm /\
       closed arm' /\ terminated arm' /\ status_independent arm'
       ==>
	   (get_st (runTo (upload (arm ++ arm') iB pos0) (pos0 + LENGTH arm + LENGTH arm') ((pos0,cpsr0,st),({}))) =
		get_st (runTo (upload arm' iB pos2) (pos2 + LENGTH arm')
		     ((pos2,cpsr2, get_st (runTo (upload arm iB pos1) (pos1 + LENGTH arm) ((pos1,cpsr1,st),({})))), ({}))))`,

   RW_TAC std_ss [get_st] THEN
   RW_TAC std_ss [(SIMP_RULE set_ss [ADD_ASSOC] o SIMP_RULE list_ss [] o
               Q.SPECL [`arm`,`arm'`,`[]`,`[]`,`pos0`,`iB`,`((pos0,cpsr0,st),{}):STATEPCS`]) CLOSED_SEQUENTIAL_COMPOSITION] THEN
   `?pos' cpsr' pcS'. runTo (upload arm iB pos0) (pos0 + LENGTH arm) ((pos0,cpsr0,st),{}) =
      ((pos',cpsr',SND(SND(FST (runTo (upload arm iB pos0) (pos0 + LENGTH arm) ((pos0,cpsr0,st),{}))))),pcS')` by METIS_TAC [ABS_PAIR_THM, FST,SND] THEN
    `pos' = pos0 + LENGTH arm` by METIS_TAC [TERMINATED_THM, FST] THEN
    ONCE_ASM_REWRITE_TAC [] THEN
    Q.PAT_ASSUM `runTo x y z = k` (K ALL_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    `SND (SND (FST (runTo (upload arm iB pos0) (pos0 + LENGTH arm) (((pos0,cpsr0,st),({})):STATEPCS)))) =
       SND (SND (FST (runTo (upload arm iB pos1) (pos1 + LENGTH arm) (((pos1,cpsr1,st),({})):STATEPCS))))` by METIS_TAC [status_independent,get_st] THEN
    METIS_TAC [status_independent, FST, get_st, DSTATE_IRRELEVANT_PCS, SND]
  );

(*
val BASIC_CLOSED_POSIND_COMPOSITION =
    SIMP_RULE std_ss [Once SWAP_FORALL_THM] (GEN_ALL (SIMP_RULE arith_ss [reset_st] (Q.SPECL [`arm`,`arm'`,`0`,`0`,`0`] CLOSED_POSIND_COMPOSITION)));
*)

(*---------------------------------------------------------------------------------*)
(*      Well formed codes                                                          *)
(*---------------------------------------------------------------------------------*)

val well_formed = Define `
    well_formed arm =
         closed arm /\ terminated arm /\ status_independent arm`;


(*---------------------------------------------------------------------------------*)
(*      Evaluation of flag codes                                                   *)
(*---------------------------------------------------------------------------------*)

val eval_fl = Define `
    eval_fl arm st =
         get_st (runTo (uploadCode arm (\i.ARB)) (LENGTH arm) ((0,0w,st),({})))`;


val SEQ_COMPOSITION_FLAT = Q.store_thm (
   "SEQ_COMPOSITION_FLAT",
   `!arm arm'.
       well_formed arm /\ well_formed arm'
       ==>
	   (eval_fl (arm ++ arm') = eval_fl arm' o eval_fl arm)`,
   RW_TAC std_ss [uploadCode_def, eval_fl, well_formed, FUN_EQ_THM] THEN
   RW_TAC list_ss [SIMP_RULE arith_ss [] (Q.SPECL [`arm`,`arm'`,`0`,`0`,`0`,`0w`,`0w`,`0w`,`(\i. ARB)`,`x`] DSTATE_COMPOSITION)]
  );

(*---------------------------------------------------------------------------------*)
(* flat coce composition                                                           *)
(*---------------------------------------------------------------------------------*)

val mk_SC = Define `
    mk_SC arm1 arm2 =
         arm1 ++ arm2`;

val mk_CJ = Define `
    mk_CJ (v1,rop,v2) arm_t arm_f =
         [((CMP,NONE,F),NONE,[v1;v2],NONE):INST] ++
         [((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))] ++
         arm_f ++
         [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++
	 arm_t`;


val mk_TR = Define `
    mk_TR (v1,rop,v2) (arm:INST list) =
         ((CMP,NONE,F),NONE,[v1;v2],NONE) ::
         ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2))) ::
         arm ++
         [((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm + 2)))]`;

(*---------------------------------------------------------------------------------*)
(*      Well-formed Composition                                                    *)
(*---------------------------------------------------------------------------------*)

val SC_IS_WELL_FORMED = Q.store_thm (
   "SC_IS_WELL_FORMED",
   `!arm1 arm2. well_formed arm1 /\ well_formed arm2
           ==> well_formed (mk_SC arm1 arm2)`,

   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [well_formed, mk_SC] THEN
   ASSUME_TAC ((GEN (Term `s:STATE`) o GEN (Term `iB:num->INST`) o SIMP_RULE set_ss [] o SIMP_RULE list_ss [] o
               Q.SPECL [`arm1`,`arm2`,`[]`,`[]`,`FST (s:STATE)`,`iB`,`(s,{}):STATEPCS`]) CLOSED_SEQUENTIAL_COMPOSITION) THEN
   RW_TAC std_ss [terminated, status_independent] THENL [

       RES_TAC THEN
           FULL_SIMP_TAC std_ss [ADD_ASSOC, LENGTH_APPEND, closed] THEN
           REPEAT GEN_TAC THEN
           NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
           `FST (FST (runTo (upload arm1 iB (FST s)) (FST s + LENGTH arm1) (s,{}))) = FST s + LENGTH arm1` by METIS_TAC [TERMINATED_THM,FST] THEN
           `?s' pcS'. runTo (upload arm1 iB (FST s)) (FST s + LENGTH arm1) (s,{}) = (s',pcS')` by METIS_TAC [ABS_PAIR_THM] THEN
           `SND (runTo (upload arm2 iB (FST s + LENGTH arm1)) (FST s + LENGTH arm1 + LENGTH arm2) (s',pcS')) =
               SND (runTo (upload arm2 iB (FST s + LENGTH arm1)) (FST s + LENGTH arm1 + LENGTH arm2) (s',{})) UNION pcS'`
							 by METIS_TAC [terminated, RUNTO_PCS_UNION, ADD_ASSOC] THEN
           FULL_SIMP_TAC set_ss [] THEN
           STRIP_TAC THENL [
               Q.PAT_ASSUM `FST s' = FST s + LENGTH arm1` (ASSUME_TAC o GSYM) THEN
                   FULL_SIMP_TAC arith_ss [ADD_ASSOC] THEN
                   RES_TAC THEN FULL_SIMP_TAC arith_ss [],
               `x IN SND (runTo (upload arm1 iB (FST s)) (FST s + LENGTH arm1) (s,{}))` by METIS_TAC [SND] THEN
                   RES_TAC THEN FULL_SIMP_TAC arith_ss []
               ],

       `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
           ASM_REWRITE_TAC [ADD_ASSOC] THEN
           MATCH_MP_TAC (Q.SPECL [`{}`,`pcS0`] STOPAT_ANY_PCS_2) THEN
           METIS_TAC [LENGTH_APPEND],

       RES_TAC THEN
           FULL_SIMP_TAC std_ss [ADD_ASSOC, LENGTH_APPEND] THEN
           FIRST_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [] o Q.SPECL [`(pos0,cpsr0,st):STATE`,`iB`]) THEN
           Q.PAT_ASSUM `!s.x` (ASSUME_TAC o SIMP_RULE std_ss [] o Q.SPECL [`(pos1,cpsr1,st):STATE`,`iB`]) THEN
           FULL_SIMP_TAC std_ss [get_st, status_independent] THEN
           NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
           Q.ABBREV_TAC `s' = runTo (upload arm1 iB pos0) (pos0 + LENGTH arm1) ((pos0,cpsr0,st),{})` THEN
           `?pos' cpsr' pcS'. (s':STATEPCS = ((FST (FST (s')), FST (SND (FST s')), SND (SND (FST s'))),SND s')) /\
               (runTo (upload arm1 iB pos1) (pos1 + LENGTH arm1) ((pos1,cpsr1,st),{}) =
                    ((pos',cpsr',SND (SND (FST s'))),pcS'))`
                  by (Q.UNABBREV_TAC `s'` THEN METIS_TAC [ABS_PAIR_THM, FST, SND]) THEN
           `(pos0 + LENGTH arm1 = FST (FST s')) /\ (pos1 + LENGTH arm1 = pos')` by
                   (Q.UNABBREV_TAC `s'` THEN METIS_TAC [TERMINATED_THM, terminated, FST]) THEN
           ONCE_ASM_REWRITE_TAC [] THEN
           NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN
           METIS_TAC [RUNTO_STATE_PCS_SEPERATE, terminated, FST]
       ]
  );

val UNCOND_JUMP_OVER_THM = Q.store_thm (
   "UNCOND_JUMP_OVER_THM",
   `!arm. well_formed ([((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm + 1)))] ++ arm) /\
          !iB pos cpsr st pcS. get_st (runTo (upload ([((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm + 1)))] ++ arm) iB pos)
					(pos + LENGTH arm + 1) ((pos,cpsr,st),pcS)) = st`,

   STRIP_TAC THEN
   `!s pcS iB. step (upload (((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm + 1)))::arm) iB (FST s)) (s,pcS) =
					 ((FST s + LENGTH arm + 1, SND s), FST s INSERT pcS)` by ALL_TAC THENL [
       REPEAT GEN_TAC THEN
           `?pc cpsr st. s = (pc,cpsr,st)` by METIS_TAC [ABS_PAIR_THM] THEN
           FULL_SIMP_TAC std_ss [step_def] THEN
           `0 < LENGTH (((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm + 1)))::arm)` by RW_TAC list_ss [] THEN
           IMP_RES_TAC UPLOAD_LEM THEN
           FULL_SIMP_TAC arith_ss [EL, HD] THEN
           RW_TAC list_ss [decode_cond_def, decode_cond_cpsr_def, decode_op_thm, setS_def, getS_def, goto_thm],

       RW_TAC std_ss [well_formed, terminated, status_independent] THENL [
           SIMP_TAC std_ss [closed] THEN
               REPEAT GEN_TAC THEN
               SIMP_TAC list_ss [Once RUNTO_EXPAND_ONCE] THEN
               ASM_REWRITE_TAC [] THEN
               SIMP_TAC list_ss [Once RUNTO_EXPAND_ONCE] THEN
               RW_TAC set_ss [] THEN
               RW_TAC arith_ss [],
           `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
               RW_TAC list_ss [stopAt_def] THEN
               Q.EXISTS_TAC `SUC 0` THEN
               RW_TAC arith_ss [FUNPOW],
            RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, get_st] THEN
                FIRST_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [] o (Q.SPECL [`(pos0,cpsr0,st)`])) THEN
                RW_TAC list_ss [Once RUNTO_EXPAND_ONCE] THEN
                POP_ASSUM (K ALL_TAC) THEN
                POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [] o (Q.SPECL [`(pos1,cpsr1,st)`])) THEN
                RW_TAC list_ss [Once RUNTO_EXPAND_ONCE] THEN
                RW_TAC list_ss [Once RUNTO_EXPAND_ONCE],
            RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, get_st] THEN
                POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [] o (Q.SPECL [`(pos,cpsr,st)`])) THEN
                RW_TAC list_ss [Once RUNTO_EXPAND_ONCE]
            ]
   ]
  );


(*---------------------------------------------------------------------------------*)
(* Hoare Logic for sequential compositions of flat codes                           *)
(*---------------------------------------------------------------------------------*)

val _ = type_abbrev("P_DSTATE", Type`:DSTATE->bool`);

val HOARE_SC_FLAT = Q.store_thm (
   "HOARE_SC_FLAT",
   `!arm1 arm2 (P:P_DSTATE) (Q:P_DSTATE) (R:P_DSTATE) (T:P_DSTATE).
           well_formed arm1 /\ well_formed arm2 /\
	   (!st. P st ==> Q (eval_fl arm1 st)) /\ (!st. R st ==> T (eval_fl arm2 st)) /\ (!st. Q st ==> R st)
           ==>
           (!st. P st ==> T (eval_fl (mk_SC arm1 arm2) st))`,
       RW_TAC std_ss [mk_SC, SEQ_COMPOSITION_FLAT]
   );


(*---------------------------------------------------------------------------------*)
(* Enumerate all possibilities of conditions                                       *)
(*---------------------------------------------------------------------------------*)
val eval_cond_def = Define `
    (eval_cond (v1,EQ,v2) s = (read s v1 = read s v2)) /\
    (eval_cond (v1,CS,v2) s = (read s v1 >=+ read s v2)) /\
    (eval_cond (v1,MI,v2) s = (let (n,z,c,v) = nzcv (read s v1) (read s v2) in n)) /\
    (eval_cond (v1,VS,v2) s = (let (n,z,c,v) = nzcv (read s v1) (read s v2) in v)) /\
    (eval_cond (v1,HI,v2) s = (read s v1 >+ read s v2)) /\
    (eval_cond (v1,GE,v2) s = (read s v1 >= read s v2)) /\
    (eval_cond (v1,GT,v2) s = (read s v1 > read s v2)) /\
    (eval_cond (v1,AL,v2) s = T) /\

    (eval_cond (v1,NE,v2) s = ~(read s v1 = read s v2)) /\
    (eval_cond (v1,CC,v2) s = (read s v1 <+ read s v2)) /\
    (eval_cond (v1,PL,v2) s = (let (n,z,c,v) = nzcv (read s v1) (read s v2) in ~n)) /\
    (eval_cond (v1,VC,v2) s = (let (n,z,c,v) = nzcv (read s v1) (read s v2) in ~v)) /\
    (eval_cond (v1,LS,v2) s = (read s v1 <=+ read s v2)) /\
    (eval_cond (v1,LT,v2) s = (read s v1 < read s v2)) /\
    (eval_cond (v1,LE,v2) s = (read s v1 <= read s v2)) /\
    (eval_cond (v1,NV,v2) s = F)`;


val eval_cond_thm = Q.store_thm (
   "eval_cond_thm",
	 `!v1 rop v2 st cpsr.
		  (eval_cond (v1,rop,v2) st = decode_cond_cpsr
            (setNZCV cpsr
               (word_msb (read st v1 - read st v2),read st v1 = read st v2,
                read st v2 <=+ read st v1,
                ~(word_msb (read st v1) = word_msb (read st v2)) /\
                ~(word_msb (read st v1) =
                  word_msb (read st v1 - read st v2)))) rop)` ,

	Cases_on `rop` THEN
	FULL_SIMP_TAC std_ss [eval_cond_def, decode_cond_def , decode_op_thm,
		decode_cond_cpsr_def, setNZCV_thm, LET_THM,
		nzcv_def] THENL [


		REWRITE_TAC [WORD_HIGHER_EQ],
		SIMP_TAC std_ss [GSYM word_add_def, word_sub_def],
		SIMP_TAC std_ss [GSYM word_add_def, word_sub_def] THEN METIS_TAC[],
		SIMP_TAC arith_ss [WORD_HI, WORD_LO, WORD_LS, GSYM w2n_11],


		SIMP_TAC std_ss [word_ge_def, nzcv_def, LET_THM, GSYM word_add_def,
			GSYM word_sub_def] THEN METIS_TAC[],

		SIMP_TAC std_ss [word_gt_def, nzcv_def, LET_THM, GSYM word_add_def,
				GSYM word_sub_def, WORD_EQ_SUB_RADD, WORD_ADD_0] THEN
      METIS_TAC[],

		PROVE_TAC[WORD_LOWER_EQ_ANTISYM, WORD_LOWER_CASES],
		SIMP_TAC std_ss [GSYM word_add_def, GSYM word_sub_def],

		SIMP_TAC std_ss [GSYM word_add_def, GSYM word_sub_def] THEN METIS_TAC[],

		SIMP_TAC std_ss [WORD_LOWER_OR_EQ] THEN
		METIS_TAC[WORD_LOWER_LOWER_CASES, WORD_LOWER_ANTISYM],

		SIMP_TAC std_ss [word_lt_def, nzcv_def, LET_THM, GSYM word_add_def,
				GSYM word_sub_def, WORD_EQ_SUB_RADD, WORD_ADD_0] THEN
      METIS_TAC[],

		SIMP_TAC std_ss [word_le_def, nzcv_def, LET_THM, GSYM word_add_def,
			GSYM word_sub_def, WORD_EQ_SUB_RADD, WORD_ADD_0] THEN METIS_TAC[]
	]);



val ENUMERATE_CJ = Q.store_thm (
   "ENUMERATE_CJ",
    `!cond pc cpsr st offset.
            (eval_cond cond st ==>
             ?cpsr'. decode_cond (pc + 1, decode_op (pc,cpsr,st) (CMP,(NONE :EXP option),[FST cond; SND (SND cond)],(NONE:OFFSET option)))
		                 ((B,SOME (FST (SND cond)),F),NONE,[],SOME offset) =
                     ((goto (pc+1,SOME offset)), cpsr', st)) /\
            (~(eval_cond cond) st ==>
              ?cpsr'. decode_cond (pc + 1, decode_op (pc,cpsr,st) (CMP,(NONE :EXP option),[FST cond; SND (SND cond)],(NONE:OFFSET option)))
		                 ((B,SOME (FST (SND cond)),F),NONE,[],SOME offset) =
		     (pc+2,cpsr',st))`,

	 REPEAT GEN_TAC THEN
	 `?v1 rop v2. cond = (v1,rop,v2)` by METIS_TAC [ABS_PAIR_THM] THEN
	 ASM_SIMP_TAC list_ss [decode_op_def, OPERATOR_case_def, decode_cond_def, LET_THM,
		GSYM eval_cond_thm]
)

(*---------------------------------------------------------------------------------*)
(* Cnditional-jump compositions of flat codes                                      *)
(*---------------------------------------------------------------------------------*)

(* The condition is true, execute the true block *)

val CJ_COMPOSITION_LEM_1 = Q.store_thm (
   "CJ_COMPOSITION_LEM_1",
   `!cond arm_t arm_f arm' s iB.
          well_formed arm_t /\ well_formed arm_f /\ eval_cond cond (SND (SND s)) /\ (arm' = mk_CJ cond arm_t arm_f)
          ==> ?cpsr' cpsr''.
          (runTo (upload arm' iB (FST s)) (FST s + LENGTH arm') (s,{}) =
            ((FST s + LENGTH arm', cpsr', get_st (runTo (uploadCode arm_t iB) (LENGTH arm_t) ((0,SND s),{}))),
              SND (runTo (upload arm_t iB (FST s+ LENGTH arm_f + 3)) (FST s + LENGTH arm_f + 3 + LENGTH arm_t)
		   ((FST s + LENGTH arm_f + 3,cpsr'', SND (SND s)),{FST s + 1;FST s}))))`,

    RW_TAC std_ss [well_formed] THEN
    `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, SUC_ONE_ADD] THEN REWRITE_TAC [ADD_ASSOC, uploadCode_def] THEN

    Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))):: (arm_f ++
                 [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)` THEN
    `0 < LENGTH insts` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
    `((upload insts iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload insts iB pc) (pc+1) =
         ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))))` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                  IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, decode_cond_thm] THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def] THEN
    IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPECL [`pc`,`cpsr`,`arm_f`]) THEN
    FULL_SIMP_TAC std_ss [] THEN
    RW_TAC arith_ss [goto_def, uploadCode_def] THEN
    Q.UNABBREV_TAC `insts` THEN
    Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::arm_f ++
							[((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))]` THEN
    `(LENGTH arm_f + 3 = LENGTH insts) /\
    (((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
                (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t) =
                insts ++ arm_t)` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
    `LENGTH arm_f + (LENGTH arm_t + 3) = LENGTH arm_f + 3 + LENGTH arm_t` by RW_TAC arith_ss [] THEN
    ASM_REWRITE_TAC [] THEN
    NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
    RW_TAC arith_ss [get_st, SIMP_RULE arith_ss []
	 (Q.SPECL [`arm_t:INST list`,`insts:INST list`,`pc`, `iB`, `((pc + LENGTH (insts:INST list),cpsr',st),{pc+1; pc})`] CLOSED_PREFIX)] THEN
    `FST (FST (runTo (upload arm_t iB (pc + LENGTH insts)) (pc + LENGTH insts + LENGTH arm_t) ((pc+LENGTH insts,cpsr',st),{pc+1; pc}))) =
           pc + LENGTH insts + LENGTH arm_t` by METIS_TAC [TERMINATED_THM, FST] THEN
    Q.EXISTS_TAC `FST (SND (FST (runTo (upload arm_t iB (pc+LENGTH insts)) (pc+LENGTH arm_t+LENGTH insts) ((pc+LENGTH insts,cpsr',st),{pc+1;pc}))))` THEN
    Q.EXISTS_TAC `cpsr'` THEN
    `SND (SND (FST (runTo (upload arm_t iB 0) (LENGTH arm_t) ((0,cpsr,st),{})))) =  SND (SND (FST (runTo (upload arm_t iB (pc+LENGTH insts))
                 (pc + LENGTH insts + LENGTH arm_t) ((pc + LENGTH insts,cpsr',st),{pc+1;pc}))))` by METIS_TAC [get_st, DSTATE_IRRELEVANT_PCS,
                   status_independent, DECIDE (Term `!x.0 + x = x`), FST] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [METIS_PROVE [ADD_SYM, ADD_ASSOC] (Term `pc + LENGTH arm_t + LENGTH insts = pc + LENGTH insts + LENGTH arm_t`)] THEN
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC [ABS_PAIR_THM, ADD_SYM, FST, SND]
   );


val CJ_TERMINATED_LEM_1 = Q.store_thm (
   "CJ_TERMINATED_LEM_1",
   `!cond arm_t arm_f arm' s pcS iB.
          well_formed arm_t /\ well_formed arm_f /\ eval_cond cond (SND (SND s)) /\ (arm' = mk_CJ cond arm_t arm_f)
          ==> terd (upload arm' iB (FST s)) (FST s + LENGTH arm') (s,pcS)`,

    RW_TAC std_ss [well_formed, terd_def, stopAt_def] THEN
    `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, SUC_ONE_ADD] THEN REWRITE_TAC [ADD_ASSOC] THEN
    Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))):: (arm_f ++
                 [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)` THEN
    `?cpsr' st' pcS'. FUNPOW (step (upload insts iB pc)) 2 ((pc,cpsr,st),pcS) = ((pc+3+LENGTH arm_f,cpsr',st'),pcS')` by ALL_TAC THENL [
           `0 < LENGTH insts` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
           `((upload insts iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload insts iB pc) (pc+1) =
                 ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))))` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                  IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
           REWRITE_TAC [DECIDE ``2 = SUC 1``] THEN
           RW_TAC list_ss [FUNPOW, step_def, decode_cond_thm] THEN
           REWRITE_TAC [DECIDE ``1 = SUC 0``] THEN
           RW_TAC list_ss [FUNPOW, step_def] THEN
           IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
           POP_ASSUM (ASSUME_TAC o Q.SPECL [`pc`,`cpsr`,`arm_f`]) THEN
           FULL_SIMP_TAC std_ss [] THEN RW_TAC arith_ss [goto_def],

    Q.ABBREV_TAC `pc' = pc + 3 + LENGTH arm_f` THEN
        Q.EXISTS_TAC `shortest (\s':STATEPCS.FST (FST s') = pc' + LENGTH arm_t) (step (upload insts iB pc)) ((pc',cpsr',st'),pcS') + 2` THEN
        RW_TAC std_ss [GSYM FUNPOW_FUNPOW] THEN
        Q.UNABBREV_TAC `insts` THEN
        Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::arm_f ++
							[((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))]` THEN
        `(pc + 3 + LENGTH arm_f = pc + LENGTH insts) /\
        (((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
                (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t) =
                insts ++ arm_t)` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss [] THEN Q.UNABBREV_TAC `pc'` THEN RW_TAC arith_ss []) THEN
        Q.UNABBREV_TAC `pc'` THEN ASM_REWRITE_TAC [] THEN
        `stopAt (\s'. FST (FST s') = pc + LENGTH insts + LENGTH arm_t) (step (upload (insts ++ arm_t) iB pc))
           ((pc + LENGTH insts,cpsr',st'),pcS')` by METIS_TAC [SIMP_RULE list_ss [] (Q.SPECL [`arm_t`,`insts`,`[]`] TERMINATED_MIDDLE),FST,terd_def] THEN
        IMP_RES_TAC UNROLL_RUNTO THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
        NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
        RW_TAC arith_ss [SIMP_RULE arith_ss [] (Q.SPECL [`arm_t:INST list`,`insts:INST list`,`pc`, `iB`,
             `((pc + LENGTH (insts:INST list),cpsr',st'),pcS')`] CLOSED_PREFIX)] THEN
        `FST (FST (runTo (upload arm_t iB (pc + LENGTH insts)) (pc + (LENGTH insts + LENGTH arm_t)) ((pc+LENGTH insts,cpsr',st'),pcS'))) =
           pc + LENGTH insts + LENGTH arm_t` by METIS_TAC [TERMINATED_THM, FST, ADD_ASSOC] THEN
        FULL_SIMP_TAC arith_ss []
    ]
   );


(* The condition is false, execute the false block *)

val CJ_COMPOSITION_LEM_2 = Q.store_thm (
   "CJ_COMPOSITION_LEM_2",
   `!cond arm_t arm_f arm' s iB.
        well_formed arm_t /\ well_formed arm_f /\ ~(eval_cond cond (SND (SND s))) /\ (arm' = mk_CJ cond arm_t arm_f)
        ==> ?cpsr' cpsr''.
         (runTo (upload arm' iB (FST s)) (FST s + LENGTH arm') (s,{}) =
             ((FST s+LENGTH arm', cpsr', get_st (runTo (uploadCode arm_f iB) (LENGTH arm_f) ((0,SND s),{}))),
               FST s + 2 + LENGTH arm_f INSERT SND (runTo (upload arm_f iB (FST s + 2)) (FST s + 2 + LENGTH arm_f)
						    ((FST s + 2,cpsr'',SND (SND s)),{FST s + 1;FST s}))))`,

    RW_TAC std_ss [well_formed] THEN
    `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, SUC_ONE_ADD] THEN REWRITE_TAC [ADD_ASSOC, uploadCode_def] THEN

    Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))):: (arm_f ++
                 [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)` THEN
    `0 < LENGTH insts` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
    `((upload insts iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload insts iB pc) (pc+1) =
         ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))))` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                  IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, decode_cond_thm] THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def] THEN
    IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPECL [`pc`,`cpsr`,`arm_f`]) THEN
    FULL_SIMP_TAC std_ss [] THEN
    RW_TAC arith_ss [goto_def, uploadCode_def] THEN
    Q.UNABBREV_TAC `insts` THEN
    NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
    Q.ABBREV_TAC `insts1 = (((CMP,NONE,F),NONE,[v1; v2],NONE):INST)::[((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))]` THEN
    Q.ABBREV_TAC `insts2 = ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1))) :: arm_t` THEN
    `(LENGTH arm_t + 1 = LENGTH insts2) /\ (LENGTH insts1 = 2) /\
    ((((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
          (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)) =
                (insts1 ++ (arm_f:INST list)) ++ insts2)` by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [] THEN
							METIS_TAC [ rich_listTheory.CONS_APPEND, APPEND_ASSOC]) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    `pc + LENGTH insts1 = FST (FST ((pc + 2,cpsr',st),{pc+1; pc}))` by RW_TAC arith_ss [] THEN
    `?s1 pcS1. (s1,pcS1) = runTo (upload (insts1 ++ arm_f ++ insts2) iB pc) (FST (FST ((pc+2,cpsr',st),{pc+1; pc})) +
	      LENGTH arm_f) ((pc + 2,cpsr',st),{pc+1; pc})` by METIS_TAC [ABS_PAIR_THM] THEN
    `~(pc + LENGTH insts1 + LENGTH arm_f + LENGTH insts2 IN ((FST ((pc + 2,cpsr',st))) INSERT pcS1))` by ALL_TAC THENL [
        POP_ASSUM MP_TAC THEN
           RW_TAC std_ss [SIMP_RULE std_ss [] (Q.SPECL [`arm_f`,`insts1`,`insts2`,`pc`,`iB`, `((pc+2,cpsr',st),{pc+1;pc}):STATEPCS`] CLOSED_MIDDLE)] THEN
            `pcS1 = SND (runTo (upload arm_f iB (pc+2)) (pc + 2 + LENGTH arm_f) ((pc+2,cpsr',st),{})) UNION {pc+1;pc}`
		     by METIS_TAC [RUNTO_PCS_UNION, SND, FST, terminated] THEN
            `!x. x IN SND (runTo (upload arm_f iB (pc+2)) (pc + 2 + LENGTH arm_f) ((pc + 2,cpsr',st),{})) ==>
			 pc + 2 <= x /\ x < pc + 2 + LENGTH arm_f` by METIS_TAC [closed,FST] THEN
            Q.PAT_ASSUM `LENGTH arm_t + 1 = LENGTH insts2` (ASSUME_TAC o GSYM) THEN
            FULL_SIMP_TAC set_ss [] THEN FULL_SIMP_TAC arith_ss [] THEN
            STRIP_TAC THEN RES_TAC THEN
            FULL_SIMP_TAC arith_ss [],

    `terd (upload (insts1 ++ arm_f ++ insts2) iB pc) (FST (FST ((pc + 2,cpsr',st),{pc+1; pc})) + LENGTH arm_f)
						 ((pc+2,cpsr',st),{pc+1; pc})` by METIS_TAC [FST, TERMINATED_MIDDLE] THEN
            `pc + (LENGTH arm_f + (LENGTH arm_t + 3)) = pc + LENGTH insts1 + LENGTH arm_f + LENGTH insts2` by RW_TAC arith_ss [] THEN
             Q.PAT_ASSUM `LENGTH insts1 = 2` (K ALL_TAC) THEN
             Q.PAT_ASSUM `pc + LENGTH insts1 = x` (K ALL_TAC) THEN
             ASM_REWRITE_TAC [] THEN
             IMP_RES_TAC RUNTO_COMPOSITION THEN ASM_REWRITE_TAC [] THEN
             NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
             POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [] o GSYM) THEN
             `(LENGTH insts1 = 2) /\ (LENGTH insts2 = LENGTH arm_t + 1)` by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2`
                       THEN RW_TAC list_ss []) THEN
             `runTo (upload arm_f iB (pc+2)) (pc + 2 + LENGTH arm_f) ((pc+2,cpsr',st),{pc+1;pc})= (s1,pcS1)` by METIS_TAC [FST, CLOSED_PAIR_EQ,
                        DECIDE (Term `pc + (LENGTH arm_f + 2) = pc + 2 + LENGTH arm_f`),
		        SIMP_RULE std_ss [] (Q.SPECL [`arm_f`,`insts1`,`insts2`,`pc`,`iB`, `((pc+2,cpsr',st),{pc+1;pc}):STATEPCS`] CLOSED_MIDDLE)] THEN
             FULL_SIMP_TAC std_ss [] THEN
             `FST s1 = pc + 2 + LENGTH arm_f` by METIS_TAC [TERMINATED_THM,FST] THEN
             `?cpsr1 st1. s1:STATE = (SUC (SUC (pc + LENGTH arm_f)), cpsr1,st1)` by (RW_TAC arith_ss [SUC_ONE_ADD] THEN
			       METIS_TAC [FST, ADD_SYM, ADD_ASSOC,ABS_PAIR_THM]) THEN
             FULL_SIMP_TAC std_ss [] THEN
             `(upload (insts1++arm_f++insts2) iB pc) (pc+(LENGTH arm_f+2)) = ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))` by ALL_TAC THENL [
	         Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN
                    `LENGTH arm_f + 2 < LENGTH  ([((CMP,NONE,F),NONE,[v1; v2],NONE);((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))] ++ arm_f ++
						 ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))::arm_t)` by RW_TAC list_ss [] THEN
                    RW_TAC list_ss [UPLOAD_LEM] THEN
                    `LENGTH (((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::arm_f) <=  LENGTH arm_f + 2`
                         by RW_TAC list_ss [] THEN
                    IMP_RES_TAC rich_listTheory.EL_APPEND2 THEN
                    FULL_SIMP_TAC list_ss [SUC_ONE_ADD],

                RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, decode_cond_thm, decode_op_thm,goto_thm] THEN
                    RW_TAC arith_ss [Once RUNTO_EXPAND_ONCE, SUC_ONE_ADD, ADD_SYM, get_st] THEN
                    Q.EXISTS_TAC `cpsr'` THEN STRIP_TAC THENL [
	            `SND (SND (FST (runTo (upload arm_f iB 0) (LENGTH arm_f) ((0,cpsr,st),{})))) =  SND (SND (FST (runTo (upload arm_f iB (pc + 2))
                     (pc + 2 + LENGTH arm_f) ((pc + 2,cpsr',st),{pc+1; pc}))))` by METIS_TAC [get_st, DSTATE_IRRELEVANT_PCS,
                       status_independent, DECIDE (Term `!x.0 + x = x`), FST, ADD_SYM] THEN
                     METIS_TAC [ABS_PAIR_THM, ADD_SYM, FST, SND],
                 METIS_TAC [ABS_PAIR_THM, ADD_SYM, ADD_ASSOC,FST, SND]
               ]
             ]
        ]
   );


val CJ_TERMINATED_LEM_2 = Q.store_thm (
   "CJ_TERMINATED_LEM_2",
   `!cond arm_t arm_f arm' s pcS iB.
        well_formed arm_t /\ well_formed arm_f /\ ~(eval_cond cond (SND (SND s))) /\ (arm' = mk_CJ cond arm_t arm_f)
          ==> terd (upload arm' iB (FST s)) (FST s + LENGTH arm') (s,pcS)`,

    RW_TAC std_ss [well_formed, terd_def, stopAt_def] THEN
    `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, SUC_ONE_ADD] THEN REWRITE_TAC [ADD_ASSOC] THEN
    Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))):: (arm_f ++
                 [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)` THEN
    `?cpsr' st' pcS'. FUNPOW (step (upload insts iB pc)) 2 ((pc,cpsr,st),pcS) = ((pc+2,cpsr',st'),pcS')` by ALL_TAC THENL [
           `0 < LENGTH insts` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
           `((upload insts iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload insts iB pc) (pc+1) =
                 ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2))))` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                  IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
           REWRITE_TAC [DECIDE ``2 = SUC 1``] THEN
           RW_TAC list_ss [FUNPOW, step_def, decode_cond_thm] THEN
           REWRITE_TAC [DECIDE ``1 = SUC 0``] THEN
           RW_TAC list_ss [FUNPOW, step_def] THEN
           IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
           POP_ASSUM (ASSUME_TAC o Q.SPECL [`pc`,`cpsr`,`arm_f`]) THEN
           FULL_SIMP_TAC std_ss [] THEN RW_TAC arith_ss [goto_def],

    Q.EXISTS_TAC `1 + shortest (\s':STATEPCS.FST (FST s') = pc + 2 + LENGTH arm_f) (step (upload insts iB pc)) ((pc+2,cpsr',st'),pcS') + 2` THEN
        RW_TAC std_ss [GSYM FUNPOW_FUNPOW] THEN
        Q.UNABBREV_TAC `insts` THEN
        Q.ABBREV_TAC `insts1 = (((CMP,NONE,F),NONE,[v1; v2],NONE):INST)::[((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))]` THEN
        Q.ABBREV_TAC `insts2 = ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1))) :: arm_t` THEN
        `(LENGTH arm_t + 1 = LENGTH insts2) /\ (2 = LENGTH insts1) /\
            ((((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
               (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)) =
                (insts1 ++ (arm_f:INST list)) ++ insts2)` by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [] THEN
							METIS_TAC [ rich_listTheory.CONS_APPEND, APPEND_ASSOC]) THEN
        ASM_REWRITE_TAC [] THEN
        `stopAt (\s'. FST (FST s') = pc + LENGTH insts1 + LENGTH arm_f) (step (upload (insts1 ++ arm_f ++ insts2) iB pc)) ((pc + LENGTH insts1,
             cpsr',st'),pcS')` by METIS_TAC [SIMP_RULE list_ss [] (Q.SPECL [`arm_f`,`insts1`,`insts2`] TERMINATED_MIDDLE),FST,terd_def] THEN
        IMP_RES_TAC UNROLL_RUNTO THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
        NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
        IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`arm_f`,`insts1:INST list`,`insts2`,`pc`,`iB`,`((pc + LENGTH (insts1:INST list),cpsr',st'),pcS')`]
               CLOSED_MIDDLE)) THEN
        RW_TAC std_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
        `FST (FST (runTo (upload arm_f iB (pc+LENGTH insts1)) (pc + LENGTH insts1 + LENGTH arm_f) ((pc + LENGTH insts1,cpsr',st'),pcS'))) =
              pc + LENGTH insts1 + LENGTH arm_f` by METIS_TAC [TERMINATED_THM,FST] THEN
        `?cpsr1 st1 pcS1.runTo (upload arm_f iB (pc+LENGTH insts1)) (pc + LENGTH insts1 + LENGTH arm_f) ((pc + LENGTH insts1,cpsr',st'),pcS') =
              ((pc + LENGTH insts1 + LENGTH arm_f,cpsr1,st1),pcS1)` by METIS_TAC [FST,ABS_PAIR_THM] THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [DECIDE (Term`1 = SUC 0`)] THEN
        RW_TAC std_ss [FUNPOW] THEN
        `(upload (insts1++arm_f++insts2) iB pc) (pc+(LENGTH arm_f+2)) = ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))` by ALL_TAC THENL [
	     Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN
                    `LENGTH arm_f + 2 < LENGTH  ([((CMP,NONE,F),NONE,[v1; v2],NONE);((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))] ++ arm_f ++
						 ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))::arm_t)` by RW_TAC list_ss [] THEN
                    RW_TAC list_ss [UPLOAD_LEM] THEN
                    `LENGTH (((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::arm_f) <=  LENGTH arm_f + 2`
                         by RW_TAC list_ss [] THEN
                    IMP_RES_TAC rich_listTheory.EL_APPEND2 THEN
                    FULL_SIMP_TAC list_ss [SUC_ONE_ADD],
            POP_ASSUM MP_TAC THEN
                FULL_SIMP_TAC arith_ss [] THEN
                RW_TAC list_ss [step_def, decode_cond_thm, goto_def]
            ]
        ]
   );


val LENGTH_CJ = Q.store_thm (
   "LENGTH_CJ",
   `!cond arm_t arm_f. LENGTH (mk_CJ cond arm_t arm_f) =  LENGTH arm_f + 3 + LENGTH arm_t`,
   REPEAT STRIP_TAC THEN
   `?v1 rop v2. cond = (v1,rop,v2)` by METIS_TAC [ABS_PAIR_THM] THEN
   RW_TAC list_ss [mk_CJ]
  );


val CJ_IS_WELL_FORMED = Q.store_thm (
   "CJ_IS_WELL_FORMED",
   `!cond arm_t arm_f. well_formed arm_t /\ well_formed arm_f
           ==> well_formed (mk_CJ cond arm_t arm_f)`,

   REPEAT STRIP_TAC THEN
   RW_TAC std_ss [well_formed, terminated, status_independent] THENL [

       SIMP_TAC std_ss [closed] THEN REPEAT GEN_TAC THEN Cases_on `eval_cond cond (SND (SND s))` THENL [
           ASSUME_TAC ((Q.SPECL [`cond`,`arm_t`,`arm_f`,`s:STATE`,`iB:num->INST`]) (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_1)) THEN
               RES_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
               FULL_SIMP_TAC set_ss [LENGTH_CJ] THEN
               Q.ABBREV_TAC `pc = FST s + LENGTH arm_f + 3` THEN
               `SND (runTo (upload arm_t iB pc) (pc + LENGTH arm_t) ((pc,cpsr'',SND(SND s)),{FST s + 1; FST s})) =
                   SND (runTo (upload arm_t iB pc) (pc + LENGTH arm_t) ((pc,cpsr'',SND(SND s)),{})) UNION {FST s + 1; FST s}`
							 by METIS_TAC [well_formed, terminated, RUNTO_PCS_UNION, FST] THEN
               FULL_SIMP_TAC set_ss [] THEN
               STRIP_TAC THEN FULL_SIMP_TAC arith_ss [] THEN
               `pc <= x /\ x< pc + LENGTH arm_t` by METIS_TAC [well_formed,closed,FST] THEN
               Q.UNABBREV_TAC `pc` THEN
               FULL_SIMP_TAC arith_ss [],
           ASSUME_TAC ((Q.SPECL [`cond`,`arm_t`,`arm_f`,`s:STATE`,`iB:num->INST`]) (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_2)) THEN
               RES_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
               FULL_SIMP_TAC set_ss [LENGTH_CJ] THEN
               STRIP_TAC THEN
               FULL_SIMP_TAC arith_ss [] THEN
              `FST s + (LENGTH arm_f + 2) = FST s + 2 + LENGTH arm_f` by RW_TAC arith_ss [] THEN
              `SND (runTo (upload arm_f iB (FST s+2)) (FST s + (LENGTH arm_f + 2)) ((FST s+2,cpsr'',SND(SND s)),{FST s + 1; FST s})) =
               SND (runTo (upload arm_f iB (FST s+2)) (FST s + 2 + LENGTH arm_f) ((FST s+2,cpsr'',SND(SND s)),{})) UNION {FST s + 1; FST s}`
					 by METIS_TAC [well_formed, terminated, RUNTO_PCS_UNION, FST] THEN
               Q.PAT_ASSUM `x IN k` MP_TAC THEN
               FULL_SIMP_TAC set_ss [] THEN
               STRIP_TAC THEN FULL_SIMP_TAC arith_ss [] THEN
               `FST s + 2 <= x /\ x< FST s + 2 + LENGTH arm_f` by METIS_TAC [well_formed,closed,FST,
						       DECIDE (Term`FST s + (LENGTH arm_f + 2) = FST s + 2 + LENGTH arm_f`)] THEN
               FULL_SIMP_TAC arith_ss []
           ],

       `?s0 pcS0.s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN ASM_REWRITE_TAC [] THEN Cases_on `eval_cond cond (SND (SND s0))` THENL [
            METIS_TAC [CJ_TERMINATED_LEM_1,terd_def],
            METIS_TAC [CJ_TERMINATED_LEM_2,terd_def]
       ],

       SIMP_TAC std_ss [closed] THEN REPEAT GEN_TAC THEN Cases_on `eval_cond cond st` THENL [
            ASSUME_TAC ((SIMP_RULE std_ss [] o Q.SPECL [`cond`,`arm_t`,`arm_f`,`(pos0,cpsr0,st):STATE`,`iB:num->INST`])
                             (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_1)) THEN
                ASSUME_TAC ((SIMP_RULE std_ss [] o Q.SPECL [`cond`,`arm_t`,`arm_f`,`(pos1,cpsr1,st):STATE`,`iB:num->INST`])
                             (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_1)) THEN
                METIS_TAC [get_st,FST,SND,well_formed,status_independent, uploadCode_def, DECIDE (Term`!x.0+x=x`)],
            ASSUME_TAC ((SIMP_RULE std_ss [] o Q.SPECL [`cond`,`arm_t`,`arm_f`,`(pos0,cpsr0,st):STATE`,`iB:num->INST`])
                             (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_2)) THEN
                ASSUME_TAC ((SIMP_RULE std_ss [] o Q.SPECL [`cond`,`arm_t`,`arm_f`,`(pos1,cpsr1,st):STATE`,`iB:num->INST`])
                             (SIMP_RULE std_ss [] CJ_COMPOSITION_LEM_2)) THEN
                METIS_TAC [get_st,FST,SND,well_formed,status_independent, uploadCode_def, DECIDE (Term`!x.0+x=x`)]
            ]
       ]
  );


val HOARE_CJ_FLAT_LEM_1 = Q.store_thm (
   "HAORE_CJ_FLAT_LEM_1",
   `!cond arm_t arm_f (P:P_DSTATE) (Q:P_DSTATE) (R:P_DSTATE).
          well_formed arm_t /\ well_formed arm_f /\
	  (!st. P st ==> Q (eval_fl arm_t st)) /\ (!st. P st ==> R (eval_fl arm_f st))
          ==>
          !st. (P st /\ eval_cond cond st ==> Q (eval_fl (mk_CJ cond arm_t arm_f) st))`,

    RW_TAC std_ss [well_formed] THEN
    `?v1 rop v2. cond = (v1,rop,v2)` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, eval_fl, SUC_ONE_ADD] THEN

        (* The condition is true, execute the true block *)
        RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, UPLOADCODE_LEM, decode_cond_thm] THEN
            RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, UPLOADCODE_LEM] THEN
            IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`0`,`0w`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
            POP_ASSUM (ASSUME_TAC o Q.SPEC `arm_f`) THEN
            FULL_SIMP_TAC std_ss [] THEN
            RW_TAC arith_ss [goto_def, uploadCode_def] THEN
            Q.ABBREV_TAC `insts = ((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::arm_f ++
							[((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))]` THEN
	    `(LENGTH arm_f + 3 = LENGTH insts) /\
             (((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
                    (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t) =
                    insts ++ arm_t)` by (Q.UNABBREV_TAC `insts` THEN RW_TAC list_ss []) THEN
            `LENGTH arm_f + (LENGTH arm_t + 3) = LENGTH arm_f + 3 + LENGTH arm_t` by RW_TAC arith_ss [] THEN
            ASM_REWRITE_TAC [] THEN
            NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
            RW_TAC arith_ss [SIMP_RULE arith_ss []
			 (Q.SPECL [`arm_t:INST list`,`insts:INST list`,`0`, `(\i. ARB)`, `((LENGTH insts,cpsr',st),{1; 0})`] CLOSED_PREFIX)] THEN
            FULL_SIMP_TAC std_ss [eval_fl, uploadCode_def] THEN
            `LENGTH insts = FST (LENGTH insts,cpsr',st)` by RW_TAC std_ss [] THEN
            METIS_TAC [status_independent, DECIDE (Term `!x.0 + x = x`), ADD_SYM, DSTATE_IRRELEVANT_PCS]
   );


val HOARE_CJ_FLAT_LEM_2 = Q.store_thm (
   "HAORE_CJ_FLAT_LEM_2",
   `!cond arm_t arm_f (P:P_DSTATE) (Q:P_DSTATE) (R:P_DSTATE).
          well_formed arm_t /\ well_formed arm_f /\
	  (!st. P st ==> Q (eval_fl arm_t st)) /\ (!st. P st ==> R (eval_fl arm_f st))
          ==>
          !st. (P st /\ ~(eval_cond cond st) ==> R (eval_fl (mk_CJ cond arm_t arm_f) st))`,

    RW_TAC std_ss [well_formed] THEN
    `?v1 rop v2. cond = (v1,rop,v2)` by METIS_TAC [ABS_PAIR_THM] THEN
    RW_TAC list_ss [mk_CJ, eval_fl, SUC_ONE_ADD] THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, UPLOADCODE_LEM, decode_cond_thm] THEN
    RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, UPLOADCODE_LEM] THEN
    IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`0`,`0w`,`st`, `POS (LENGTH (arm_f:INST list) + 2)`] ENUMERATE_CJ)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `arm_f`) THEN
    FULL_SIMP_TAC std_ss [uploadCode_def] THEN
    POP_ASSUM (K ALL_TAC) THEN
    Q.ABBREV_TAC `insts1 = (((CMP,NONE,F),NONE,[v1; v2],NONE):INST)::[((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))]` THEN
    Q.ABBREV_TAC `insts2 = ((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1))) :: arm_t` THEN
    `(LENGTH arm_t + 1 = LENGTH insts2) /\ (LENGTH insts1 = 2) /\
    ((((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm_f + 2)))::
          (arm_f ++ [((B,SOME AL,F),NONE,[],SOME (POS (LENGTH arm_t + 1)))] ++ arm_t)) =
                (insts1 ++ (arm_f:INST list)) ++ insts2)` by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [] THEN
							METIS_TAC [ rich_listTheory.CONS_APPEND, APPEND_ASSOC]) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    `0 + LENGTH insts1 = FST (FST ((2,cpsr',st),{1; 0}))` by RW_TAC arith_ss [] THEN
    `?s1 pcS1. (s1,pcS1) = runTo (upload (insts1 ++ arm_f ++ insts2) (\i. ARB) 0) (FST (FST ((2,cpsr',st),{1; 0})) +
	      LENGTH arm_f) ((2,cpsr',st),{1; 0})` by METIS_TAC [ABS_PAIR_THM] THEN
    `~(LENGTH insts1 + LENGTH arm_f + LENGTH insts2 IN ((FST ((2,cpsr',st))) INSERT pcS1))` by ALL_TAC THENL [
        POP_ASSUM MP_TAC THEN
            RW_TAC std_ss [SIMP_RULE std_ss [] (Q.SPECL [`arm_f`,`insts1`,`insts2`,`0`,`\i. ARB`, `((2,cpsr',st),{1; 0}):STATEPCS`] CLOSED_MIDDLE)] THEN
            `pcS1 = SND (runTo (upload arm_f (\i. ARB) 2) (2 + LENGTH arm_f) ((2,cpsr',st),{})) UNION {1;0}`
		     by METIS_TAC [RUNTO_PCS_UNION, SND, FST, terminated] THEN
            `!x. x IN SND (runTo (upload arm_f (\i. ARB) 2) (2 + LENGTH arm_f) ((2,cpsr',st),{})) ==>
			 2 <= x /\ x < 2 + LENGTH arm_f` by METIS_TAC [closed,FST] THEN
            Q.PAT_ASSUM `LENGTH arm_t + 1 = LENGTH insts2` (ASSUME_TAC o GSYM) THEN
            FULL_SIMP_TAC set_ss [] THEN FULL_SIMP_TAC arith_ss [] THEN
            STRIP_TAC THEN RES_TAC THEN
            FULL_SIMP_TAC arith_ss [],

    `terd (upload (insts1 ++ arm_f ++ insts2) (\i. ARB) 0) (FST (FST ((2,cpsr',st),{1; 0})) + LENGTH arm_f)
						 ((2,cpsr',st),{1; 0})` by METIS_TAC [FST, TERMINATED_MIDDLE] THEN
            `LENGTH arm_f + (LENGTH arm_t + 3) = LENGTH insts1 + LENGTH arm_f + LENGTH insts2` by RW_TAC arith_ss [] THEN
             Q.PAT_ASSUM `LENGTH insts1 = 2` (K ALL_TAC) THEN
             ASM_REWRITE_TAC [] THEN
             IMP_RES_TAC RUNTO_COMPOSITION THEN ASM_REWRITE_TAC [] THEN
             NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
             POP_ASSUM (ASSUME_TAC o GSYM) THEN
             `LENGTH insts1 = 2` by (Q.UNABBREV_TAC `insts1` THEN RW_TAC list_ss []) THEN
             `runTo (upload arm_f (\i. ARB) 2) (2 + LENGTH arm_f) ((2,cpsr',st),{1; 0})= (s1,pcS1)` by METIS_TAC [FST, CLOSED_PAIR_EQ,
		        SIMP_RULE std_ss [] (Q.SPECL [`arm_f`,`insts1`,`insts2`,`0`,`\i. ARB`, `((2,cpsr',st),{1; 0}):STATEPCS`] CLOSED_MIDDLE)] THEN
             FULL_SIMP_TAC std_ss [] THEN
             `?cpsr1 st1. s1:STATE = (SUC (SUC (LENGTH arm_f)), cpsr1,st1)` by (RW_TAC arith_ss [SUC_ONE_ADD] THEN
									 METIS_TAC [TERMINATED_THM,FST, ADD_SYM, ABS_PAIR_THM]) THEN
             Q.PAT_ASSUM `LENGTH arm_t + 1 = LENGTH insts2` (ASSUME_TAC o GSYM) THEN
             FULL_SIMP_TAC std_ss [] THEN
             Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN

             RW_TAC list_ss [Once RUNTO_EXPAND_ONCE, step_def, GSYM uploadCode_def, UPLOADCODE_LEM,rich_listTheory.EL_APPEND2,
				  decode_cond_thm, decode_op_thm,goto_thm] THEN

             RW_TAC arith_ss [Once RUNTO_EXPAND_ONCE, SUC_ONE_ADD, get_st] THEN
             FULL_SIMP_TAC arith_ss [SUC_ONE_ADD, eval_fl, uploadCode_def, get_st] THEN
             METIS_TAC [get_st, status_independent, DECIDE (Term `!x.0 + x = x`), DSTATE_IRRELEVANT_PCS, FST, SND, ADD_SYM]
        ]
   );

val HOARE_CJ_FLAT_1 = Q.store_thm (
   "HOARE_CJ_FLAT_1",
   `!cond arm_t arm_f (P:P_DSTATE) (Q:P_DSTATE) (R:P_DSTATE).
          well_formed arm_t /\ well_formed arm_f /\
	  (!st. P st ==> Q (eval_fl arm_t st)) /\ (!st. P st ==> R (eval_fl arm_f st))
          ==>
          !st. (P st /\ eval_cond cond st ==> Q (eval_fl (mk_CJ cond arm_t arm_f) st)) /\
               (P st /\ ~(eval_cond cond st) ==> R (eval_fl (mk_CJ cond arm_t arm_f) st))`,
   RW_TAC std_ss [] THEN
   METIS_TAC [HOARE_CJ_FLAT_LEM_1,HOARE_CJ_FLAT_LEM_2]
   );

val HOARE_CJ_FLAT = Q.store_thm (
   "HOARE_CJ_FLAT",
   `!cond arm_t arm_f (P:P_DSTATE) (Q:P_DSTATE) (R:P_DSTATE).
          well_formed arm_t /\ well_formed arm_f /\
	  (!st. P st ==> Q (eval_fl arm_t st)) /\ (!st. P st ==> R (eval_fl arm_f st))
          ==>
          !st. (P st ==> if eval_cond cond st then Q (eval_fl (mk_CJ cond arm_t arm_f) st)
                                              else R (eval_fl (mk_CJ cond arm_t arm_f) st))`,
   RW_TAC std_ss [] THEN
   METIS_TAC [HOARE_CJ_FLAT_LEM_1,HOARE_CJ_FLAT_LEM_2]
   );


(*---------------------------------------------------------------------------------*)
(*      Tail Recursion Composition                                                 *)
(*---------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------------*)
(*      The well-founded behaviors of finite loops                                 *)
(*      There exsits a number identifing the minimal number of rounds for the loop *)
(*      condition to hold, i.e. the number of rounds executed until the loop       *)
(*      terminates                                                                 *)
(*      The WF_Loop specifies a case where the loop would surely terminates,       *)
(*          it is built on a well-founded relation on states of consecutive rounds *)
(*---------------------------------------------------------------------------------*)

val WF_Loop = Define `
    WF_Loop (cond_f,g) =
        ?R. WF R /\ (!s. ~(cond_f s) ==> R (g s) s)`;

val WF_LOOP_IMP_TER = Q.store_thm (
    "WF_LOOP_IMP_TER",
    `!g cond_f. WF_Loop (cond_f,g) ==>
              !s. ?k. cond_f (FUNPOW g k s)`,
    RW_TAC std_ss [WF_Loop] THEN
    IMP_RES_TAC WHILE_INDUCTION THEN
    POP_ASSUM (ASSUME_TAC o Q.SPECL [`g`,`$~ o cond_f`]) THEN
    FULL_SIMP_TAC list_ss [] THEN
    RES_TAC THEN
    `!s.(~cond_f s ==> ?k. cond_f (FUNPOW g k (g s))) ==> ?k.cond_f(FUNPOW g k s)` by ALL_TAC THENL [
        REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
        Cases_on `cond_f s` THENL [
             Q.EXISTS_TAC `0` THEN
             METIS_TAC [FUNPOW_THM_1],
             Q.EXISTS_TAC `k + 1` THEN
             METIS_TAC [GSYM FUNPOW, SUC_ONE_ADD, ADD_SYM]
             ],
         POP_ASSUM MP_TAC THEN
         POP_ASSUM (ASSUME_TAC o Q.SPEC `\v.?k.cond_f (FUNPOW g k v)`) THEN
         METIS_TAC []
    ]
 );

val WF_LOOP_IMP_STOPAT = Q.store_thm (
    "WF_LOOP_IMP_STOPAT",
    `!g cond_f s. WF_Loop (cond_f,g) ==>
              stopAt cond_f g x`,
    RW_TAC std_ss [stopAt_def] THEN
    METIS_TAC [WF_LOOP_IMP_TER]
 );

val LOOP_SHORTEST_LESS_LEAST = Q.store_thm (
    "LOOP_SHORTEST_LESS_LEAST",
    `!i s g cond_f.
        (i < shortest cond_f g s ==> ~cond_f (FUNPOW g i s))`,
    RW_TAC list_ss [shortest_def] THEN
    METIS_TAC [Q.SPEC `\k. cond_f (FUNPOW f k s)` LESS_LEAST]
  );

val LOOP_SHORTEST_THM = Q.store_thm (
    "LOOP_SHORTEST_THM",
    `!i s g cond_f. WF_Loop (cond_f,g) ==>
        (i <= shortest cond_f g s ==> (shortest cond_f g s  = shortest cond_f g (FUNPOW g i s) + i))`,
    RW_TAC list_ss [] THEN
    IMP_RES_TAC WF_LOOP_IMP_TER THEN
    POP_ASSUM (ASSUME_TAC o (Q.SPEC `s`)) THEN
    FULL_SIMP_TAC list_ss [shortest_def] THEN
    IMP_RES_TAC (SIMP_RULE std_ss  [] (Q.SPEC `\n.cond_f (FUNPOW g n s)` LEAST_ADD_LEM)) THEN
    RW_TAC arith_ss [SIMP_RULE std_ss [FUN_EQ_THM] FUNPOW_FUNPOW, ADD_SYM]
  );

val WF_LOOP_IMP_LEAST = Q.store_thm (
    "WF_LOOP_IMP_LEAST",
    `!cond_f g. WF_Loop (cond_f,g) ==>
                   !s. cond_f (FUNPOW g (shortest cond_f g s) s)`,
    RW_TAC list_ss [shortest_def] THEN
    IMP_RES_TAC WF_LOOP_IMP_TER THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `s`) THEN
    METIS_TAC [Q.SPEC `\k. cond_f (FUNPOW g k s)` LEAST_INTRO]
   );

val UNROLL_LOOP = Q.store_thm (
   "UNROLL_LOOP",
   `!P g x. WF_Loop (P,g) ==>
       (WHILE ($~ o P) g x = (FUNPOW g (shortest P g x) x))`,
      Induct_on `shortest P g x` THENL [
           RW_TAC list_ss [] THEN
               IMP_RES_TAC WF_LOOP_IMP_LEAST THEN
               POP_ASSUM (ASSUME_TAC o Q.SPEC `x`) THEN
               PAT_ASSUM ``0 = x`` (ASSUME_TAC o GSYM) THEN
               FULL_SIMP_TAC arith_ss [Once WHILE,FUNPOW],
           REPEAT GEN_TAC THEN
               POP_ASSUM (ASSUME_TAC o Q.SPECL [`P`,`g`,`g (x:'a)`]) THEN
               STRIP_TAC THEN
               POP_ASSUM (ASSUME_TAC o GSYM) THEN
               STRIP_TAC THEN
               `SUC 0 <= shortest P g x` by RW_TAC arith_ss [] THEN
               IMP_RES_TAC LOOP_SHORTEST_THM THEN
               POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [FUNPOW]) THEN
               `v = shortest P g (g x)` by RW_TAC arith_ss [] THEN
               `0 < shortest P g x` by RW_TAC arith_ss [] THEN
               IMP_RES_TAC LOOP_SHORTEST_LESS_LEAST THEN
               REWRITE_TAC [Once WHILE] THEN
               FULL_SIMP_TAC arith_ss [FUNPOW] THEN
               METIS_TAC [FUNPOW, DECIDE (Term`shortest P g (g x) + 1 = SUC (shortest P g (g x))`)]
       ]
  );

(*---------------------------------------------------------------------------------*)
(*      Induction on the number of rounds,                                         *)
(*---------------------------------------------------------------------------------*)

val LENGTH_TR = Q.store_thm (
   "LENGTH_TR",
   `!cond arm. LENGTH (mk_TR cond arm) =  LENGTH arm + 3`,
   REPEAT STRIP_TAC THEN
   `?v1 rop v2. cond = (v1,rop,v2)` by METIS_TAC [ABS_PAIR_THM] THEN
   RW_TAC list_ss [mk_TR]
  );


val WF_TR = Define `
    WF_TR (cond,arm) =
        !iB. WF_Loop ((\s:STATEPCS.eval_cond cond (SND (SND (FST s)))),
               (\s:STATEPCS.runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s))`;

val loopNum = Define `
    loopNum cond arm iB = shortest (\s'.eval_cond cond (get_st s')) (\s'.runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm) s')`;

val LOOPNUM_BASIC = Q.store_thm (
    "LOOPNUM_BASIC",
    `!n cond arm. WF_TR (cond,arm) /\ (loopNum cond arm iB s = 0) ==>
         eval_cond cond (get_st s)`,
     RW_TAC std_ss [WF_TR, loopNum] THEN
     Q.PAT_ASSUM `!iB.x` (ASSUME_TAC o Q.SPEC `iB`) THEN IMP_RES_TAC WF_LOOP_IMP_STOPAT THEN
     POP_ASSUM (ASSUME_TAC o Q.SPEC `s:STATEPCS`) THEN
     FULL_SIMP_TAC std_ss [GSYM get_st] THEN
     METIS_TAC [Q.SPECL [`s:STATEPCS`,`(\s. eval_cond cond (get_st s))`, `(\s'. runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm) s')`]
         (INST_TYPE [alpha|->Type `:STATEPCS`] SHORTEST_LEM)]
  );

val LOOPNUM_INDUCTIVE = Q.store_thm (
    "LOOPNUM_INDUCTIVE",
    `!n cond arm. WF_TR (cond,arm) /\ (loopNum cond arm iB s = SUC n) ==>
        ~eval_cond cond (get_st s) /\ (n = loopNum cond arm iB (runTo (upload arm iB (FST (FST s))) (FST (FST s) + LENGTH arm) s))`,
     REWRITE_TAC [WF_TR, loopNum] THEN NTAC 4 STRIP_TAC THEN
     Q.PAT_ASSUM `!iB.x` (ASSUME_TAC o Q.SPEC `iB`) THEN IMP_RES_TAC WF_LOOP_IMP_STOPAT THEN
     POP_ASSUM (ASSUME_TAC o Q.SPEC `s:STATEPCS`) THEN
     FULL_SIMP_TAC std_ss [GSYM get_st] THEN
     METIS_TAC [Q.SPECL [`(\s. eval_cond cond (get_st s))`, `(\s'. runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm) s')`,`s:STATEPCS`]
         (INST_TYPE [alpha|->Type `:STATEPCS`] SHORTEST_INDUCTIVE)]
  );


val LOOPNUM_INDEPENDENT_OF_CPSR_PCS = Q.store_thm (
    "LOOPNUM_INDEPENDENT_OF_CPSR_PCS",
    `!cond arm iB pc0 pc1 cpsr0 cpsr1 st pcS0 pcS1.
        well_formed arm /\ WF_TR (cond,arm) ==>
            (loopNum cond arm iB ((pc0,cpsr0,st),pcS0) = loopNum cond arm iB ((pc1,cpsr1,st),pcS1))`,
    Induct_on `loopNum cond arm iB ((pc0,cpsr0,st),pcS0)` THENL [
        RW_TAC std_ss [WF_TR] THEN
            POP_ASSUM (ASSUME_TAC o Q.SPEC `iB`) THEN IMP_RES_TAC WF_LOOP_IMP_STOPAT THEN
            FIRST_ASSUM (ASSUME_TAC o Q.SPEC `((pc0,cpsr0,st),pcS0):STATEPCS`) THEN
            FULL_SIMP_TAC std_ss [loopNum,get_st] THEN
            IMP_RES_TAC SHORTEST_LEM THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
            `(\s. eval_cond cond (SND (SND (FST s)))) ((pc1,cpsr1,st),pcS1)` by METIS_TAC [SND,FST] THEN
            METIS_TAC [Q.SPECL [`((pc1,cpsr1,st),pcS):STATEPCS`,`(\s. eval_cond cond (SND (SND (FST s))))`]
		       (INST_TYPE [alpha|->Type `:STATEPCS`] SHORTEST_LEM)],
        REWRITE_TAC [Once EQ_SYM_EQ] THEN FULL_SIMP_TAC std_ss [loopNum, get_st] THEN
            REPEAT STRIP_TAC THEN
            FIRST_ASSUM (ASSUME_TAC o Q.SPEC `iB` o REWRITE_RULE [WF_TR]) THEN
            IMP_RES_TAC WF_LOOP_IMP_STOPAT THEN
            FIRST_ASSUM (ASSUME_TAC o Q.SPEC `((pc0,cpsr0,st),pcS0):STATEPCS`) THEN
            IMP_RES_TAC SHORTEST_INDUCTIVE THEN
            `?pc' cpsr' st' pcS'. runTo (upload arm iB pc0) (pc0 + LENGTH arm) ((pc0,cpsr0,st),pcS0) = ((pc',cpsr',st'),pcS')`
                by METIS_TAC [ABS_PAIR_THM] THEN
            Q.PAT_ASSUM `!cond arm iB pc cpsr0 st pcS0.x` (ASSUME_TAC o Q.SPECL [`cond`,`arm`,`iB`,`pc'`,`cpsr'`,`st'`,`pcS'`]) THEN
            `~(\s. eval_cond cond (SND (SND (FST s)))) (((pc1,cpsr1,st),pcS1):STATEPCS)` by METIS_TAC [SND,FST] THEN
            Q.PAT_ASSUM `!x.stopAT x y x` (ASSUME_TAC o Q.SPEC `((pc1,cpsr1,st),pcS1):STATEPCS`) THEN
            `1 <= shortest (\s'. eval_cond cond (SND (SND (FST s')))) (\s'.runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm)
			s') ((pc1,cpsr1,st),pcS1)` by METIS_TAC  [Q.SPECL [`((pc1,cpsr1,st),pcS):STATEPCS`,`(\s. eval_cond cond (SND (SND (FST s))))`]
		       (INST_TYPE [alpha|->Type `:STATEPCS`] SHORTEST_LEM)] THEN
            IMP_RES_TAC SHORTEST_THM THEN ASM_REWRITE_TAC [DECIDE (Term `1 = SUC 0`), FUNPOW] THEN
            REWRITE_TAC [DECIDE (Term `!x.x + SUC 0 = SUC x`), prim_recTheory.INV_SUC_EQ] THEN
            NTAC 4 (POP_ASSUM (K ALL_TAC)) THEN
            `?pc'' cpsr'' pcS''. runTo (upload arm iB pc1) (pc1 + LENGTH arm) ((pc1,cpsr1,st),pcS1) = ((pc'',cpsr'',st'),pcS'')` by ALL_TAC THENL [
                      `st' = SND (SND (FST (runTo (upload arm iB pc1) (pc1 + LENGTH arm) ((pc1,cpsr1,st),pcS1))))`by
                          METIS_TAC [DSTATE_IRRELEVANT_PCS, status_independent, well_formed, FST, get_st,SND] THEN
                      Q.EXISTS_TAC `FST (FST (runTo (upload arm iB pc1) (pc1 + LENGTH arm) ((pc1,cpsr1,st),pcS1)))` THEN
                      Q.EXISTS_TAC `FST (SND (FST (runTo (upload arm iB pc1) (pc1 + LENGTH arm) ((pc1,cpsr1,st),pcS1))))` THEN
                      Q.EXISTS_TAC `SND (runTo (upload arm iB pc1) (pc1 + LENGTH arm) ((pc1,cpsr1,st),pcS1))` THEN
                      RW_TAC std_ss [],
                  FULL_SIMP_TAC std_ss [] THEN RES_TAC
            ]
        ]
   );


val TR_TERMINATED_LEM = Q.store_thm (
   "TR_TERMINATED_LEM",
   `!cond arm s iB.
        well_formed arm /\ WF_TR (cond,arm)
          ==> terd (upload (mk_TR cond arm) iB (FST (FST s))) (FST(FST s) + LENGTH (mk_TR cond arm)) s`,
    REPEAT GEN_TAC THEN
    Induct_on `loopNum cond arm iB s` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [terd_def, stopAt_def, LENGTH_TR] THEN
            IMP_RES_TAC LOOPNUM_BASIC THEN
            Q.EXISTS_TAC `SUC (SUC 0)` THEN
            `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st pcS. s = ((pc,cpsr,st),pcS))` by METIS_TAC [ABS_PAIR_THM] THEN
            `0 < LENGTH (mk_TR (v1,rop,v2) arm)` by (RW_TAC list_ss [LENGTH_TR]) THEN
            `((upload (mk_TR (v1,rop,v2) arm) iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload (mk_TR (v1,rop,v2) arm) iB pc) (pc+1) =
                 ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2))))` by (FULL_SIMP_TAC std_ss [mk_TR] THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                  IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
            RW_TAC list_ss [FUNPOW, step_def, decode_cond_thm] THEN
            IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm:INST list) + 2)`] ENUMERATE_CJ)) THEN
            POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [get_st] o Q.SPECL [`pc`,`cpsr`,`arm`]) THEN
            FULL_SIMP_TAC std_ss [] THEN RW_TAC arith_ss [goto_def],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [terd_def, stopAt_def, LENGTH_TR] THEN
            IMP_RES_TAC LOOPNUM_INDUCTIVE THEN
            `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st pcS. s = ((pc,cpsr,st),pcS))` by METIS_TAC [ABS_PAIR_THM] THEN
            FULL_SIMP_TAC std_ss [terd_def,stopAt_def] THEN
            NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
            `?cpsr1. FUNPOW (step (upload (mk_TR (v1,rop,v2) arm) iB pc)) 2 ((pc,cpsr,st),pcS) = ((pc+2,cpsr1,st),pc+1 INSERT pc INSERT pcS)`
               by (`0 < LENGTH (mk_TR (v1,rop,v2) arm)` by RW_TAC list_ss [LENGTH_TR] THEN
               `((upload (mk_TR (v1,rop,v2) arm) iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload (mk_TR (v1,rop,v2) arm) iB pc) (pc+1) =
                 ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2))))` by (POP_ASSUM (ASSUME_TAC o REWRITE_RULE [mk_TR]) THEN
                    RW_TAC list_ss [mk_TR, UPLOAD_LEM] THEN IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
               REWRITE_TAC [DECIDE ``2 = SUC 1``] THEN
               RW_TAC list_ss [FUNPOW, step_def, decode_cond_thm] THEN
               REWRITE_TAC [DECIDE ``1 = SUC 0``] THEN
               RW_TAC list_ss [FUNPOW, step_def] THEN
               IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm:INST list) + 2)`] ENUMERATE_CJ)) THEN
               POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [get_st] o Q.SPECL [`pc`,`cpsr`,`arm`]) THEN
               FULL_SIMP_TAC std_ss []) THEN

            `?cpsr' pcS'. FUNPOW (step (upload (mk_TR (v1,rop,v2) arm) iB pc)) (1 + shortest (\s':STATEPCS.FST (FST s') = pc + 2 + LENGTH arm)
                     (step (upload (mk_TR (v1,rop,v2) arm) iB pc)) ((pc+2,cpsr1,st),pc + 1 INSERT pc INSERT pcS) + 2) ((pc,cpsr,st),pcS) =
                        ((pc,cpsr',get_st(runTo (upload arm iB pc) (pc+LENGTH arm) ((pc,cpsr,st),pcS))),pcS')` by ALL_TAC THENL [
               RW_TAC std_ss [GSYM FUNPOW_FUNPOW] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
               Q.ABBREV_TAC `insts1 = (((CMP,NONE,F),NONE,[v1; v2],NONE):INST)::[((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))]` THEN
               Q.ABBREV_TAC `insts2 = [((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm + 2))):INST]` THEN
               `(LENGTH insts2 = 1) /\ (2 = LENGTH insts1) /\ (mk_TR (v1,rop,v2) arm = insts1 ++ (arm:INST list) ++ insts2)`
                    by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [mk_TR] THEN
							METIS_TAC [ rich_listTheory.CONS_APPEND, APPEND_ASSOC]) THEN
               ASM_REWRITE_TAC [] THEN
               `stopAt (\s'. FST (FST s') = pc + LENGTH insts1 + LENGTH arm) (step (upload (insts1 ++ arm ++ insts2) iB pc)) ((pc + LENGTH insts1,
                 cpsr1,st), pc + 1 INSERT pc INSERT pcS)` by METIS_TAC [SIMP_RULE list_ss []
			 (Q.SPECL [`arm`,`insts1`,`insts2`] TERMINATED_MIDDLE),FST,well_formed,terd_def] THEN
               IMP_RES_TAC UNROLL_RUNTO THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
               NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN FULL_SIMP_TAC std_ss [well_formed] THEN
               IMP_RES_TAC (SIMP_RULE std_ss [] (Q.SPECL [`arm`,`insts1:INST list`,`insts2`,`pc`,`iB`,
                    `((pc + LENGTH (insts1:INST list),cpsr1,st),pc + 1 INSERT pc INSERT pcS):STATEPCS`] CLOSED_MIDDLE)) THEN
               RW_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
               Q.ABBREV_TAC `s10 = runTo (upload arm iB (pc+LENGTH insts1)) (pc + LENGTH insts1 + LENGTH arm) ((pc + LENGTH insts1,cpsr1,st),
                 pc + 1 INSERT pc INSERT pcS)` THEN
              `SND (SND (FST s10)) =  SND (SND (FST (runTo (upload arm iB pc) (pc+LENGTH arm) ((pc,cpsr,st),pcS))))` by
                 (Q.UNABBREV_TAC `s10` THEN METIS_TAC [get_st, DSTATE_IRRELEVANT_PCS, status_independent, FST, ADD_SYM]) THEN
              `FST (FST s10) = pc + LENGTH insts1 + LENGTH arm` by (Q.UNABBREV_TAC `s10` THEN METIS_TAC [TERMINATED_THM,FST]) THEN
              `?cpsr2. s10 = ((FST (FST s10),cpsr2,SND (SND (FST s10))),SND s10)` by METIS_TAC [ABS_PAIR_THM,FST,SND] THEN
               ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [DECIDE (Term`1 = SUC 0`)] THEN
               RW_TAC std_ss [FUNPOW] THEN
               `(upload (insts1++arm++insts2) iB pc) (pc+(LENGTH arm+LENGTH (insts1:INST list)))=((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm+2)))`
                  by (
                   Q.PAT_ASSUM `2 = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN
	           Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN
                   REPEAT (POP_ASSUM (K ALL_TAC)) THEN RW_TAC list_ss [] THEN
                      `LENGTH (arm:INST list) + 2 < LENGTH  (((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))
                         :: (arm ++ [((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm + 2))):INST]))` by RW_TAC list_ss [] THEN
                      RW_TAC list_ss [UPLOAD_LEM] THEN
                      `LENGTH (((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))::arm) <=  LENGTH arm + 2`
                         by RW_TAC list_ss [] THEN
                    IMP_RES_TAC rich_listTheory.EL_APPEND2 THEN
                    FULL_SIMP_TAC list_ss [SUC_ONE_ADD]
                    ) THEN
                RW_TAC list_ss [step_def, decode_cond_thm, decode_op_thm, goto_def, get_st],

          Q.PAT_ASSUM `!cond1 arm1 iB1 s1.x` (ASSUME_TAC o SIMP_RULE std_ss [LENGTH_TR] o Q.SPECL [`(v1,rop,v2)`,`arm`,`iB`,
                  `((pc,cpsr',get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS))),pcS')`]) THEN
              `loopNum (v1,rop,v2) arm iB (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS)) =
               loopNum (v1,rop,v2) arm iB ((pc,cpsr', get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS))),pcS')` by
                    METIS_TAC [ABS_PAIR_THM, LOOPNUM_INDEPENDENT_OF_CPSR_PCS, get_st, FST, SND] THEN RES_TAC THEN
              POP_ASSUM MP_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN STRIP_TAC THEN
              Q.ABBREV_TAC `n'' = 1 + shortest (\s'. FST (FST s') = pc + 2 + LENGTH arm) (step (upload (mk_TR (v1,rop,v2) arm) iB pc))
                  ((pc + 2,cpsr1,st),pc + 1 INSERT pc INSERT pcS) + 2` THEN
              Q.EXISTS_TAC `n' + n''` THEN
              RW_TAC arith_ss [GSYM FUNPOW_FUNPOW]
          ]
        ]
   );

val FUNPOW_DSTATE = Q.store_thm (
   "FUNPOW_DSTATE",
  `!n arm iB pc0 pc1 cpsr0 cpsr1 st pcS0 pcS1.
     well_formed arm ==>
     (get_st (FUNPOW (\s'. runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm) s') n ((pc0,cpsr0,st),pcS0)) =
      get_st (FUNPOW (\s'. runTo (upload arm iB (FST (FST s'))) (FST (FST s') + LENGTH arm) s') n ((pc1,cpsr1,st),pcS1)))`,
   Induct_on `n` THENL [
       RW_TAC std_ss [get_st, FUNPOW],
       RW_TAC std_ss [FUNPOW] THEN
       `get_st (runTo (upload arm iB pc0) (pc0 + LENGTH arm) ((pc0,cpsr0,st),pcS0)) = get_st (runTo (upload arm iB pc1) (pc1 + LENGTH arm)
            ((pc1,cpsr1,st),pcS1))` by METIS_TAC [DSTATE_IRRELEVANT_PCS, status_independent, well_formed, FST, get_st] THEN
       METIS_TAC [ABS_PAIR_THM, FST, SND, get_st]
   ]
   );

val _ = (Globals.priming := SOME "");

val UNROLL_TR_LEM = Q.store_thm (
   "UNROLL_TR_LEM",
   `!cond arm iB s pcS.
        well_formed arm /\ WF_TR (cond,arm) /\ ~(FST s + LENGTH (mk_TR cond arm) IN pcS) ==>
        ?cpsr' pcS' cpsr''. (runTo (upload (mk_TR cond arm) iB (FST s)) (FST s + LENGTH (mk_TR cond arm)) (s,pcS) =
            ((FST s + LENGTH (mk_TR cond arm), cpsr', get_st (FUNPOW (\s'.runTo (upload arm iB (FST (FST s')))
                (FST (FST s')+LENGTH arm) s') (loopNum cond arm iB (s,pcS)) (s,pcS))), pcS')) /\
            !x. x IN pcS' DIFF pcS ==> FST s <= x /\ x < FST s + LENGTH (mk_TR cond arm)`,

    REPEAT GEN_TAC THEN
    Induct_on `loopNum cond arm iB (s,pcS)` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [LENGTH_TR, FUNPOW] THEN
          IMP_RES_TAC LOOPNUM_BASIC THEN
          `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
          `0 < LENGTH (mk_TR (v1,rop,v2) arm)` by (RW_TAC list_ss [LENGTH_TR]) THEN
          `((upload (mk_TR (v1,rop,v2) arm) iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload (mk_TR (v1,rop,v2) arm) iB pc) (pc+1) =
               ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2))))` by (FULL_SIMP_TAC std_ss [mk_TR] THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
          RW_TAC list_ss [Once RUNTO_ADVANCE, step_def, decode_cond_thm] THEN
          RW_TAC list_ss [Once RUNTO_ADVANCE, step_def] THEN
          IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm:INST list) + 2)`] ENUMERATE_CJ)) THEN
          POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [get_st] o Q.SPECL [`pc`,`cpsr`,`arm`]) THEN
          FULL_SIMP_TAC std_ss [] THEN RW_TAC arith_ss [goto_def] THEN
          RW_TAC set_ss [Once RUNTO_ADVANCE, get_st] THEN RW_TAC arith_ss [],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [LENGTH_TR, FUNPOW] THEN
            IMP_RES_TAC LOOPNUM_INDUCTIVE THEN
            `(?v1 rop v2. cond = (v1,rop,v2)) /\ (?pc cpsr st pcS. s = (pc,cpsr,st))` by METIS_TAC [ABS_PAIR_THM] THEN
            FULL_SIMP_TAC std_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
            `0 < LENGTH (mk_TR (v1,rop,v2) arm)` by (RW_TAC list_ss [LENGTH_TR]) THEN
            `((upload (mk_TR (v1,rop,v2) arm) iB pc) pc = ((CMP,NONE,F),NONE,[v1; v2],NONE)) /\ ((upload (mk_TR (v1,rop,v2) arm) iB pc) (pc+1) =
               ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2))))` by (FULL_SIMP_TAC std_ss [mk_TR] THEN RW_TAC list_ss [UPLOAD_LEM] THEN
                IMP_RES_TAC UPLOAD_LEM THEN FULL_SIMP_TAC list_ss []) THEN
            RW_TAC list_ss [Once RUNTO_ADVANCE, step_def, decode_cond_thm] THEN
            RW_TAC list_ss [Once RUNTO_ADVANCE, step_def] THEN
            IMP_RES_TAC (SIMP_RULE arith_ss [] (Q.SPECL [`(v1,rop,v2)`,`pc`,`cpsr:DATA`,`st`, `POS (LENGTH (arm:INST list) + 2)`] ENUMERATE_CJ)) THEN
            POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [get_st] o Q.SPECL [`pc`,`cpsr`,`arm`]) THEN
            FULL_SIMP_TAC std_ss [] THEN NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN

            Q.ABBREV_TAC `insts1 = (((CMP,NONE,F),NONE,[v1; v2],NONE):INST)::[((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))]` THEN
            Q.ABBREV_TAC `insts2 = [((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm + 2))):INST]` THEN
            `(LENGTH insts2 = 1) /\ (2 = LENGTH insts1) /\ (mk_TR (v1,rop,v2) arm = insts1 ++ (arm:INST list) ++ insts2)`
                 by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [mk_TR] THEN
				METIS_TAC [ rich_listTheory.CONS_APPEND, APPEND_ASSOC]) THEN
            ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
            `?s1 pcS1. (s1,pcS1) = runTo (upload (insts1 ++ arm ++ insts2) iB pc) (pc + LENGTH (insts1:INST list) + LENGTH arm)
                  ((pc + LENGTH (insts1:INST list),cpsr',st),pc + 1 INSERT pc INSERT pcS)` by METIS_TAC [ABS_PAIR_THM] THEN
            `~(pc + (LENGTH arm + 3) IN (FST ((pc + LENGTH insts1,cpsr',st)) INSERT pcS1))` by (
               POP_ASSUM MP_TAC THEN FULL_SIMP_TAC std_ss [well_formed] THEN
               RW_TAC std_ss [SIMP_RULE std_ss [] (Q.SPECL [`arm`,`insts1`,`insts2`,`pc`,`iB`, `((pc + LENGTH (insts1:INST list),cpsr',st),
                   pc + 1 INSERT pc INSERT pcS) :STATEPCS`] CLOSED_MIDDLE)] THEN
               `pcS1 = SND (runTo (upload arm iB (pc+2)) (pc + 2 + LENGTH arm) ((pc+2,cpsr',st),{})) UNION (pc+1 INSERT pc INSERT pcS)`
		     by METIS_TAC [RUNTO_PCS_UNION, SND, FST, terminated] THEN
               `!x. x IN SND (runTo (upload arm iB (pc+2)) (pc + 2 + LENGTH arm) ((pc + 2,cpsr',st),{})) ==>
			 pc + 2 <= x /\ x < pc + 2 + LENGTH arm` by METIS_TAC [closed,FST] THEN
               FULL_SIMP_TAC set_ss [] THEN FULL_SIMP_TAC arith_ss [] THEN
               STRIP_TAC THEN Q.PAT_ASSUM `2 = LENGTH insts1` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN
               RES_TAC THEN FULL_SIMP_TAC arith_ss []
            ) THEN

            `terd (upload (insts1 ++ arm ++ insts2) iB pc) (pc + LENGTH (insts1:INST list) + LENGTH arm)
		    ((pc+LENGTH(insts1:INST list),cpsr',st),pc+1 INSERT pc INSERT pcS)` by METIS_TAC [FST, well_formed, TERMINATED_MIDDLE] THEN
            IMP_RES_TAC RUNTO_COMPOSITION THEN Q.PAT_ASSUM `(s1,pcS1) = x` (ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
            `(get_st (s1,pcS1) = get_st (runTo (upload arm iB pc) (pc+LENGTH arm) ((pc,cpsr,st),{}))) /\
             (FST (FST (s1,pcS1)) = pc + LENGTH insts1 + LENGTH arm) /\
             (pcS1 = SND (runTo (upload arm iB (pc+LENGTH (insts1:INST list))) (pc+LENGTH (insts1:INST list)+LENGTH arm)
                     ((pc+LENGTH (insts1:INST list),cpsr',st),{})) UNION (pc+1 INSERT pc INSERT pcS))` by
                 METIS_TAC [DSTATE_IRRELEVANT_PCS, status_independent, SIMP_RULE std_ss [] (Q.SPECL [`arm`,`insts1:INST list`,`insts2`,`pc`,
                      `iB`,`((pc + LENGTH (insts1:INST list),cpsr',st), pc + 1 INSERT pc INSERT pcS):STATEPCS`] CLOSED_MIDDLE),
                      well_formed, FST, TERMINATED_THM,RUNTO_PCS_UNION, terminated, SND] THEN
            `?cpsr2. s1 = (FST (FST (s1,pcS1)),cpsr2,get_st(s1,pcS1))` by METIS_TAC [ABS_PAIR_THM,FST,SND, get_st] THEN
            ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN RW_TAC std_ss [] THEN NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN

            `(upload (insts1++arm++insts2) iB pc) (pc+(LENGTH arm+LENGTH (insts1:INST list)))=((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm+2)))` by (
                   Q.PAT_ASSUM `2 = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN
	           Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN
                   REPEAT (POP_ASSUM (K ALL_TAC)) THEN RW_TAC list_ss [] THEN
                      `LENGTH (arm:INST list) + 2 < LENGTH  (((CMP,NONE,F),NONE,[v1; v2],NONE)::((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))
                         :: (arm ++ [((B,SOME AL,F),NONE,[],SOME (NEG (LENGTH arm + 2))):INST]))` by RW_TAC list_ss [] THEN
                      RW_TAC list_ss [UPLOAD_LEM] THEN
                      `LENGTH (((CMP,NONE,F),NONE,[v1; v2],NONE):: ((B,SOME rop,F),NONE,[],SOME (POS (LENGTH arm + 2)))::arm) <=  LENGTH arm + 2`
                         by RW_TAC list_ss [] THEN
                    IMP_RES_TAC rich_listTheory.EL_APPEND2 THEN
                    FULL_SIMP_TAC list_ss [SUC_ONE_ADD]
            ) THEN
            RW_TAC list_ss [Once RUNTO_ADVANCE, step_def, decode_cond_thm, decode_op_thm, goto_def] THEN

           Q.ABBREV_TAC `pcS10 = pc + (LENGTH arm + LENGTH insts1) INSERT SND (runTo (upload arm iB (pc + LENGTH insts1))
               (pc + (LENGTH arm + LENGTH insts1)) ((pc + LENGTH insts1,cpsr',st),{})) UNION (pc + 1 INSERT pc INSERT pcS)` THEN
           Q.PAT_ASSUM `!cond1 arm1 iB1 s pcS1.x` (ASSUME_TAC o SIMP_RULE std_ss [LENGTH_TR] o Q.SPECL [`(v1,rop,v2)`,`arm`,`iB`,
               `(pc,cpsr2,get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),{})))`, `pcS10`]) THEN
           `loopNum (v1,rop,v2) arm iB (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS)) =
            loopNum (v1,rop,v2) arm iB ((pc,cpsr2, get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),{}))),pcS10)` by
                    METIS_TAC [ABS_PAIR_THM, LOOPNUM_INDEPENDENT_OF_CPSR_PCS, get_st, FST, SND, DSTATE_IRRELEVANT_PCS, well_formed] THEN
           `~(pc + (LENGTH arm + 3) IN pcS10)` by (
               Q.UNABBREV_TAC `pcS10` THEN
               FULL_SIMP_TAC set_ss [] THEN FULL_SIMP_TAC arith_ss [] THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
               FULL_SIMP_TAC std_ss [well_formed, closed] THEN
               Q.PAT_ASSUM `!s iB x.k` (ASSUME_TAC o Q.SPECL [`(pc + LENGTH (insts1:INST list),cpsr',st)`,`iB`]) THEN
               `!x. x IN SND (runTo (upload arm iB (pc + LENGTH insts1)) (pc + (LENGTH arm + LENGTH insts1)) ((pc + LENGTH insts1,cpsr',st),{})) ==>
                 pc + LENGTH insts1 <= x /\ x < pc + LENGTH insts1 + LENGTH arm` by METIS_TAC [ADD_SYM,ADD_ASSOC,FST] THEN
               STRIP_TAC THEN RES_TAC THEN
               FULL_SIMP_TAC arith_ss []
            ) THEN

           `insts1 ++ arm ++ insts2 = mk_TR (v1,rop,v2) arm` by (Q.UNABBREV_TAC `insts1` THEN Q.UNABBREV_TAC `insts2` THEN RW_TAC list_ss [mk_TR]) THEN
           RES_TAC THEN FULL_SIMP_TAC arith_ss [] THEN STRIP_TAC THENL [
               NTAC 19 (POP_ASSUM (K ALL_TAC)) THEN
                   `get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS)) =
                       get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),{}))` by METIS_TAC [DSTATE_IRRELEVANT_PCS,FST,well_formed] THEN
                   `?pc'' cpsr'' pc'' pcS''. runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS) =
                                   ((pc'',cpsr'',get_st (runTo (upload arm iB pc) (pc + LENGTH arm) ((pc,cpsr,st),{}))),pcS'')` by
                   METIS_TAC [get_st, FST, SND, ABS_PAIR_THM] THEN
                   METIS_TAC [FUNPOW_DSTATE, ABS_PAIR_THM, FST, SND],

               `pcS'3 = pcS'` by METIS_TAC [] THEN
               NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 11 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
               Q.UNABBREV_TAC `pcS10` THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN Q.PAT_ASSUM `loopNum x y z p = q` (K ALL_TAC) THEN
               POP_ASSUM (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC set_ss [] THEN NTAC 5 STRIP_TAC THEN
               FULL_SIMP_TAC set_ss [] THEN Q.PAT_ASSUM `!x1.k` (ASSUME_TAC o Q.SPEC `x`) THEN
               FULL_SIMP_TAC arith_ss [] THEN
               Cases_on `(x = pc + 1) \/ (x = pc) \/ (x = pc + (LENGTH (arm:INST list) + LENGTH (insts1:INST list)))` THENL [
                   RW_TAC arith_ss [],
                   FULL_SIMP_TAC arith_ss [] THEN
                   Cases_on `x IN SND (runTo (upload arm iB (pc + LENGTH insts1)) (pc + (LENGTH (arm:INST list) + LENGTH (insts1:INST list)))
                               ((pc + LENGTH (insts1:INST list),cpsr',st),{}))` THENL [
                       FULL_SIMP_TAC arith_ss [well_formed, closed] THEN
                       Q.PAT_ASSUM `!s iB x.k` (ASSUME_TAC o Q.SPECL [`(pc + LENGTH (insts1:INST list),cpsr',st):STATE`,`iB`,`x`]) THEN
                       `pc + 2  <= x /\ x < pc + 2 + LENGTH arm` by METIS_TAC [FST, ADD_SYM, ADD_ASSOC] THEN
                       RW_TAC arith_ss [],
                       FULL_SIMP_TAC arith_ss [] THEN METIS_TAC []
                   ]
               ]
          ]
     ]
  );


val _ = (Globals.priming := NONE);

val TR_IS_WELL_FORMED = Q.store_thm (
   "TR_IS_WELL_FORMED",
   `!cond arm. well_formed arm /\ WF_TR (cond,arm)
           ==> well_formed (mk_TR cond arm)`,
   REPEAT STRIP_TAC THEN
   RW_TAC std_ss [well_formed, terminated, status_independent] THENL [
       SIMP_TAC std_ss [closed] THEN REPEAT GEN_TAC THEN
           METIS_TAC [SND,SIMP_RULE set_ss [] (Q.SPECL [`cond`,`arm`,`iB`,`s:STATE`,`{}`] UNROLL_TR_LEM)],
       METIS_TAC [terd_def, TR_TERMINATED_LEM],
       IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`cond`,`arm`,`iB`,`(pos0,cpsr0,st):STATE`,`{}`] UNROLL_TR_LEM)) THEN
           METIS_TAC [SND,FST,get_st,FUNPOW_DSTATE, LOOPNUM_INDEPENDENT_OF_CPSR_PCS]
   ]
  );


val HOARE_TR_FLAT = Q.store_thm (
   "HOARE_TR_FLAT",
   `!cond arm_t (P:P_DSTATE).
          well_formed arm /\ WF_TR (cond,arm) /\
	  (!st. P st ==> P (eval_fl arm st)) ==>
          !st. P st ==> P (eval_fl (mk_TR cond arm) st) /\ (eval_cond cond (eval_fl (mk_TR cond arm) st))`,
    REPEAT GEN_TAC THEN SIMP_TAC std_ss [LENGTH_TR, eval_fl] THEN STRIP_TAC THEN GEN_TAC THEN
    IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`cond`,`arm`,`iB`,`s:STATE`,`{}`] UNROLL_TR_LEM)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPECL [`(0,0w,st):STATE`,`\i.ARB`]) THEN
    FULL_SIMP_TAC std_ss [LENGTH_TR, FUNPOW,get_st, uploadCode_def] THEN
    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
    Induct_on `loopNum cond arm (\i.ARB) ((0,0w,st),{})` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN REPEAT GEN_TAC THEN SIMP_TAC std_ss [FUNPOW,get_st] THEN
            NTAC 5 STRIP_TAC THEN
            METIS_TAC [LOOPNUM_BASIC, get_st, FST, SND],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN REPEAT GEN_TAC THEN SIMP_TAC std_ss [FUNPOW] THEN
            NTAC 5 STRIP_TAC THEN
            IMP_RES_TAC LOOPNUM_INDUCTIVE THEN
            `v = loopNum cond arm (\i.ARB) ((0,0w,SND (SND (FST (runTo (upload arm (\i.ARB) 0) (LENGTH arm) ((0,0w,st),{}))))),{})` by
            METIS_TAC [ABS_PAIR_THM,DECIDE (Term`!x.0+x=x`),LOOPNUM_INDEPENDENT_OF_CPSR_PCS, get_st, FST, SND, DSTATE_IRRELEVANT_PCS, well_formed] THEN
            RES_TAC THEN
            METIS_TAC [SND,FST,get_st,FUNPOW_DSTATE, ABS_PAIR_THM]
      ]
   );

(*---------------------------------------------------------------------------------*)
(*      Well-formed program upon any instB                                         *)
(*---------------------------------------------------------------------------------*)

val WELL_FORMED_INSTB_LEM = Q.store_thm (
   "WELL_FORMED_INSTB_LEM",
   `!arm iB0 iB1 (s:STATEPCS) s'.
           closed arm /\ terminated arm /\ (instB = upload arm iB0 (FST (FST s))) /\
           (?m. (s' = FUNPOW (step instB) m s) /\ m <= shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s)
            ==>
               (runTo (upload arm iB0 (FST (FST s))) (FST (FST s) + LENGTH arm) s' =
                runTo (upload arm iB1 (FST (FST s))) (FST (FST s) + LENGTH arm) s')`,

   RW_TAC std_ss [] THEN
   Q.ABBREV_TAC `instB = upload arm iB0 (FST (FST s))` THEN
   Cases_on `m = shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` THENL [
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [STOPAT_THM, terminated] THEN
           `FST (FST (FUNPOW (step instB) m s)) = FST (FST s) + LENGTH arm` by ( FULL_SIMP_TAC std_ss [stopAt_def, shortest_def] THEN
               METIS_TAC [Q.SPEC `\n.FST (FST (FUNPOW (step instB) n s)) = FST (FST s) + LENGTH arm` LEAST_INTRO]) THEN
           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE] THEN
           RW_TAC std_ss [Once RUNTO_EXPAND_ONCE],

       `m < shortest (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
       Q.PAT_ASSUM `~p` (K ALL_TAC) THEN
       `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` by METIS_TAC [STOPAT_THM, terminated] THEN
       RW_TAC std_ss [UNROLL_RUNTO] THEN
       Induct_on `shortest (\s1:STATEPCS. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) (FUNPOW (step instB) m s)` THENL [
           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               Q.ABBREV_TAC `s' = FUNPOW (step instB) m s` THEN
               `FST (FST s') = FST (FST s) + LENGTH arm` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) = FST (FST s) + LENGTH arm`]
                                                          (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)] THEN
               `?s0 pcS0. s' = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
               METIS_TAC [RUNTO_ADVANCE, FST, SND],

           REWRITE_TAC [Once EQ_SYM_EQ] THEN
               RW_TAC list_ss [FUNPOW] THEN
               IMP_RES_TAC SHORTEST_INDUCTIVE THEN
               `stopAt (\s1. FST (FST s1) = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [terminated] THEN
               `SUC m <= shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
               `v + SUC m = shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by METIS_TAC [FUNPOW_SUC, ADD_SYM,
                   (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_THM)] THEN
               `step (upload arm iB1 (FST (FST s))) (FUNPOW (step instB) m s) = step instB (FUNPOW (step instB) m s)` by (
                   Q.UNABBREV_TAC `instB` THEN
                   `FST (FST s) <= FST (FST (FUNPOW (step (upload arm iB0 (FST (FST s)))) m s))` by METIS_TAC [CLOSED_THM] THEN
                   `?n. FST (FST (FUNPOW (step (upload arm iB0 (FST (FST s)))) m s)) = FST (FST s) + n` by RW_TAC arith_ss [LESS_EQUAL_ADD] THEN
                   `n < LENGTH arm` by METIS_TAC [LESS_MONO_ADD_EQ, CLOSED_THM, ADD_SYM] THEN
                   `?s' pcS'. FUNPOW (step (upload arm iB0 (FST (FST s)))) m s = (s',pcS')` by METIS_TAC [ABS_PAIR_THM] THEN
                   FULL_SIMP_TAC std_ss [] THEN
                   RW_TAC std_ss [step_def] THEN
                   METIS_TAC [UPLOAD_LEM]
               ) THEN

               Cases_on `v` THENL [
                   RW_TAC std_ss [Once RUNTO_EXPAND_ONCE, FUNPOW] THENL [
                       METIS_TAC [],
                       RW_TAC std_ss [Once RUNTO_EXPAND_ONCE, FUNPOW] THEN
                       Q.ABBREV_TAC `s' = step instB (FUNPOW (step instB) m s)` THEN
                       `(FST (FST s') = FST (FST s) + LENGTH arm)` by METIS_TAC [Q.SPECL [`s'`, `\s1. FST (FST s1) =
                           FST (FST s) + LENGTH arm`] (INST_TYPE [alpha |-> Type `:STATEPCS`] SHORTEST_LEM)]
                   ],

                   Q.PAT_ASSUM `!s.p` (ASSUME_TAC o SIMP_RULE std_ss [FUNPOW_SUC] o Q.SPECL [`s`,`arm`,`instB`,`SUC m`]) THEN
                   `SUC m < shortest (\s'. FST (FST s') = FST (FST s) + LENGTH arm) (step instB) s` by RW_TAC arith_ss [] THEN
                   RW_TAC std_ss [Once RUNTO_EXPAND_ONCE] THEN
                   METIS_TAC []
               ]
        ]
   ]
  );

val WELL_FORMED_INSTB = Q.store_thm (
   "WELL_FORMED_INSTB",
   `!arm iB0 iB1 (s:STATEPCS).
           well_formed arm ==>
               (runTo (upload arm iB0 (FST (FST s))) (FST (FST s) + LENGTH arm) s =
                runTo (upload arm iB1 (FST (FST s))) (FST (FST s) + LENGTH arm) s)`,
   RW_TAC std_ss [well_formed] THEN
   IMP_RES_TAC (SIMP_RULE arith_ss [GSYM RIGHT_EXISTS_IMP_THM]
        (Q.SPECL [`arm`,`iB0`,`iB1`, `s:STATEPCS`, `FUNPOW (step instB) 0 s`] WELL_FORMED_INSTB_LEM)) THEN
   NTAC 11 (POP_ASSUM (K ALL_TAC)) THEN FULL_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o Q.SPECL [`s`,`iB0`,`0`]) THEN
   FULL_SIMP_TAC arith_ss [FUNPOW]
  );


val _ = export_theory();

