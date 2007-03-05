(*
  app load ["bossLib", "numLib", "pairTheory",
            "schneiderUtils", "Temporal_LogicTheory"];
*)

open HolKernel Parse boolLib Rsyntax
     numLib numTheory prim_recTheory arithmeticTheory pairTheory
     schneiderUtils Temporal_LogicTheory;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;


val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;
val ZERO_LEMMA = ARITH_PROVE(--`~(x<x) /\ (0<SUC x) /\ ~(SUC x=0)`--);


val _ = new_theory "Past_Temporal_Logic";


(*---------------------------------------------------------------------------
            Definitions.
 ---------------------------------------------------------------------------*)

val InitPoint = new_definition("InitPoint", --`InitPoint = \t. (t=0)`--);

val PSNEXT = new_definition("PSNEXT", --`PSNEXT a t0 = (0<t0) /\ a(PRE t0)`--);

val PNEXT = new_definition("PNEXT", --`PNEXT a t0 = (t0=0) \/ a(PRE t0)`--);

val PALWAYS = new_definition("PALWAYS", --`PALWAYS a t0 = !t:num. t<=t0 ==> a t`--);

val PEVENTUAL = new_definition("PEVENTUAL", --`PEVENTUAL a t0 = ?t:num. t<=t0 /\ a t`--);

val PSWHEN = new_infixr_definition("PSWHEN",
	--`$PSWHEN a b t0 =
		?delta.
			delta<=t0 /\
			a delta /\ b delta /\
			!t. delta<t /\ t<=t0 ==> ~b t`--,200);

val PSUNTIL = new_infixr_definition("PSUNTIL",
	--`$PSUNTIL a b t0 =
		?delta.
			delta<=t0 /\
			b delta /\
			!t. delta<t /\ t<=t0 ==> a t /\ ~b t`--,200);

val PSBEFORE = new_infixr_definition("PSBEFORE",
	--`$PSBEFORE a b t0 =
		?delta.
			delta<=t0 /\
			a delta /\
			!t. delta<=t /\ t<=t0 ==> ~b t`--,200);

val PWHEN = new_infixr_definition("PWHEN",
	--`$PWHEN a b t0 =
		(!t. t<=t0 ==> ~b t) \/
		?delta.
			delta<=t0 /\
			a delta /\ b delta /\
			!t. delta<t /\ t<=t0 ==> ~b t`--,200);

val PUNTIL = new_infixr_definition("PUNTIL",
	--`$PUNTIL a b t0 =
		(!t. t<=t0 ==> a t) \/
		?delta.
			delta<=t0 /\
			b delta /\
			!t. delta<t /\ t<=t0 ==> a t /\ ~b t `--,200);

val PBEFORE = new_infixr_definition("PBEFORE",
	--`$PBEFORE a b t0 =
		(!t. t<=t0 ==> ~b t) \/
		?delta.
			delta<=t0 /\
			a delta /\
			!t. delta<=t /\ t<=t0 ==> ~b t`--,200);


(*---------------------------------------------------------------------------
       Initialization
 ---------------------------------------------------------------------------*)

val PALWAYS_INIT = TAC_PROOF(
	([],--` (PALWAYS a) 0 = a 0 `--),
	REWRITE_TAC[PALWAYS]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x<=0) = (x=0)`--))]
	THEN REWRITE_TAC[ADD_CLAUSES]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[],
	    ASM_REWRITE_TAC[]
	    ]);


val PEVENTUAL_INIT = TAC_PROOF(
	([],--` (PEVENTUAL a) 0 = a 0 `--),
	REWRITE_TAC[PEVENTUAL]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x<=0) = (x=0)`--))]
	THEN REWRITE_TAC[ADD_CLAUSES]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[]
	    ]);


val PSUNTIL_INIT = TAC_PROOF(
	([],--` (a PSUNTIL b) 0 = b 0 `--),
	REWRITE_TAC[PSUNTIL] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((0<t)/\(t<=0))`--))]
	    ]);


val PUNTIL_INIT = TAC_PROOF(
	([],--` (a PUNTIL b) 0 = a 0 \/ b 0 `--),
	REWRITE_TAC[PUNTIL] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ1_TAC THEN POP_ASSUM MATCH_MP_TAC
	    THEN REWRITE_TAC[LESS_EQ_REFL],
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    DISJ1_TAC THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x<=0) = (x=0)`--))]
	    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[],
	    DISJ2_TAC THEN EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((0<t)/\(t<=0))`--))]
	    ]);


val PSWHEN_INIT = TAC_PROOF(
	([],--` (a PSWHEN b) 0 = a 0 /\ b 0 `--),
	REWRITE_TAC[PSWHEN] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((0<t)/\(t<=0))`--))]
	    ]);


val PWHEN_INIT = TAC_PROOF(
	([],--` (a PWHEN b) 0 = a 0 \/ ~b 0 `--),
	ONCE_REWRITE_TAC[TAC_PROOF(([],--`a\/~b = (a/\b)\/~b`--),PROP_TAC)]
	THEN REWRITE_TAC[PWHEN] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ2_TAC THEN POP_ASSUM MATCH_MP_TAC
	    THEN REWRITE_TAC[LESS_EQ_REFL],
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    DISJ2_TAC THEN EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((0<t)/\(t<=0))`--))],
	    DISJ1_TAC THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x<=0) = (x=0)`--))]
	    THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    ]);


val PSBEFORE_INIT = TAC_PROOF(
	([],--` (a PSBEFORE b) 0 = a 0 /\ ~b 0`--),
	REWRITE_TAC[PSBEFORE] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=0) ==> (0=x)`--)))
	    THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[],
	    RES_TAC THEN UNDISCH_NO_TAC 2 THEN REWRITE_TAC[]
	    THEN POP_NO_ASSUM 1 MATCH_MP_TAC
	    THEN REWRITE_TAC[LESS_EQ_REFL],
	    EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`((0<=t)/\(t<=0)) = (t=0)`--))]
	    THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    ]);


val PBEFORE_INIT = TAC_PROOF(
	([],--` (a PBEFORE b) 0 = ~b 0`--),
	REWRITE_TAC[PBEFORE] THEN EQ_TAC THEN STRIP_TAC
	THENL[
	    POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
	    POP_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
	    DISJ1_TAC THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x<=0) = (x=0)`--))]
	    THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    ]);



val INITIALISATION = TAC_PROOF(
	([],--`
	( (PNEXT a) 0 = T ) /\
	( (PSNEXT a) 0 = F ) /\
	( (PALWAYS a) 0 = a 0 ) /\
	( (PEVENTUAL a) 0 = a 0 ) /\
	( (a PSUNTIL b) 0 = b 0 ) /\
	( (a PSWHEN b) 0 = a 0 /\ b 0 ) /\
	( (a PSBEFORE b) 0 = a 0 /\ ~b 0 ) /\
	( (a PUNTIL b) 0 = a 0 \/ b 0 ) /\
	( (a PWHEN b) 0 = a 0 \/ ~b 0 ) /\
	( (a PBEFORE b) 0 = ~b 0 )
	`--),
	REWRITE_TAC[PALWAYS_INIT,PEVENTUAL_INIT,
		    PSUNTIL_INIT,PSWHEN_INIT,PSBEFORE_INIT,
		    PUNTIL_INIT,PWHEN_INIT,PBEFORE_INIT,
		    PNEXT,PSNEXT,LESS_REFL]
	);



(*---------------------------------------------------------------------------
       Recursion theorems
 ---------------------------------------------------------------------------*)

val PEVENTUAL_REC = TAC_PROOF(
	([],--` (PEVENTUAL a) = \t. a t \/ PSNEXT (PEVENTUAL a) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PSNEXT,PRE,PEVENTUAL_INIT]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`0<SUC t`--))]
	THEN REWRITE_TAC[PEVENTUAL]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_NO_ASSUM 1 (fn x => DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x<SUC t ==> x<=t`--)))
		THEN DISJ2_TAC THEN EXISTS_TAC(--`t':num`--)
		THEN ASM_REWRITE_TAC[],
		POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]
		],
	    EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
	    EXISTS_TAC(--`t':num`--) THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_NO_TAC 1 THEN CONV_TAC ARITH_CONV
	    ]);


val PSUNTIL_REC = TAC_PROOF(
	([],--` (a PSUNTIL b) = \t. b t \/ a t /\ PSNEXT (a PSUNTIL b) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PSNEXT,PRE,PSUNTIL_INIT]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`0<SUC t`--))]
	THEN REWRITE_TAC[PSUNTIL]
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`a\/b = a\/(~a/\b)`--),PROP_TAC)]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_NO_ASSUM 2 (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		COPY_ASM_NO 1 THEN LEFT_FORALL_TAC (--`SUC t`--)
		THEN DISCH_TAC THEN UNDISCH_NO_TAC 1
		THEN REWRITE_TAC[LESS_EQ_REFL] THEN ASM_REWRITE_TAC[]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN EXISTS_TAC (--`delta:num`--)
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
		THEN ASM_REWRITE_TAC[]
		THEN REPEAT STRIP_TAC THEN RES_TAC
		THENL[
		    POP_NO_ASSUM 3 MATCH_MP_TAC THEN UNDISCH_NO_TAC 3
		    THEN CONV_TAC ARITH_CONV,
		    UNDISCH_NO_TAC 4 THEN REWRITE_TAC[]
		    THEN POP_NO_ASSUM 1 MATCH_MP_TAC THEN UNDISCH_NO_TAC 3
		    THEN CONV_TAC ARITH_CONV],
		DISJ1_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
		THEN ASM_REWRITE_TAC[]],
	    EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t<x /\ x<=SUC t)`--))],
	    EXISTS_TAC (--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<=t ==> delta<=SUC t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN STRIP_TAC
	    THEN POP_ASSUM (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<SUC t ==> t'<=t`--)))
		THEN RES_TAC THEN ASM_REWRITE_TAC[],
		ASM_REWRITE_TAC[]
		]
	    ]);


val PSWHEN_REC = TAC_PROOF(
	([],--` (a PSWHEN b) = \t. a t /\ b t \/ ~b t /\ PSNEXT (a PSWHEN b) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PSNEXT,PRE,PSWHEN_INIT]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`0<SUC t`--))]
	THEN REWRITE_TAC[PSWHEN]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_NO_ASSUM 3 (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[ALL_TAC, POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]
	    THEN DISJ2_TAC THEN CONJ_TAC
	    THENL[POP_NO_ASSUM 1 MATCH_MP_TAC THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
		  ALL_TAC]
	    THEN EXISTS_TAC (--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<=t ==> t'<=SUC t`--)))
	    THEN RES_TAC,
	    EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t<x /\ x<=SUC t)`--))],
	    EXISTS_TAC (--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<=t ==> delta<=SUC t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN STRIP_TAC
	    THEN POP_ASSUM (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<SUC t ==> t'<=t`--)))
		THEN RES_TAC THEN ASM_REWRITE_TAC[],
		ASM_REWRITE_TAC[]]
	    ]);


val PSBEFORE_REC = TAC_PROOF(
	([],--` (a PSBEFORE b) = \t. ~b t /\ (a t \/ PSNEXT (a PSBEFORE b) t)`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PSNEXT,PRE,PSBEFORE_INIT]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	THEN REWRITE_TAC[NOT_LESS_0,EQT_ELIM(ARITH_CONV(--`0<SUC t`--))]
	THENL[PROP_TAC,ALL_TAC]
	THEN REWRITE_TAC[PSBEFORE]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    UNDISCH_HD_TAC THEN REWRITE_TAC[]
	    THEN POP_ASSUM MATCH_MP_TAC
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
	    POP_NO_ASSUM 2 (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[ALL_TAC, POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]
	    THEN DISJ2_TAC THEN EXISTS_TAC (--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<=t ==> t'<=SUC t`--)))
	    THEN RES_TAC,
	    EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(SUC t<=x /\ x<=SUC t) = (x = SUC t)`--))]
	    THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC (--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<=t ==> delta<=SUC t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN STRIP_TAC
	    THEN POP_ASSUM (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<SUC t ==> t'<=t`--)))
		THEN RES_TAC THEN ASM_REWRITE_TAC[],
		ASM_REWRITE_TAC[]]
	    ]);


val PALWAYS_REC = TAC_PROOF(
	([],--` (PALWAYS a) = \t. a t /\ PNEXT (PALWAYS a) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PNEXT,PRE,PALWAYS_INIT]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
	THEN REWRITE_TAC[PALWAYS]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
	    POP_NO_ASSUM 1 MATCH_MP_TAC
	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
	    POP_NO_ASSUM 0 (fn x => DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x<SUC t ==> x<=t`--)))
		THEN POP_NO_ASSUM 2 MATCH_MP_TAC
		THEN ASM_REWRITE_TAC[],
		POP_ASSUM (SUBST1_TAC) THEN ASM_REWRITE_TAC[]
		]
	    ]);

val PUNTIL_REC = TAC_PROOF(
	([],--` (a PUNTIL b) = \t. b t \/ a t /\ PNEXT (a PUNTIL b) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PNEXT,PRE,PUNTIL_INIT]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
	THENL[PROP_TAC,ALL_TAC]
	THEN REWRITE_TAC[PUNTIL]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* -------------------- 1st goal ------------------	*)
	    DISJ2_TAC THEN COPY_ASM_NO 0 THEN LEFT_FORALL_TAC (--`SUC t`--)
	    THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_EQ_REFL]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC
	    THEN GEN_TAC THEN DISCH_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x<=t ==> x<=SUC t`--)))
	    THEN RES_TAC,
	    (* -------------------- 2nd goal ------------------	*)
	    POP_NO_ASSUM 2 (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[ALL_TAC,POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]
	    THEN COPY_ASM_NO 1 THEN LEFT_FORALL_TAC (--`SUC t`--)
	    THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_EQ_REFL]
	    THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
	    THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC
	    THEN POP_NO_ASSUM 3 MATCH_MP_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
	    (* -------------------- 3rd goal ------------------	*)
	    DISJ2_TAC THEN EXISTS_TAC (--`SUC t`--)
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t<x /\x<=SUC t)`--))],
	    (* -------------------- 4th goal ------------------	*)
	    DISJ1_TAC THEN GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ]
	    THEN STRIP_TAC
	    THENL[
		POP_NO_ASSUM 1 MATCH_MP_TAC
	    	THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
		ASM_REWRITE_TAC[]],
	    (* -------------------- 5th goal ------------------	*)
	    DISJ2_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`b(SUC t):bool`--)BOOL_CASES_AX)
	    THENL[
		EXISTS_TAC (--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t<x /\x<=SUC t)`--))],
	    	EXISTS_TAC (--`delta:num`--)
	    	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<=t ==> delta<=SUC t`--)))
	    	THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ]
	    	THEN STRIP_TAC
	    	THENL[
		    POP_NO_ASSUM 4 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
	    	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
		    ASM_REWRITE_TAC[]]
		]
	    ]);





val PWHEN_REC = TAC_PROOF(
	([],--` (a PWHEN b) = \t. a t /\ b t \/ ~b t /\ PNEXT (a PWHEN b) t`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PNEXT,PRE,PWHEN_INIT]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
	THENL[PROP_TAC,ALL_TAC]
	THEN REWRITE_TAC[PWHEN]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ2_TAC THEN COPY_ASM_NO 0 THEN LEFT_FORALL_TAC (--`SUC t`--)
	    THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_EQ_REFL]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN DISJ1_TAC THEN GEN_TAC THEN DISCH_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<=t ==> t'<=SUC t`--)))
	    THEN RES_TAC,
	    POP_NO_ASSUM 3 (fn x => DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[ALL_TAC, POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]
	    THEN COPY_ASM_NO 1 THEN LEFT_FORALL_TAC (--`SUC t`--)
	    THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_EQ_REFL]
	    THEN ASM_REWRITE_TAC[]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
	    THEN POP_ASSUM REWRITE1_TAC
	    THEN GEN_TAC THEN DISCH_TAC
	    THEN POP_NO_ASSUM 2 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
	    DISJ2_TAC THEN EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t<x /\ x<=SUC t)`--))],
	    DISJ1_TAC THEN GEN_TAC THEN DISCH_TAC
	    THEN POP_ASSUM (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<SUC t ==> t'<=t`--)))
		THEN RES_TAC THEN ASM_REWRITE_TAC[],
		ASM_REWRITE_TAC[]],
	    DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<= t ==> delta<=SUC t`--)))
	    THEN POP_ASSUM REWRITE1_TAC
	    THEN REWRITE_TAC[LESS_OR_EQ] THEN GEN_TAC THEN STRIP_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x<SUC t ==> x<=t`--)))
	    THEN RES_TAC
	    ]);



val PBEFORE_REC = TAC_PROOF(
	([],--` (a PBEFORE b)	= \t. ~b t /\ (a t \/ PNEXT (a PBEFORE b) t)`--),
	CONV_TAC (X_FUN_EQ_CONV(--`t:num`--)) THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[PNEXT,PRE,PBEFORE_INIT]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
	THEN REWRITE_TAC[PBEFORE] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* -------------------- 1st goal ------------------	*)
	    UNDISCH_HD_TAC THEN REWRITE_TAC[]
	    THEN POP_ASSUM MATCH_MP_TAC
	    THEN REWRITE_TAC[LESS_EQ_REFL],
	    (* -------------------- 2nd goal ------------------	*)
	    DISJ2_TAC THEN DISJ1_TAC
	    THEN GEN_TAC THEN DISCH_TAC
	    THEN POP_NO_ASSUM 1 MATCH_MP_TAC
	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
	    (* -------------------- 3rd goal ------------------	*)
	    UNDISCH_HD_TAC THEN REWRITE_TAC[]
	    THEN POP_ASSUM MATCH_MP_TAC
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
	    (* -------------------- 4th goal ------------------	*)
	    POP_NO_ASSUM 2 (fn x=> DISJ_CASES_TAC(REWRITE_RULE[LESS_OR_EQ]x))
	    THENL[ALL_TAC,POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]
	    THEN DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<SUC t ==> delta<=t`--)))
	    THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC
	    THEN POP_NO_ASSUM 3 MATCH_MP_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
	    (* -------------------- 5th goal ------------------	*)
	    DISJ2_TAC THEN EXISTS_TAC (--`SUC t`--)
	    THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV
			(--`(SUC t<=x /\x<=SUC t)=(x=SUC t)`--))]
	    THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
	    (* -------------------- 6th goal ------------------	*)
	    DISJ1_TAC THEN REWRITE_TAC[LESS_OR_EQ]
	    THEN GEN_TAC THEN STRIP_TAC
	    THENL[
		POP_NO_ASSUM 1 MATCH_MP_TAC
	    	THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
		ASM_REWRITE_TAC[]],
	    (* -------------------- 7th goal ------------------	*)
	    DISJ2_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`a(SUC t):bool`--)BOOL_CASES_AX)
	    THENL[
		EXISTS_TAC (--`SUC t`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV
			(--`(SUC t<=x /\x<=SUC t)=(x=SUC t)`--))]
	    	THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
	    	EXISTS_TAC (--`delta:num`--)
	    	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`delta<=t ==> delta<=SUC t`--)))
	    	THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ]
	    	THEN STRIP_TAC
	    	THENL[
		    POP_NO_ASSUM 4 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
	    	    THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		    THEN CONV_TAC ARITH_CONV,
		    ASM_REWRITE_TAC[],
		    POP_NO_ASSUM 4 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
	    	    THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		    THEN CONV_TAC ARITH_CONV,
		    ASM_REWRITE_TAC[]]
		]
	    ]);






val RECURSION = TAC_PROOF(
	([],--`
	( ALWAYS a       = \t. (a t /\ NEXT (ALWAYS a) t) ) /\
	( EVENTUAL a     = \t. (a t \/ NEXT (EVENTUAL a) t) ) /\
	( (a SUNTIL b)   = \t. ~(b t) ==> a t /\ NEXT (a SUNTIL b) t ) /\
	( (a SWHEN b)    = \t. (if (b t) then (a t) else (NEXT (a SWHEN b) t)) ) /\
	( (a SBEFORE b)  = \t. ~b t /\ (a t \/ NEXT (a SBEFORE b) t) ) /\
	( (a UNTIL b)    = \t. (~b t ==> a t /\ NEXT (a UNTIL b) t) ) /\
	( (a WHEN b)     = \t. (if (b t) then (a t) else (NEXT (a WHEN b) t)) ) /\
	( (a BEFORE b)   = \t. ~b t /\ (a t \/ NEXT (a BEFORE b) t) ) /\
	( (PALWAYS a)    = \t. a t /\ PNEXT (PALWAYS a) t ) /\
	( (PEVENTUAL a)  = \t. a t \/ PSNEXT (PEVENTUAL a) t ) /\
	( (a PSUNTIL b)  = \t. b t \/ a t /\ PSNEXT (a PSUNTIL b) t ) /\
	( (a PSWHEN b)   = \t. a t /\ b t \/ ~b t /\ PSNEXT (a PSWHEN b) t ) /\
	( (a PSBEFORE b) = \t. ~b t /\ (a t \/ PSNEXT (a PSBEFORE b) t) ) /\
	( (a PUNTIL b)   = \t. b t \/ a t /\ PNEXT (a PUNTIL b) t ) /\
	( (a PWHEN b)    = \t. a t /\ b t \/ ~b t /\ PNEXT (a PWHEN b) t ) /\
	( (a PBEFORE b)  = \t. ~b t /\ (a t \/ PNEXT (a PBEFORE b) t) )
	`--),
	REWRITE_TAC (map SYM
			[PALWAYS_REC,PEVENTUAL_REC,
		    	 PSUNTIL_REC,PSWHEN_REC,PSBEFORE_REC,
		   	 PUNTIL_REC,PWHEN_REC,PBEFORE_REC])
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REWRITE_TAC (map SYM
			[ALWAYS_REC,EVENTUAL_REC,
		   	 SUNTIL_REC,SWHEN_REC,SBEFORE_REC,
		   	 UNTIL_REC,WHEN_REC,BEFORE_REC])
	);



(*---------------------------------------------------------------------------
        Fixpoints
 ---------------------------------------------------------------------------*)

fun FIXPOINT_CHARACTERIZATION_TAC init_thm rec_thm (asm,g)=
	(EQ_TAC THEN STRIP_TAC
	THENL[
	    CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN INDUCT_TAC
	    THENL[
		POP_ASSUM SUBST1_TAC THEN BETA_TAC
		THEN REWRITE_TAC[init_thm,PSNEXT,PNEXT,ZERO_LEMMA],
		POP_NO_ASSUM 1 SUBST1_TAC
		THEN ONCE_REWRITE_TAC[rec_thm]
		THEN BETA_TAC THEN ASM_REWRITE_TAC[PNEXT,PSNEXT,PRE]
		],
    	    POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[SYM rec_thm]
	    ])
	(asm,g)
	;



val PSUNTIL_FIX = TAC_PROOF(
	([],--` (y = \t. b t \/ a t /\ PSNEXT y t) = (y = (a PSUNTIL b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PSUNTIL_INIT PSUNTIL_REC);


val PSWHEN_FIX = TAC_PROOF(
	([],--` (y = \t. a t /\ b t \/ ~b t /\ PSNEXT y t) = (y = (a PSWHEN b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PSWHEN_INIT PSWHEN_REC);

val PSBEFORE_FIX = TAC_PROOF(
	([],--` (y = \t. ~b t /\ (a t \/ PSNEXT y t)) = (y = (a PSBEFORE b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PSBEFORE_INIT PSBEFORE_REC THEN PROP_TAC);


val PUNTIL_FIX = TAC_PROOF(
	([],--` (y = \t. b t \/ a t /\ PNEXT y t) = (y = (a PUNTIL b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PUNTIL_INIT PUNTIL_REC THEN PROP_TAC);


val PWHEN_FIX = TAC_PROOF(
	([],--` (y = \t. a t /\ b t \/ ~b t /\ PNEXT y t) = (y = (a PWHEN b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PWHEN_INIT PWHEN_REC THEN PROP_TAC);


val PBEFORE_FIX = TAC_PROOF(
	([],--` (y = \t. ~b t /\ (a t \/ PNEXT y t)) = (y = (a PBEFORE b))`--),
	FIXPOINT_CHARACTERIZATION_TAC PBEFORE_INIT PBEFORE_REC THEN PROP_TAC);


val PALWAYS_FIX = TAC_PROOF(
	([],--` (y = \t. a t /\ PNEXT y t) = (y = PALWAYS a)`--),
	FIXPOINT_CHARACTERIZATION_TAC PALWAYS_INIT PALWAYS_REC);

val PEVENTUAL_FIX = TAC_PROOF(
	([],--` (y = \t. a t \/ PSNEXT y t) = (y = PEVENTUAL a)`--),
	FIXPOINT_CHARACTERIZATION_TAC PEVENTUAL_INIT PEVENTUAL_REC);





val FIXPOINTS = TAC_PROOF(
	([],--`
	    ( (y = \t. a t /\ NEXT y t) = (y = ALWAYS a)   \/ (y = \t. F) ) /\
	    ( (y = \t. a t \/ NEXT y t) = (y = EVENTUAL a) \/ (y = \t. T) ) /\
	    ( (y = \t. ~b t ==> a t /\ NEXT y t) = (y = a UNTIL b) \/ (y = a SUNTIL b) ) /\
	    ( (y = \t. if b t then a t else NEXT y t) = ((y = a WHEN b) \/ (y = a SWHEN b)) ) /\
	    ( (y = \t. ~b t /\ (a t \/ NEXT y t)) = (y = a BEFORE b) \/ (y = a SBEFORE b) ) /\
	    ( (y = \t. a t /\ PNEXT y t) = (y = PALWAYS a) ) /\
	    ( (y = \t. a t \/ PSNEXT y t) = (y = PEVENTUAL a) ) /\
	    ( (y = \t. b t \/ a t /\ PSNEXT y t) = (y = (a PSUNTIL b)) ) /\
	    ( (y = \t. a t /\ b t \/ ~b t /\ PSNEXT y t) = (y = (a PSWHEN b)) ) /\
	    ( (y = \t. ~b t /\ (a t \/ PSNEXT y t)) = (y = (a PSBEFORE b)) ) /\
	    ( (y = \t. b t \/ a t /\ PNEXT y t) = (y = (a PUNTIL b)) ) /\
	    ( (y = \t. a t /\ b t \/ ~b t /\ PNEXT y t) = (y = (a PWHEN b)) ) /\
	    ( (y = \t. ~b t /\ (a t \/ PNEXT y t)) = (y = (a PBEFORE b)) )
	`--),
	REWRITE_TAC (map SYM
		[
		 ALWAYS_FIX,EVENTUAL_FIX,UNTIL_FIX,WHEN_FIX,SPEC_ALL BEFORE_FIX,
		 PALWAYS_FIX,PEVENTUAL_FIX,
		 PSUNTIL_FIX,PUNTIL_FIX,
		 PSWHEN_FIX,PWHEN_FIX,
		 PSBEFORE_FIX,PBEFORE_FIX
		])
	THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN REWRITE_TAC[ADD1]);



(* ********************************************************************	*)
(* As past temporal operators can be defined by primitive recursion,	*)
(* most of the proofs can be done by a simple induction tactic that	*)
(* solves the resulting subgoals by the initialisation and recursion	*)
(* theorems of the temporal operators and a tactic for propositional	*)
(* logic theorem proving.						*)
(* ********************************************************************	*)

val PAST_TEMP_TAC  =
	INDUCT_TAC THENL[ALL_TAC,UNDISCH_HD_TAC]
	THEN BETA_TAC
	THEN REWRITE_TAC[INITIALISATION]
	THEN BETA_TAC
	THEN REWRITE_TAC (map (fn x => BETA_RULE(AP_THM x (--`SUC t`--)))
			      (CONJUNCTS RECURSION))
	THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,ZERO_LEMMA,PRE]
	THEN (PROP_TAC ORELSE ALL_TAC);



val PAST_TEMP_TAC2  =
	SPEC_TAC((--`t:num`--),(--`t:num`--))
	THEN INDUCT_TAC THENL[ALL_TAC,UNDISCH_HD_TAC]
	THEN BETA_TAC
	THEN REWRITE_TAC[INITIALISATION]
	THEN BETA_TAC
	THEN REWRITE_TAC (map (fn x => BETA_RULE(AP_THM x (--`SUC t`--)))
			      (CONJUNCTS RECURSION))
	THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,ZERO_LEMMA,PRE]
	THEN (PROP_TAC ORELSE ALL_TAC);


(*---------------------------------------------------------------------------
      Expressiveness
 ---------------------------------------------------------------------------*)

val PSUNTIL_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. ~((\t.T) PSUNTIL (\t.~a t)) t ) /\
	    ( (PEVENTUAL a)  = \t. ((\t.T) PSUNTIL a) t ) /\
	    ( (a PUNTIL b)   = \t. ~((\t. ~b t) PSUNTIL (\t. ~a t /\ ~b t)) t ) /\
	    ( (a PWHEN b)    = \t. ~((\t. ~a t \/ ~b t) PSUNTIL (\t. ~a t /\ b t)) t ) /\
	    ( (a PBEFORE b)  = \t. ~((\t. ~a t) PSUNTIL b) t ) /\
	    ( (a PSWHEN b)   = \t. ((\t. ~b t) PSUNTIL (\t. a t /\ b t)) t ) /\
	    ( (a PSBEFORE b) = \t. ((\t. ~b t) PSUNTIL (\t. a t /\ ~b t)) t )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );


val PUNTIL_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. (a PUNTIL (\t.F)) t ) /\
	    ( (PEVENTUAL a)  = \t. ~((\t.~ a t) PUNTIL (\t.F)) t ) /\
	    ( (a PSUNTIL b)  = \t. ~((\t. ~b t) PUNTIL (\t. ~a t /\ ~b t)) t ) /\
	    ( (a PWHEN b)    = \t. ((\t. ~b t) PUNTIL (\t. a t /\ b t)) t ) /\
	    ( (a PSWHEN b)   = \t. ~((\t. ~a t \/ ~b t) PUNTIL (\t. ~a t /\ b t)) t ) /\
	    ( (a PBEFORE b)  = \t. ((\t. ~b t) PUNTIL (\t. a t /\ ~b t)) t  ) /\
	    ( (a PSBEFORE b) = \t. ~ ((\t. ~a t) PUNTIL b) t  )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );



val PWHEN_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. ((\t.F) PWHEN (\t. ~a t)) t ) /\
	    ( (PEVENTUAL a)  = \t. ~((\t.F) PWHEN a) t ) /\
	    ( (a PSUNTIL b)  = \t. ~((\t. ~b t) PWHEN (\t. a t ==> b t)) t ) /\
	    ( (a PUNTIL b)   = \t. (b PWHEN (\t. a t ==> b t)) t  ) /\
	    ( (a PSWHEN b)   = \t. ~((\t. ~a t) PWHEN b) t ) /\
	    ( (a PBEFORE b)  = \t. ((\t. ~b t) PWHEN (\t. a t \/ b t)) t  ) /\
	    ( (a PSBEFORE b) = \t. ~(b PWHEN (\t. a t \/ b t)) t  )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );


val PSWHEN_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. ~((\t.T) PSWHEN (\t. ~a t)) t ) /\
	    ( (PEVENTUAL a)  = \t. ((\t.T) PSWHEN a) t ) /\
	    ( (a PSUNTIL b)  = \t. (b PSWHEN (\t. a t ==> b t)) t ) /\
	    ( (a PUNTIL b)   = \t. ~((\t. ~b t) PSWHEN (\t. a t ==> b t)) t ) /\
	    ( (a PWHEN b)    = \t. ~((\t. ~a t) PSWHEN b) t ) /\
	    ( (a PBEFORE b)  = \t. ~(b PSWHEN (\t. a t \/ b t)) t  ) /\
	    ( (a PSBEFORE b) = \t. ((\t. ~b t) PSWHEN (\t. a t \/ b t)) t )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );



val PBEFORE_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. ((\t.F) PBEFORE (\t. ~a t)) t ) /\
	    ( (PEVENTUAL a)  = \t. ~((\t. F) PBEFORE a) t ) /\
	    ( (a PSUNTIL b)  = \t. ~((\t. ~a t) PBEFORE b) t ) /\
	    ( (a PUNTIL b)   = \t. (b PBEFORE (\t. ~a t /\ ~b t)) t ) /\
	    ( (a PSWHEN b)   = \t. ~(b PBEFORE (\t. a t /\ b t)) t  ) /\
	    ( (a PWHEN b)    = \t. ((\t. a t /\ b t) PBEFORE (\t. ~a t /\ b t)) t  ) /\
	    ( (a PSBEFORE b) = \t. ~(b PBEFORE (\t. a t /\ ~b t)) t  )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );




val PSBEFORE_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (PALWAYS a)    = \t. ~((\t. ~a t) PSBEFORE (\t. F)) t ) /\
	    ( (PEVENTUAL a)  = \t. (a PSBEFORE (\t. F)) t ) /\
	    ( (a PSUNTIL b)  = \t. (b PSBEFORE (\t. ~a t /\ ~b t)) t ) /\
	    ( (a PUNTIL b)   = \t. ~((\t. ~a t) PSBEFORE b) t ) /\
	    ( (a PSWHEN b)   = \t. (b PSBEFORE (\t. ~a t /\ b t)) t  ) /\
	    ( (a PWHEN b)    = \t. ~(b PSBEFORE (\t. a t /\ b t)) t  ) /\
	    ( (a PBEFORE b)  = \t. ~(b PSBEFORE (\t. a t /\ ~b t)) t  )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );







val SUNTIL_AS_SBEFORE1 = TAC_PROOF(
	([], --`(a SUNTIL b) = b SBEFORE (\t. ~a t /\ ~b t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--))
	THEN REWRITE_TAC[SBEFORE_SIGNAL,SUNTIL_SIGNAL] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[LESS_OR_EQ] THEN GEN_TAC THEN STRIP_TAC
	    THEN RES_TAC THEN ASM_REWRITE_TAC[],
	    ALL_TAC]
	THEN DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
	THEN LEFT_EXISTS_TAC THEN EXISTS_TAC(--`d:num`--)
	THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC
	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THEN MY_MP_TAC (--`d<=delta`--)
	THENL[
	    SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`d<=delta = ~(delta<d)`--)))
	    THEN DISCH_TAC THEN RES_TAC,
	    DISCH_TAC]
	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<d /\ d<=delta ==> t<=delta`--)))
	THEN RES_TAC THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]);




val BEFORE_AS_UNTIL1 = TAC_PROOF(
	([], --`(a BEFORE b) = (\t. ~b t) UNTIL (\t. a t /\ ~b t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--)) THEN GEN_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NOT_BEFORE,NOT_UNTIL] THEN BETA_TAC
	THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[SUNTIL_AS_SBEFORE1] THEN BETA_TAC
	THEN REWRITE_TAC[]);



val SBEFORE_AS_SUNTIL1 = TAC_PROOF(
	([], --`(a SBEFORE b) = (\t. ~b t) SUNTIL (\t. a t /\ ~b t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--))
	THEN REWRITE_TAC[SBEFORE_SIGNAL,SUNTIL_SIGNAL] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(~b/\~(a/\~b)) = (~a/\~b)`--),PROP_TAC)]
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    ALL_TAC,
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[LESS_OR_EQ] THEN GEN_TAC THEN STRIP_TAC
	    THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    ]
	THEN DISJ_CASES_TAC(SPEC(--`a:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	THEN RES_TAC
	THEN LEFT_EXISTS_TAC THEN EXISTS_TAC(--`d:num`--)
	THEN ASM_REWRITE_TAC[]
	THEN MY_MP_TAC (--`d<=delta`--)
	THENL[
	    SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`d<=delta = ~(delta<d)`--)))
	    THEN DISCH_TAC THEN RES_TAC,
	    DISCH_TAC]
	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<d /\ d<=delta ==> t<=delta`--)))
	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THEN RES_TAC);




val UNTIL_AS_BEFORE1 = TAC_PROOF(
	([], --`(a UNTIL b) = b BEFORE (\t. ~a t /\ ~b t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--)) THEN GEN_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NOT_BEFORE,NOT_UNTIL] THEN BETA_TAC
	THEN REWRITE_TAC[SBEFORE_AS_SUNTIL1] THEN BETA_TAC
	THEN REWRITE_TAC[]);



val SUNTIL_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. ~((\t.T) SUNTIL (\t.~a t)) t ) /\
	    ( (EVENTUAL a)  = \t. ((\t.T) SUNTIL a) t ) /\
	    ( (a UNTIL b)   = \t. ~((\t. ~b t) SUNTIL (\t. ~a t /\ ~b t)) t ) /\
	    ( (a WHEN b)    = \t. ~((\t. ~a t \/ ~b t) SUNTIL (\t. ~a t /\ b t)) t ) /\
	    ( (a BEFORE b)  = \t. ~((\t. ~a t) SUNTIL b) t ) /\
	    ( (a SWHEN b)   = \t. ((\t. ~b t) SUNTIL (\t. a t /\ b t)) t ) /\
	    ( (a SBEFORE b) = \t. ((\t. ~b t) SUNTIL (\t. a t /\ ~b t)) t )
	`--),
	    REWRITE_TAC[ALWAYS_AS_SUNTIL,EVENTUAL_AS_SUNTIL,
			BEFORE_AS_SUNTIL,SWHEN_AS_SUNTIL,SBEFORE_AS_SUNTIL1]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
	    THEN REWRITE_TAC[UNTIL_AS_BEFORE1, WHEN_AS_UNTIL, NOT_SUNTIL]
	    THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[DE_MORGAN_THM]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`b/\(~a\/~b)=~a/\b`--),PROP_TAC)]);




val SWHEN_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. ~((\t.T) SWHEN (\t. ~a t)) t ) /\
	    ( (EVENTUAL a)  = \t. ((\t.T) SWHEN a) t ) /\
	    ( (a SUNTIL b)  = \t. (b SWHEN (\t. a t ==> b t)) t ) /\
	    ( (a UNTIL b)   = \t. ~((\t. ~b t) SWHEN (\t. a t ==> b t)) t ) /\
	    ( (a WHEN b)    = \t. ~((\t. ~a t) SWHEN b) t ) /\
	    ( (a BEFORE b)  = \t. ~(b SWHEN (\t. a t \/ b t)) t  ) /\
	    ( (a SBEFORE b) = \t. ((\t. ~b t) SWHEN (\t. a t \/ b t)) t )
	`--),
	    REWRITE_TAC[ALWAYS_AS_SWHEN,EVENTUAL_AS_SWHEN,
			SBEFORE_AS_SWHEN,SUNTIL_AS_SWHEN,
			UNTIL_AS_WHEN,BEFORE_AS_WHEN,
			(SYM WHEN_AS_NOT_SWHEN)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
	    THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC
	    THEN REWRITE_TAC[NOT_SWHEN]);



val SBEFORE_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. ~((\t. ~a t) SBEFORE (\t. F)) t ) /\
	    ( (EVENTUAL a)  = \t. (a SBEFORE (\t. F)) t ) /\
	    ( (a SUNTIL b)  = \t. (b SBEFORE (\t. ~a t /\ ~b t)) t ) /\
	    ( (a UNTIL b)   = \t. ~((\t. ~a t) SBEFORE b) t ) /\
	    ( (a SWHEN b)   = \t. (b SBEFORE (\t. ~a t /\ b t)) t  ) /\
	    ( (a WHEN b)    = \t. ~(b SBEFORE (\t. a t /\ b t)) t  ) /\
	    ( (a BEFORE b)  = \t. ~(b SBEFORE (\t. a t /\ ~b t)) t  )
	`--),
	    REWRITE_TAC[ALWAYS_AS_SBEFORE,EVENTUAL_AS_SBEFORE,
			SWHEN_AS_SBEFORE,SUNTIL_AS_SBEFORE1,
			UNTIL_AS_WHEN,BEFORE_AS_WHEN,
			(SYM WHEN_AS_NOT_SWHEN)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	    THEN REWRITE_TAC[NOT_SBEFORE,WHEN_AS_UNTIL]
	    THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`b/\(a==>b)=b`--),PROP_TAC)]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~b/\(a\/b)=a/\~b`--),PROP_TAC)]
	    THEN ONCE_REWRITE_TAC[MORE_EVENT] THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~(a==>b)/\~b=a/\~b`--),PROP_TAC)]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~(a\/b)/\~(a/\~b)=~b/\~(a/\~b)`--),PROP_TAC)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	    THEN REWRITE_TAC[]);


val UNTIL_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. (a UNTIL (\t.F)) t ) /\
	    ( (EVENTUAL a)  = \t. ~((\t.~ a t) UNTIL (\t.F)) t ) /\
	    ( (a SUNTIL b)  = \t. ~((\t. ~b t) UNTIL (\t. ~a t /\ ~b t)) t ) /\
	    ( (a WHEN b)    = \t. ((\t. ~b t) UNTIL (\t. a t /\ b t)) t ) /\
	    ( (a SWHEN b)   = \t. ~((\t. ~a t \/ ~b t) UNTIL (\t. ~a t /\ b t)) t ) /\
	    ( (a BEFORE b)  = \t. ((\t. ~b t) UNTIL (\t. a t /\ ~b t)) t  ) /\
	    ( (a SBEFORE b) = \t. ~ ((\t. ~a t) UNTIL b) t  )
	`--),
	    REWRITE_TAC[ALWAYS_AS_UNTIL,EVENTUAL_AS_UNTIL,
			SBEFORE_AS_UNTIL,WHEN_AS_UNTIL,BEFORE_AS_UNTIL1]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
	    THEN REWRITE_TAC[SUNTIL_AS_SBEFORE1, SWHEN_AS_SUNTIL, NOT_UNTIL]
	    THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[DE_MORGAN_THM]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`b/\(~a\/~b)=~a/\b`--),PROP_TAC)]);



val WHEN_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. ((\t.F) WHEN (\t. ~a t)) t ) /\
	    ( (EVENTUAL a)  = \t. ~((\t.F) WHEN a) t ) /\
	    ( (a SUNTIL b)  = \t. ~((\t. ~b t) WHEN (\t. a t ==> b t)) t ) /\
	    ( (a UNTIL b)   = \t. (b WHEN (\t. a t ==> b t)) t  ) /\
	    ( (a SWHEN b)   = \t. ~((\t. ~a t) WHEN b) t ) /\
	    ( (a BEFORE b)  = \t. ((\t. ~b t) WHEN (\t. a t \/ b t)) t  ) /\
	    ( (a SBEFORE b) = \t. ~(b WHEN (\t. a t \/ b t)) t  )
	`--),
	    REWRITE_TAC[ALWAYS_AS_WHEN,EVENTUAL_AS_WHEN,
			BEFORE_AS_WHEN,UNTIL_AS_WHEN,
			SUNTIL_AS_SWHEN,SBEFORE_AS_SWHEN,
			(SYM SWHEN_AS_NOT_WHEN)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
	    THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC
	    THEN REWRITE_TAC[NOT_WHEN]);



val BEFORE_EXPRESSIVE = TAC_PROOF(
	([],--`
	    ( (ALWAYS a)    = \t. ((\t.F) BEFORE (\t. ~a t)) t ) /\
	    ( (EVENTUAL a)  = \t. ~((\t. F) BEFORE a) t ) /\
	    ( (a SUNTIL b)  = \t. ~((\t. ~a t) BEFORE b) t ) /\
	    ( (a UNTIL b)   = \t. (b BEFORE (\t. ~a t /\ ~b t)) t ) /\
	    ( (a SWHEN b)   = \t. ~(b BEFORE (\t. a t /\ b t)) t  ) /\
	    ( (a WHEN b)    = \t. ((\t. a t /\ b t) BEFORE (\t. ~a t /\ b t)) t  ) /\
	    ( (a SBEFORE b) = \t. ~(b BEFORE (\t. a t /\ ~b t)) t  )
	`--),
	    REWRITE_TAC[ALWAYS_AS_BEFORE,EVENTUAL_AS_BEFORE,
			UNTIL_AS_BEFORE1,WHEN_AS_UNTIL,
			SUNTIL_AS_SWHEN,SBEFORE_AS_SWHEN,
			(SYM SWHEN_AS_NOT_WHEN)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	    THEN REWRITE_TAC[NOT_BEFORE,SWHEN_AS_SUNTIL]
	    THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`b/\(a==>b)=b`--),PROP_TAC)]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~b/\(a\/b)=a/\~b`--),PROP_TAC)]
	    THEN ONCE_REWRITE_TAC[MORE_EVENT] THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~(a==>b)/\~b=a/\~b`--),PROP_TAC)]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~(a\/b)/\~(a/\~b)=~b/\~(a/\~b)`--),PROP_TAC)]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`b/\~(a/\b)=~a/\b`--),PROP_TAC)]
	    THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	    THEN REWRITE_TAC[]
	);


(*---------------------------------------------------------------------------
     Normal form theorems
 ---------------------------------------------------------------------------*)


val NEGATION_NORMAL_FORM = TAC_PROOF(
	([],--`
	 (~(NEXT a) t       = (NEXT (\t. ~a t)) t)		/\
	 (~(ALWAYS a) t     = (EVENTUAL (\t. ~a t)) t)		/\
	 (~(EVENTUAL a) t   = (ALWAYS (\t. ~a t)) t)		/\
	 (~(a WHEN b) t     = ((\t. ~a t) SWHEN b) t)		/\
         (~(a UNTIL b) t    = ((\t. ~a t) SBEFORE b) t) 	/\
         (~(a BEFORE b) t   = ((\t. ~a t) SUNTIL b) t)		/\
	 (~(a SWHEN b) t    = ((\t. ~a t) WHEN b) t)		/\
         (~(a SUNTIL b) t   = ((\t. ~a t) BEFORE b) t) 		/\
         (~(a SBEFORE b) t  = ((\t. ~a t) UNTIL b) t)		/\
	 (~(PNEXT a) t      = (PSNEXT (\t. ~a t)) t)		/\
	 (~(PSNEXT a) t     = (PNEXT (\t. ~a t)) t)		/\
	 (~(PALWAYS a) t    = (PEVENTUAL (\t. ~a t)) t)		/\
	 (~(PEVENTUAL a) t  = (PALWAYS (\t. ~a t)) t)		/\
	 (~(a PWHEN b) t    = ((\t. ~a t) PSWHEN b) t)		/\
         (~(a PUNTIL b) t   = ((\t. ~a t) PSBEFORE b) t) 	/\
         (~(a PBEFORE b) t  = ((\t. ~a t) PSUNTIL b) t)		/\
	 (~(a PSWHEN b) t   = ((\t. ~a t) PWHEN b) t)		/\
         (~(a PSUNTIL b) t  = ((\t. ~a t) PBEFORE b) t) 	/\
         (~(a PSBEFORE b) t = ((\t. ~a t) PUNTIL b) t)
	`--),
	let val past_nnf_thm =  TAC_PROOF(
	([],--`
	 (~(PNEXT a) t      = (PSNEXT (\t. ~a t)) t)		/\
	 (~(PSNEXT a) t     = (PNEXT (\t. ~a t)) t)		/\
	 (~(PALWAYS a) t    = (PEVENTUAL (\t. ~a t)) t)		/\
	 (~(PEVENTUAL a) t  = (PALWAYS (\t. ~a t)) t)		/\
	 (~(a PWHEN b) t    = ((\t. ~a t) PSWHEN b) t)		/\
         (~(a PUNTIL b) t   = ((\t. ~a t) PSBEFORE b) t) 	/\
         (~(a PBEFORE b) t  = ((\t. ~a t) PSUNTIL b) t)		/\
	 (~(a PSWHEN b) t   = ((\t. ~a t) PWHEN b) t)		/\
         (~(a PSUNTIL b) t  = ((\t. ~a t) PBEFORE b) t) 	/\
         (~(a PSBEFORE b) t = ((\t. ~a t) PUNTIL b) t)
	`--),
	PAST_TEMP_TAC2
	THEN REWRITE_TAC[PSNEXT,PNEXT,PRE,EQT_ELIM(ARITH_CONV(--`(0<t)=~(t=0)`--))]
	THEN BETA_TAC THEN PROP_TAC
	)
	in
	REWRITE_TAC[NOT_ALWAYS,NOT_EVENTUAL,
		    NOT_WHEN,NOT_UNTIL,NOT_BEFORE,
		    NOT_SWHEN,NOT_SUNTIL,NOT_SBEFORE,
		    past_nnf_thm]
	THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	THEN REWRITE_TAC[]
	end);





val past_cnf_thm = TAC_PROOF(
    ([],--`
     ((PNEXT (\t. a t /\ b t)) t      = (PNEXT a) t     /\ (PNEXT b) t)		/\
     ((PSNEXT (\t. a t /\ b t)) t     = (PSNEXT a) t    /\ (PSNEXT b) t)	/\
     ((PALWAYS (\t. a t /\ b t)) t    = (PALWAYS a) t   /\ (PALWAYS b) t)	/\
     (((\t. a t /\ b t) PWHEN c) t    = (a PWHEN c) t   /\ (b PWHEN c) t)	/\
     (((\t. a t /\ b t) PSWHEN c) t   = (a PSWHEN c) t  /\ (b PSWHEN c) t)	/\
     (((\t. a t /\ b t) PUNTIL c) t   = (a PUNTIL c) t  /\ (b PUNTIL c) t)	/\
     (((\t. a t /\ b t) PSUNTIL c) t  = (a PSUNTIL c) t /\ (b PSUNTIL c) t)	/\
     ((c PBEFORE (\t. a t \/ b t)) t  = (c PBEFORE a) t /\ (c PBEFORE b) t)	/\
     ((c PSBEFORE (\t. a t \/ b t)) t = (c PSBEFORE a) t /\ (c PSBEFORE b) t)
    `--),
    SPEC_TAC((--`t:num`--),(--`t:num`--))
    THEN INDUCT_TAC THENL[ALL_TAC,UNDISCH_HD_TAC]
    THEN BETA_TAC
    THEN REWRITE_TAC[INITIALISATION]
    THEN REWRITE_TAC(map (fn x => BETA_RULE(AP_THM x (--`SUC t`--)))
			 (CONJUNCTS RECURSION))
    THEN BETA_TAC
    THEN REWRITE_TAC[PNEXT,PSNEXT,ZERO_LEMMA,PRE,
		     EQT_ELIM(ARITH_CONV(--`(0<t)=~(t=0)`--))]
    THEN BETA_TAC
    THENL[
        PROP_TAC,
        DISCH_TAC THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
        THEN DISJ_CASES_TAC(SPEC(--`a(SUC t):bool`--)BOOL_CASES_AX)
        THEN DISJ_CASES_TAC(SPEC(--`b(SUC t):bool`--)BOOL_CASES_AX)
        THEN DISJ_CASES_TAC(SPEC(--`c(SUC t):bool`--)BOOL_CASES_AX)
        THEN ASM_REWRITE_TAC[]
	]
    );




val future_cnf_thm = TAC_PROOF(
    ([],--`
     ((NEXT (\t. a t /\ b t)) t       = (NEXT a) t      /\ (NEXT b) t)		/\
     ((ALWAYS (\t. a t /\ b t)) t     = (ALWAYS a) t    /\ (ALWAYS b) t)	/\
     (((\t. a t /\ b t) WHEN c) t     = (a WHEN c) t    /\ (b WHEN c) t)	/\
     (((\t. a t /\ b t) SWHEN c) t    = (a SWHEN c) t   /\ (b SWHEN c) t)	/\
     (((\t. a t /\ b t) UNTIL c) t    = (a UNTIL c) t   /\ (b UNTIL c) t)	/\
     (((\t. a t /\ b t) SUNTIL c) t   = (a SUNTIL c) t  /\ (b SUNTIL c) t)	/\
     ((c SBEFORE (\t. a t \/ b t)) t  = (c SBEFORE a) t /\ (c SBEFORE b) t)
    `--),
	REWRITE_TAC[past_cnf_thm]
	THEN REWRITE_TAC[NEXT,ALWAYS] THEN BETA_TAC
	THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV FORALL_AND_CONV)
	THEN BETA_TAC THEN REWRITE_TAC[BEFORE_AS_SUNTIL]


	THEN REWRITE_TAC[WHEN_SIGNAL,SWHEN_SIGNAL,UNTIL_SIGNAL,SUNTIL_SIGNAL,SBEFORE_SIGNAL]
	THEN BETA_TAC
	THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[],
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
		(--`(delta<delta') \/ (delta=delta') \/(delta'<delta)`--)))
	    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    THEN RES_TAC (* cases (delta<delta') and (delta'<delta) are seen to be wrong *)
	    THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[SYM x]))
	    THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
		(--`(delta<delta') \/ (delta=delta') \/(delta'<delta)`--)))
	    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    THEN RES_TAC (* cases (delta<delta') and (delta'<delta) are seen to be wrong *)
	    THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[SYM x]))
	    THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
		(--`(delta<=delta') \/ (delta'<=delta)`--)))
	    THENL[EXISTS_TAC(--`delta:num`--),EXISTS_TAC(--`delta':num`--)]
	    THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN DISCH_TAC
	    THEN IMP_RES_TAC LESS_EQ_TRANS
	    THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    ]);




val before_cnf_thm = TAC_PROOF(
	([],--`((c BEFORE (\t. a t \/ b t)) t = (c BEFORE a) t  /\ (c BEFORE b) t)`--),
	REWRITE_TAC[BEFORE_AS_SUNTIL] THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(~a=~b/\~c) = (a = b\/c)`--),PROP_TAC)]
	THEN REWRITE_TAC[SUNTIL_SIGNAL] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ1_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ_CASES_TAC (SPEC(--`t:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THEN ASM_REWRITE_TAC[]
	    THENL[
		LEFT_EXISTS_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
					(--`(delta<d) \/ (delta=d) \/(d<delta)`--)))
		THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    	THENL[EXISTS_TAC(--`delta:num`--),
			EXISTS_TAC(--`d:num`--)
			THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x])),
			EXISTS_TAC(--`d:num`--)]
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN DISCH_TAC
	    	THEN IMP_RES_TAC LESS_TRANS
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[],
		EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    	THEN REPEAT STRIP_TAC THEN RES_TAC],
	    DISJ_CASES_TAC (SPECL[(--`t:num`--), (--`a:num->bool`--)]
			   (GENL [(--`t0:num`--),(--`b:num->bool`--)]DELTA_CASES))
	    THEN ASM_REWRITE_TAC[]
	    THENL[
		LEFT_EXISTS_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
					(--`(delta<d) \/ (delta=d) \/(d<delta)`--)))
		THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    	THENL[EXISTS_TAC(--`delta:num`--),
			EXISTS_TAC(--`d:num`--)
			THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x])),
			EXISTS_TAC(--`d:num`--)]
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN DISCH_TAC
	    	THEN IMP_RES_TAC LESS_TRANS
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[],
		EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    	THEN REPEAT STRIP_TAC THEN RES_TAC]
	]);





val CONJUNCTIVE_NORMAL_FORM = TAC_PROOF(
	([],--`
	 ((NEXT (\t. a t /\ b t))       = \t. (NEXT a) t      /\ (NEXT b) t)	  /\
	 ((ALWAYS (\t. a t /\ b t))     = \t. (ALWAYS a) t    /\ (ALWAYS b) t)	  /\
	 (((\t. a t /\ b t) WHEN c)     = \t. (a WHEN c) t    /\ (b WHEN c) t)	  /\
	 (((\t. a t /\ b t) SWHEN c)    = \t. (a SWHEN c) t   /\ (b SWHEN c) t)	  /\
         (((\t. a t /\ b t) UNTIL c)    = \t. (a UNTIL c) t   /\ (b UNTIL c) t)	  /\
         (((\t. a t /\ b t) SUNTIL c)   = \t. (a SUNTIL c) t  /\ (b SUNTIL c) t)  /\
         ((c BEFORE (\t. a t \/ b t))   = \t. (c BEFORE a) t  /\ (c BEFORE b) t)  /\
         ((c SBEFORE (\t. a t \/ b t))  = \t. (c SBEFORE a) t /\ (c SBEFORE b) t) /\
	 ((PNEXT (\t. a t /\ b t))      = \t. (PNEXT a) t     /\ (PNEXT b) t)	  /\
	 ((PSNEXT (\t. a t /\ b t))     = \t. (PSNEXT a) t    /\ (PSNEXT b) t)	  /\
	 ((PALWAYS (\t. a t /\ b t))    = \t. (PALWAYS a) t   /\ (PALWAYS b) t)	  /\
	 (((\t. a t /\ b t) PWHEN c)    = \t. (a PWHEN c) t   /\ (b PWHEN c) t)	  /\
	 (((\t. a t /\ b t) PSWHEN c)   = \t. (a PSWHEN c) t  /\ (b PSWHEN c) t)  /\
         (((\t. a t /\ b t) PUNTIL c)   = \t. (a PUNTIL c) t  /\ (b PUNTIL c) t)  /\
         (((\t. a t /\ b t) PSUNTIL c)  = \t. (a PSUNTIL c) t /\ (b PSUNTIL c) t) /\
         ((c PBEFORE (\t. a t \/ b t))  = \t. (c PBEFORE a) t /\ (c PBEFORE b) t) /\
         ((c PSBEFORE (\t. a t \/ b t)) = \t. (c PSBEFORE a) t /\ (c PSBEFORE b) t)
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REWRITE_TAC[past_cnf_thm,future_cnf_thm,before_cnf_thm]
	);


val DISJUNCTIVE_NORMAL_FORM = TAC_PROOF(
	([],--`
	 ((NEXT (\t. a t \/ b t))       = \t. (NEXT a) t      \/ (NEXT b) t)	   /\
	 ((EVENTUAL (\t. a t \/ b t))   = \t. (EVENTUAL a) t  \/ (EVENTUAL b) t)   /\
	 (((\t. a t \/ b t) WHEN c)     = \t. (a WHEN c) t    \/ (b WHEN c) t)	   /\
	 (((\t. a t \/ b t) SWHEN c)    = \t. (a SWHEN c) t   \/ (b SWHEN c) t)	   /\
         ((a UNTIL (\t. b t \/ c t))    = \t. (a UNTIL b) t   \/ (a UNTIL c) t)	   /\
         ((a SUNTIL (\t. b t \/ c t))   = \t. (a SUNTIL b) t  \/ (a SUNTIL c) t)   /\
         (((\t. a t \/ b t) BEFORE c)   = \t. (a BEFORE c) t  \/ (b BEFORE c) t)   /\
         (((\t. a t \/ b t) SBEFORE c)  = \t. (a SBEFORE c) t \/ (b SBEFORE c) t)  /\
 	 ((PNEXT (\t. a t \/ b t))      = \t. (PNEXT a) t      \/ (PNEXT b) t)	   /\
	 ((PEVENTUAL (\t. a t \/ b t))  = \t. (PEVENTUAL a) t  \/ (PEVENTUAL b) t) /\
	 (((\t. a t \/ b t) PWHEN c)    = \t. (a PWHEN c) t    \/ (b PWHEN c) t)   /\
	 (((\t. a t \/ b t) PSWHEN c)   = \t. (a PSWHEN c) t   \/ (b PSWHEN c) t)  /\
         ((a PUNTIL (\t. b t \/ c t))   = \t. (a PUNTIL b) t   \/ (a PUNTIL c) t)  /\
         ((a PSUNTIL (\t. b t \/ c t))  = \t. (a PSUNTIL b) t  \/ (a PSUNTIL c) t) /\
         (((\t. a t \/ b t) PBEFORE c)  = \t. (a PBEFORE c) t  \/ (b PBEFORE c) t) /\
         (((\t. a t \/ b t) PSBEFORE c) = \t. (a PSBEFORE c) t \/ (b PSBEFORE c) t)
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM] THEN BETA_TAC
	THEN REWRITE_TAC
		(map (fn x => BETA_RULE(AP_THM (SYM x) (--`n:num`--)))
     		     (CONJUNCTS CONJUNCTIVE_NORMAL_FORM))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



(*---------------------------------------------------------------------------
        Simplification theorems
 ---------------------------------------------------------------------------*)

val SIMPLIFY = TAC_PROOF(
	([],--`
	 (NEXT (\t.F)		 = \t.F) /\
	 (NEXT (\t.T)		 = \t.T) /\
	 (ALWAYS (\t.T)		 = \t.T) /\
	 (ALWAYS (\t.F)		 = \t.F) /\
	 (EVENTUAL (\t.T)	 = \t.T) /\
	 (EVENTUAL (\t.F)	 = \t.F) /\
	 (((\t. F) SUNTIL b)	 = b) /\
         (((\t. T) SUNTIL b)	 = (EVENTUAL b)) /\
         ((a SUNTIL (\t. F))	 = \t.F) /\
         ((a SUNTIL (\t. T))	 = \t.T) /\
         ((a SUNTIL a)		 = a) /\
	 (((\t. F) UNTIL b)	 = b) /\
         (((\t. T) UNTIL b)	 = \t.T) /\
         ((a UNTIL (\t. F))	 = (ALWAYS a)) /\
         ((a UNTIL (\t. T))	 = \t.T) /\
         ((a UNTIL a)		 = a) /\
	 (((\t. F) SWHEN b)	 = \t.F) /\
         (((\t. T) SWHEN b) 	 = (EVENTUAL b)) /\
         ((a SWHEN (\t. F)) 	 = \t.F) /\
         ((a SWHEN (\t. T)) 	 = a) /\
         ((a SWHEN a) 		 = (EVENTUAL a)) /\
	 (((\t. F) WHEN b) 	 = (ALWAYS (\t. ~b t))) /\
         (((\t. T) WHEN b) 	 = \t.T) /\
         ((a WHEN (\t. F)) 	 = \t.T) /\
         ((a WHEN (\t. T)) 	 = a) /\
         ((a WHEN a) 		 = \t.T) /\
	 (((\t. F) SBEFORE b)    = \t.F) /\
         (((\t. T) SBEFORE b)    = \t.~b t) /\
         ((a SBEFORE (\t. F))    = (EVENTUAL a)) /\
         ((a SBEFORE (\t. T))    = \t.F) /\
         ((a SBEFORE a) 	 = \t.F) /\
	 (((\t. F) BEFORE b) 	 = (ALWAYS (\t. ~b t))) /\
         (((\t. T) BEFORE b) 	 = \t.~b t) /\
         ((a BEFORE (\t. F)) 	 = \t.T) /\
         ((a BEFORE (\t. T)) 	 = \t.F) /\
         ((a BEFORE a) 	 	 = (ALWAYS (\t. ~a t))) /\
	 (PNEXT (\t.F)		 = InitPoint) /\
	 (PNEXT (\t.T)		 = \t.T) /\
	 (PSNEXT (\t.F)		 = \t.F) /\
	 (PSNEXT (\t.T)		 = \t. ~InitPoint t) /\
	 (PALWAYS (\t.T)	 = \t.T) /\
	 (PALWAYS (\t.F)	 = \t.F) /\
	 (PEVENTUAL (\t.T)	 = \t.T) /\
	 (PEVENTUAL (\t.F)	 = \t.F) /\
	 (((\t. F) PSUNTIL b)	 = b) /\
         (((\t. T) PSUNTIL b)	 = (PEVENTUAL b)) /\
         ((a PSUNTIL (\t. F))	 = \t.F) /\
         ((a PSUNTIL (\t. T))	 = \t.T) /\
         ((a PSUNTIL a)		 = a) /\
	 (((\t. F) PUNTIL b)	 = b) /\
         (((\t. T) PUNTIL b)	 = \t.T) /\
         ((a PUNTIL (\t. F))	 = (PALWAYS a)) /\
         ((a PUNTIL (\t. T))	 = \t.T) /\
         ((a PUNTIL a)		 = a) /\
	 (((\t. F) PSWHEN b)	 = \t.F) /\
         (((\t. T) PSWHEN b) 	 = (PEVENTUAL b)) /\
         ((a PSWHEN (\t. F)) 	 = \t.F) /\
         ((a PSWHEN (\t. T)) 	 = a) /\
         ((a PSWHEN a) 		 = (PEVENTUAL a)) /\
	 (((\t. F) PWHEN b) 	 = (PALWAYS (\t. ~b t))) /\
         (((\t. T) PWHEN b) 	 = \t.T) /\
         ((a PWHEN (\t. F)) 	 = \t.T) /\
         ((a PWHEN (\t. T)) 	 = a) /\
         ((a PWHEN a) 		 = \t.T) /\
	 (((\t. F) PSBEFORE b)   = \t.F) /\
         (((\t. T) PSBEFORE b)   = \t.~b t) /\
         ((a PSBEFORE (\t. F))   = (PEVENTUAL a)) /\
         ((a PSBEFORE (\t. T))   = \t.F) /\
         ((a PSBEFORE a) 	 = \t.F) /\
	 (((\t. F) PBEFORE b) 	 = (PALWAYS (\t. ~b t))) /\
         (((\t. T) PBEFORE b) 	 = \t.~b t) /\
         ((a PBEFORE (\t. F)) 	 = \t.T) /\
         ((a PBEFORE (\t. T)) 	 = \t.F) /\
         ((a PBEFORE a) 	 = (PALWAYS (\t. ~a t)))
 	`--),
	REWRITE_TAC[WHEN_SIMP,SWHEN_SIMP]
	THEN REWRITE_TAC[UNTIL_SIMP,SUNTIL_SIMP]
	THEN REWRITE_TAC[BEFORE_SIMP,SBEFORE_SIMP]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REWRITE_TAC[NEXT,ALWAYS,EVENTUAL] THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,InitPoint] THEN BETA_TAC
	THEN REWRITE_TAC[ARITH_PROVE(--`~(n=0)=(0<n)`--)]
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );





val MORE_EVENT = TAC_PROOF(
	([],--`
	 ((a WHEN b) 	 = ((\t. a t /\ b t) WHEN b)		) /\
     	 ((a UNTIL b)	 = ((\t. a t /\ ~(b t)) UNTIL b)	) /\
    	 ((a BEFORE b) 	 = ((\t. a t /\ ~(b t)) BEFORE b)	) /\
    	 ((a SWHEN b) 	 = ((\t. a t /\ b t) SWHEN b)		) /\
    	 ((a SUNTIL b) 	 = ((\t. a t /\ ~(b t)) SUNTIL b)	) /\
    	 ((a SBEFORE b)  = ((\t. a t /\ ~(b t)) SBEFORE b)	) /\
	 ((a PWHEN b)    = ((\t. a t /\ b t) PWHEN b)		) /\
         ((a PUNTIL b)   = ((\t. a t /\ ~(b t)) PUNTIL b)	) /\
         ((a PBEFORE b)  = ((\t. a t /\ ~(b t)) PBEFORE b)	) /\
         ((a PSWHEN b)   = ((\t. a t /\ b t) PSWHEN b) 		) /\
         ((a PSUNTIL b)  = ((\t. a t /\ ~(b t)) PSUNTIL b) 	) /\
         ((a PSBEFORE b) = ((\t. a t /\ ~(b t)) PSBEFORE b) 	) `--),
	ONCE_REWRITE_TAC[MORE_EVENT] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a/\b)/\b = a/\b`--),PROP_TAC)]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT CONJ_TAC THEN PAST_TEMP_TAC );


val IMMEDIATE_EVENT = TAC_PROOF(
	([],--`
	   b t ==>
		((a WHEN b) t     = a t) 	/\
     		((a UNTIL b) t    = T) 		/\
     		((a BEFORE b) t   = F) 		/\
     		((b BEFORE a) t   = ~a t) 	/\
     		((a SWHEN b) t    = a t) 	/\
     		((a SUNTIL b) t   = T) 		/\
     		((a SBEFORE b) t  = F) 		/\
     		((b SBEFORE a) t  = ~ a t) 	/\
	 	((a PWHEN b) t    = a t)	/\
         	((a PUNTIL b) t   = T)	 	/\
         	((a PBEFORE b) t  = F)	 	/\
         	((b PBEFORE a) t  = ~a t) 	/\
	 	((a PSWHEN b) t   = a t)	/\
         	((a PSUNTIL b) t  = T)	 	/\
         	((a PSBEFORE b) t = F)	 	/\
         	((b PSBEFORE a) t = ~a t) `--),
	DISCH_TAC
	THEN ONCE_REWRITE_TAC[RECURSION] THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	THEN ONCE_REWRITE_TAC[RECURSION] THEN BETA_TAC THEN ASM_REWRITE_TAC[]);


val NO_FUTURE_EVENT = NO_EVENT;

val NO_PAST_EVENT = TAC_PROOF(
	([],--`
	   (PALWAYS (\t. ~b t)) t ==>
	 	((a PWHEN b) t    = T)				/\
         	((a PUNTIL b) t   = (PALWAYS a) t)	 	/\
         	((a PBEFORE b) t  = T)	 			/\
         	((b PBEFORE a) t  = (PALWAYS (\t. ~a t)) t) 	/\
	 	((a PSWHEN b) t   = F)				/\
         	((a PSUNTIL b) t  = F)	 			/\
         	((a PSBEFORE b) t = (PEVENTUAL a) t)	 	/\
         	((b PSBEFORE a) t = F) `--),
	PAST_TEMP_TAC2 );


val SOME_FUTURE_EVENT = SOME_EVENT;

val SOME_PAST_EVENT = TAC_PROOF(
	([],--`
	   (PEVENTUAL b) t ==>
	 	((a PWHEN b) t    = (a PSWHEN b) t)		/\
         	((a PUNTIL b) t   = (a PSUNTIL b) t)	 	/\
         	((a PBEFORE b) t  = (a PSBEFORE b) t)		/\
         	((b PBEFORE a) t  = (b PSBEFORE a) t)
	`--),
	PAST_TEMP_TAC2 );



(*---------------------------------------------------------------------------
      Separation theorems
 ---------------------------------------------------------------------------*)


val PSUNTIL_WRAP = BETA_RULE(AP_THM PSUNTIL_REC (--`t:num`--));
val PBEFORE_WRAP = BETA_RULE(AP_THM PBEFORE_REC (--`t:num`--));

val NEXT_AND_PNEXT_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t /\ PNEXT b t))
		=
		\t. (b t /\ NEXT a t)
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[NEXT,PNEXT] THEN BETA_TAC
	THEN REWRITE_TAC[PRE]
	THEN REWRITE1_TAC(EQT_ELIM(ARITH_CONV(--`~((SUC y)= 0)`--)))
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	);



val NEXT_AND_PSNEXT_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t /\ PSNEXT b t))
		=
		\t. (b t /\ NEXT a t)
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[NEXT,PSNEXT] THEN BETA_TAC
	THEN REWRITE_TAC[PRE]
	THEN REWRITE1_TAC(EQT_ELIM(ARITH_CONV(--`0<(SUC y)`--)))
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	);



val NEXT_AND_PSUNTIL_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t /\ (b PSUNTIL c) t))
		=
		\t. NEXT(\t. a t /\ c t) t \/
		    (b PSUNTIL c) t /\ NEXT(\t. a t /\ b t) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[PSUNTIL_WRAP]))
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\(c\/b) = (a/\c) \/ (a/\b)`--),PROP_TAC)]
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`\t:num. a t /\ b t /\ PSNEXT (b PSUNTIL c) t`--),
		       (--`\t:num. a t /\ c t`--)]
		      OR_NEXT))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\b/\c = (a/\b)/\c`--),PROP_TAC)]
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`(b PSUNTIL c)`--),
		       (--`\t:num. a t /\ b t`--)]
		      (GEN_ALL NEXT_AND_PSNEXT_SEPARATE)))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



val NEXT_AND_PBEFORE_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t /\ (b PBEFORE c) t))
		=
		\t. NEXT(\t. a t /\ b t /\ ~c t) t \/
		    (b PBEFORE c) t /\ NEXT(\t. a t /\ ~c t) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[PBEFORE_WRAP]))
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\~c/\(b\/d)
					= (a/\b/\~c) \/ ((a/\~c)/\d)`--),PROP_TAC)]
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`\t:num. (a t /\ ~(c t)) /\ PNEXT (b PBEFORE c) t`--),
		       (--`\t:num. a t /\ b t /\ ~(c t)`--)]
		      OR_NEXT))
	THEN BETA_TAC
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`(b PBEFORE c)`--),
		       (--`\t:num. a t /\ ~c t`--)]
		      (GEN_ALL NEXT_AND_PNEXT_SEPARATE)))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



val NEXT_OR_PNEXT_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t \/ PNEXT b t))
		=
		\t. (b t \/ NEXT a t)
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN REWRITE_TAC[NEXT,PNEXT] THEN BETA_TAC
	THEN REWRITE_TAC[PRE]
	THEN REWRITE1_TAC(EQT_ELIM(ARITH_CONV(--`~((SUC y)= 0)`--)))
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	);



val NEXT_OR_PSNEXT_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t \/ PSNEXT b t))
		=
		\t. (b t \/ NEXT a t)
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN REWRITE_TAC[NEXT,PSNEXT] THEN BETA_TAC
	THEN REWRITE_TAC[PRE]
	THEN REWRITE1_TAC(EQT_ELIM(ARITH_CONV(--`0<(SUC y)`--)))
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	);



val NEXT_OR_PSUNTIL_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t \/ (b PSUNTIL c) t))
		=
		\t. NEXT(\t. a t \/ c t) t \/
		    (b PSUNTIL c) t /\ NEXT b t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[PSUNTIL_WRAP]))
	THEN REWRITE_TAC[TAC_PROOF(([],--`a\/c\/b = (a\/c) \/ b`--),PROP_TAC)]
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`\t:num. b t /\ PSNEXT (b PSUNTIL c) t`--),
		       (--`\t:num. a t \/ c t`--)]
		      OR_NEXT))
	THEN BETA_TAC
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`(b PSUNTIL c)`--),
		       (--`b:num->bool`--)]
		      (GEN_ALL NEXT_AND_PSNEXT_SEPARATE)))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



val NEXT_OR_PBEFORE_SEPARATE = TAC_PROOF(
	([], --`(NEXT (\t. a t \/ (b PBEFORE c) t))
		=
		\t. NEXT(\t. a t \/ ~c t) t /\
		    ((b PBEFORE c) t \/ NEXT (\t. a t \/ b t) t)
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[PBEFORE_WRAP]))
	THEN REWRITE_TAC[TAC_PROOF(([],--`a\/~c/\(b\/d)
					= (a\/~c) /\ ((a\/b)\/d)`--),PROP_TAC)]
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`\t:num. (a t \/ b t) \/ PNEXT (b PBEFORE c) t`--),
		       (--`\t:num. a t \/ ~c t`--)]
		      AND_NEXT))
	THEN BETA_TAC
	THEN SUBST1_TAC(BETA_RULE
		(SPECL[(--`(b PBEFORE c)`--),
		       (--`\t:num. a t \/ b t`--)]
		      (GEN_ALL NEXT_OR_PNEXT_SEPARATE)))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);







val SUNTIL_AND_SEPARATE = TAC_PROOF(
	([], --`((\t. a t /\ b t) SUNTIL c) =
		  \t. (a SUNTIL c) t /\ (b SUNTIL c) t`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[SUNTIL_SIGNAL] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
	    THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
	    THEN ASM_REWRITE_TAC[],
	    MY_MP_TAC (--`delta'=(delta:num)`--)
	    THENL[
		REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(a=b) = ~((a<b) \/ (b<a))`--))]
		THEN STRIP_TAC THEN RES_TAC,
		DISCH_TAC]
	    THEN POP_ASSUM(fn x=>RULE_ASSUM_TAC(REWRITE_RULE[x]))
	    THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
	    THEN ASM_REWRITE_TAC[]
	    ]);




val SUNTIL_AND_PNEXT_SEPARATE = TAC_PROOF(
	([], --`(a SUNTIL (\t. b t /\ PNEXT c t))
		=
		\t. (b t /\ PNEXT c t)
		    \/
		    (a SUNTIL (\t. a t /\ c t /\ NEXT b t)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a\/b) = ~a==>b`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (b ==> (a=c))
				==>
				((b ==> a) = (b ==> c)) `--),PROP_TAC))
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN REWRITE_TAC[NEXT,PNEXT,SUNTIL_SIGNAL,DE_MORGAN_THM] THEN BETA_TAC
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(x + SUC y = 0)`--))]
	THEN REWRITE_TAC[ADD_CLAUSES,PRE]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\~(a/\c/\b) = a/\(c==>~b)`--),PROP_TAC)]
	THEN DISCH_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[ASM_REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(x<0)`--))],ALL_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1 THEN CONJ_TAC
	    THENL[
		GEN_TAC THEN DISCH_TAC THEN RES_TAC
		THEN ASM_REWRITE_TAC[TAC_PROOF(([],--`(c==>~b)=~(b/\c)`--),PROP_TAC)]
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t'=0)\/(0<t')`--)))
		THENL[ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
		THEN IMP_RES_TAC LESS_ADD_1
		THEN LEFT_NO_FORALL_TAC 13 (--`p':num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,ONE]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(t'<delta) /\ (t'=0+(p'+1)) /\ (delta=0+(p'''+1))
			    ==> p'<SUC p''' `--)))
		THEN ASM_REWRITE_TAC[]
		THEN STRIP_TAC,
		LEFT_NO_FORALL_TAC 4 (--`p:num`--) THEN UNDISCH_HD_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0+(p+1)) ==> p<delta`--)))
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,ONE]
		THEN STRIP_TAC
		],
	    (* ------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[UNDISCH_NO_TAC 3 THEN ASM_REWRITE_TAC[ADD_CLAUSES], ALL_TAC]
	    THEN LEFT_NO_FORALL_TAC 4 (--`0`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC,
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[ASM_REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(x<0)`--))],ALL_TAC]
	    THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
	    THEN ASM_REWRITE_TAC[TAC_PROOF(([],--`~(b/\c)=(c==>~b)`--),PROP_TAC)]
	    THEN MAP_EVERY POP_NO_TAC [10,7,6,3,2,1,0]
	    THEN UNDISCH_NO_TAC 1
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(x<delta) ==> (SUC(x+t) = delta+t) \/ (SUC x < delta)`--)))
	    THEN DISCH_TAC THEN LEFT_NO_FORALL_TAC 1 (--`t:num`--)
	    THEN POP_ASSUM (fn x => DISJ_CASES_TAC x THEN ASM_REWRITE_TAC[])
	    THEN RES_TAC THEN UNDISCH_NO_TAC 5 THEN REWRITE_TAC[ADD_CLAUSES]
	]);



val SUNTIL_AND_PSNEXT_SEPARATE = TAC_PROOF(
	([], --`(a SUNTIL (\t. b t /\ PSNEXT c t))
		=
		\t. (b t /\ PSNEXT c t)
		    \/
		    (a SUNTIL (\t. a t /\ c t /\ NEXT b t)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a\/b) = ~a==>b`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (b ==> (a=c))
				==>
				((b ==> a) = (b ==> c)) `--),PROP_TAC))
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN REWRITE_TAC[NEXT,PSNEXT,SUNTIL_SIGNAL,DE_MORGAN_THM] THEN BETA_TAC
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`0<x + SUC y`--))]
	THEN REWRITE_TAC[ADD_CLAUSES,PRE]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\~(a/\c/\b) = a/\(c==>~b)`--),PROP_TAC)]
	THEN DISCH_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[ASM_REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(x<0)`--))],ALL_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1 THEN CONJ_TAC
	    THENL[
		GEN_TAC THEN DISCH_TAC THEN RES_TAC
		THEN ASM_REWRITE_TAC[TAC_PROOF(([],--`(c==>~b)=~(b/\c)`--),PROP_TAC)]
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t'=0)\/(0<t')`--)))
		THENL[ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
		THEN IMP_RES_TAC LESS_ADD_1
		THEN LEFT_NO_FORALL_TAC 13 (--`p':num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,ONE]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(t'<delta) /\ (t'=0+(p'+1)) /\ (delta=0+(p'''+1))
			    ==> p'<SUC p''' `--)))
		THEN ASM_REWRITE_TAC[]
		THEN STRIP_TAC,
		LEFT_NO_FORALL_TAC 4 (--`p:num`--) THEN UNDISCH_HD_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0+(p+1)) ==> p<delta`--)))
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,ONE]
		THEN STRIP_TAC
		],
	    (* ------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[UNDISCH_NO_TAC 3 THEN ASM_REWRITE_TAC[ADD_CLAUSES], ALL_TAC]
	    THEN LEFT_NO_FORALL_TAC 4 (--`0`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC,
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0)\/(0<delta)`--)))
	    THENL[ASM_REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(x<0)`--))],ALL_TAC]
	    THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
	    THEN ASM_REWRITE_TAC[TAC_PROOF(([],--`~(b/\c)=(c==>~b)`--),PROP_TAC)]
	    THEN MAP_EVERY POP_NO_TAC [10,7,6,3,2,1,0]
	    THEN UNDISCH_NO_TAC 1
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(x<delta) ==> (SUC(x+t) = delta+t) \/ (SUC x < delta)`--)))
	    THEN DISCH_TAC THEN LEFT_NO_FORALL_TAC 1 (--`t:num`--)
	    THEN POP_ASSUM (fn x => DISJ_CASES_TAC x THEN ASM_REWRITE_TAC[])
	    THEN RES_TAC THEN UNDISCH_NO_TAC 5 THEN REWRITE_TAC[ADD_CLAUSES]
	]);



val SUNTIL_OR_PNEXT_SEPARATE = TAC_PROOF(
	([], --`((\t. a t \/ PNEXT b t) SUNTIL c)
		=
		\t. (c t) \/
		    (a t \/ PNEXT b t) /\ ((\t. b t \/ NEXT a t ) SUNTIL (NEXT c)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`~a==>b = (a\/b)`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c\/a) = (c\/b)) `--),PROP_TAC))
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c/\a) = (c/\b)) `--),PROP_TAC))
	THEN REWRITE_TAC[SUNTIL_NEXT]
	THEN REWRITE_TAC[NEXT_OR_PNEXT_SEPARATE]
	);



val SUNTIL_OR_PSNEXT_SEPARATE = TAC_PROOF(
	([], --`((\t. a t \/ PSNEXT b t) SUNTIL c)
		=
		\t. (c t) \/
		    (a t \/ PSNEXT b t) /\ ((\t. b t \/ NEXT a t ) SUNTIL (NEXT c)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`~a==>b = (a\/b)`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c\/a) = (c\/b)) `--),PROP_TAC))
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c/\a) = (c/\b)) `--),PROP_TAC))
	THEN REWRITE_TAC[SUNTIL_NEXT]
	THEN REWRITE_TAC[NEXT_OR_PSNEXT_SEPARATE]
	);



val BEFORE_OR_RIGHT_SEPARATE = TAC_PROOF(
	([],--`((c BEFORE (\t. a t \/ b t)) = \t. (c BEFORE a) t  /\ (c BEFORE b) t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[BEFORE_AS_SUNTIL] THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(~a=~b/\~c) = (a = b\/c)`--),PROP_TAC)]
	THEN REWRITE_TAC[SUNTIL_SIGNAL] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM] THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ1_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
	    THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    DISJ_CASES_TAC (SPEC(--`t:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THEN ASM_REWRITE_TAC[]
	    THENL[
		LEFT_EXISTS_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
					(--`(delta<d) \/ (delta=d) \/(d<delta)`--)))
		THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    	THENL[EXISTS_TAC(--`delta:num`--),
			EXISTS_TAC(--`d:num`--)
			THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x])),
			EXISTS_TAC(--`d:num`--)]
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN DISCH_TAC
	    	THEN IMP_RES_TAC LESS_TRANS
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[],
		EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    	THEN REPEAT STRIP_TAC THEN RES_TAC],
	    DISJ_CASES_TAC (SPECL[(--`t:num`--), (--`a:num->bool`--)]
			   (GENL [(--`t0:num`--),(--`b:num->bool`--)]DELTA_CASES))
	    THEN ASM_REWRITE_TAC[]
	    THENL[
		LEFT_EXISTS_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
					(--`(delta<d) \/ (delta=d) \/(d<delta)`--)))
		THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    	THENL[EXISTS_TAC(--`delta:num`--),
			EXISTS_TAC(--`d:num`--)
			THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x])),
			EXISTS_TAC(--`d:num`--)]
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    	THEN GEN_TAC THEN DISCH_TAC
	    	THEN IMP_RES_TAC LESS_TRANS
	    	THEN RES_TAC THEN ASM_REWRITE_TAC[],
		EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    	THEN REPEAT STRIP_TAC THEN RES_TAC]
	]);



val SUNTIL_OR_SEPARATE = TAC_PROOF(
	([], --`(a SUNTIL (\t. b t \/ c t)) = \t. (a SUNTIL b) t \/ (a SUNTIL c) t`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[SUNTIL_AS_BEFORE] THEN BETA_TAC
	THEN REWRITE_TAC[BEFORE_OR_RIGHT_SEPARATE] THEN BETA_TAC
	THEN REWRITE_TAC[NOT_BEFORE,DE_MORGAN_THM]);





val MAX_EXISTS = TAC_PROOF(
	([], --`t1<= t2
		==>
		(?x. t1<=x /\ x<=t2 /\ phi x)
		==>
		(?xmax.
			t1<=xmax /\ xmax<=t2 /\ phi xmax /\
			(!y. xmax<y /\ y<=t2 ==> ~phi y))`--),
	DISCH_TAC
	THEN MY_MP_TAC (--`?psi. !x. x<=t2 ==> (phi(x) = ~psi(t2-x))`--)
	THENL[
	    EXISTS_TAC(--`\x. ~phi(t2-x)`--) THEN BETA_TAC
	    THEN REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`x<=t2 ==> (t2-(t2-x) = x)`--)))
	    THEN ASM_REWRITE_TAC[],
	    STRIP_TAC]
	THEN STRIP_TAC
	THEN MY_MP_TAC (--`?y. y<=t2-t1 /\ ~psi y `--)
	THENL[
	    EXISTS_TAC (--`t2-x:num`--)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`t1<=x /\ x<=t2 ==> (t2 - x <= t2 - t1)`--)))
	    THEN ASM_REWRITE_TAC[] THEN RES_TAC,
	    DISCH_TAC]
	THEN ASSUME_TAC(BETA_RULE(SPEC(--`\y. y<=t2-t1 /\ ~psi y`--)WOP))
	THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a==>~(b/\~c) = a/\b==>c`--),PROP_TAC)]
	THEN STRIP_TAC THEN EXISTS_TAC (--`t2-n`--)
	THEN REPEAT STRIP_TAC
	THENL[
	    MAP_EVERY UNDISCH_NO_TAC [8,6,5,2] THEN CONV_TAC ARITH_CONV,
	    MAP_EVERY UNDISCH_NO_TAC [8,6,5,2] THEN CONV_TAC ARITH_CONV,
	    LEFT_NO_FORALL_TAC 7 (--`t2-n`--) THEN UNDISCH_HD_TAC
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t2-n<=t2`--))]
	    THEN DISCH_TAC THEN POP_ASSUM SUBST1_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`n<=t2-t1 ==> (t2-(t2-n) = n)`--)))
	    THEN ASM_REWRITE_TAC[],
	    RES_TAC THEN UNDISCH_NO_TAC 4 THEN REWRITE_TAC[]
	    THEN POP_NO_ASSUM 8 MATCH_MP_TAC
	    THEN MAP_EVERY UNDISCH_NO_TAC [15,13,12,9,7,6] THEN CONV_TAC ARITH_CONV
	]);





val SUNTIL_AND_PSUNTIL_SEPARATE = TAC_PROOF(
	([], --`(a SUNTIL (\t. b t /\ (c PSUNTIL d) t))
		=
		\t. (c PSUNTIL d) t /\ ((\t. a t /\ NEXT c t) SUNTIL b) t \/
		    (a SUNTIL (\t. d t /\ ((\t. a t /\ NEXT c t) SUNTIL b) t)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[SUNTIL_LINORD,UPTO,PSUNTIL,NEXT]
	THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    (* Proving that the lhs implies the rhs. The point of time where the event	*)
	    (* b /\ (c PSUNTIL d) holds first after t, is t1, and the first point of 	*)
	    (* time before t1 where d held is delta. Therefore, we consider the cases:	*)
	    (* ------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<=t)\/(t<delta)`--)))
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* delta<=t holds, so we take the first disjunct, i.e. we must prove 	*)
		(* (c PSUNTIL d) /\ c /\ (a /\ NEXT c) SUNTIL b				*)
		(* --------------------------------------------------------------------	*)
		DISJ1_TAC THEN REPEAT STRIP_TAC
		THENL[
		    (* --------- prove that (c PSUNTIL d) t holds ---------------------	*)
		    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
		    THEN GEN_TAC THEN DISCH_TAC
		    THEN POP_NO_ASSUM 3 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
		    THEN UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 5 THEN CONV_TAC ARITH_CONV,
		    (* ------- prove that ((a /\ NEXT c) SUNTIL b) holds --------------	*)
		    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		    THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
		    THEN LEFT_NO_FORALL_TAC 10 (--`SUC(t2)`--) THEN UNDISCH_HD_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t2<t1)==>(SUC(t2)<=t1)`--)))
		    THEN IMP_RES_TAC LESS_EQ_TRANS
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(delta<SUC t2) = (delta<=t2)`--))]
		    THEN STRIP_TAC
		    ],
		(* --------------------------------------------------------------------	*)
		(* t<delta holds, so we take the second disjunct to prove that		*)
		(* [a SUNTIL (d /\ ((a /\ NEXT c) SUNTIL b))]				*)
		(* --------------------------------------------------------------------	*)
		DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<y)==>(x<=y)`--)))
		THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
		THENL[
		    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQ_TRANS
		    THEN RES_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=y)==>(x<SUC y)`--)))
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<y)==>(SUC x<= y)`--)))
		    THEN RES_TAC,
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<y)/\(y<=z)==>(x<z)`--)))
		    THEN RES_TAC
		    ]
	    ],
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC
	    THEN MAP_EVERY POP_NO_TAC [3,2,1,0]
	    THEN DISJ_CASES_TAC(REWRITE_RULE[]
				(SPEC(--`?t2. t<=t2 /\ t2<=t1 /\ d t2`--)BOOL_CASES_AX))
	    THENL[
		(* --------  ?t2. t <= t2 /\ t2 <= t1 /\ d t2 -----------------	*)
		ASSUME_TAC(Q.INST [`phi` |-> `d:num->bool`,
                                   `t2` |-> `t1:num`,
                                   `t1` |-> `t:num`] MAX_EXISTS)
		THEN UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
		THEN ASM_TAC 2 REWRITE1_TAC THEN STRIP_TAC
		THEN EXISTS_TAC(--`xmax:num`--) THEN ASM_REWRITE_TAC[]
		THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
		THEN MAP_EVERY POP_NO_TAC [7,6,5,4,3,2,1,0]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`t<=xmax /\ xmax<t' ==> t<t'`--)))
		THEN MAP_EVERY POP_NO_TAC [4,3,1,0]
		THEN IMP_RES_TAC LESS_ADD_1 THEN POP_NO_TAC 0
		THEN LEFT_NO_FORALL_TAC 9 (--`p+t`--) THEN UNDISCH_HD_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
					(--`(t'=t+(p+1))/\(t'<=t1) ==> (p+t<t1)`--)))
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t<=p+t`--))]
		THEN REWRITE_TAC[ONE,ADD_CLAUSES]
		THEN DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[],
		(* --------  ~(?t2. t <= t2 /\ t2 <= t1 /\ d t2) --------------	*)
		EXISTS_TAC(--`delta:num`--)
		THEN IMP_RES_TAC LESS_EQ_TRANS THEN ASM_REWRITE_TAC[]
		THEN UNDISCH_NO_TAC 3 THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
		THEN REWRITE_TAC[TAC_PROOF(
			([],--`~(a/\b/\c) = (a/\b==>~c)`--),PROP_TAC)]
		THEN DISCH_TAC
		THEN GEN_TAC THEN STRIP_TAC
	        THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t'<=t)\/(t<t')`--)))
		THENL[ RES_TAC THEN ASM_REWRITE_TAC[],ALL_TAC]
		THEN LEFT_NO_FORALL_TAC 3 (--`t':num`--) THEN UNDISCH_HD_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<t')==>(t<=t')`--)))
		THEN ASM_REWRITE_TAC[]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN IMP_RES_TAC LESS_ADD_1
		THEN LEFT_NO_FORALL_TAC 11 (--`t+p`--) THEN UNDISCH_HD_TAC
		THEN ASM_TAC 1 SUBST1_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(t'=t+(p+1))/\(t'<=t1) ==> (t+p<t1)`--)))
		THEN ASM_REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,
			EQT_ELIM(ARITH_CONV(--`t<=t+p`--))]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		],
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`t1':num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC
	    THENL[
		IMP_RES_TAC LESS_EQ_TRANS,
		ALL_TAC,
		LEFT_NO_FORALL_TAC 3 (--`t2:num`--) THEN UNDISCH_HD_TAC
 		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		THEN LEFT_NO_FORALL_TAC 3 (--`t2:num`--) THEN UNDISCH_HD_TAC
 		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t1<=t2)\/(t2<t1)`--)))
		THEN RES_TAC
		]
	    THEN MY_MP_TAC(--`?t2. t <= t2 /\ t2 <= t1' /\ d t2`--)
	    THENL[
		EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
		DISCH_TAC]
	    THEN ASSUME_TAC(Q.INST [`phi` |-> `d:num->bool`,
                                    `t1` |-> `t:num`,
                                    `t2` |-> `t1':num`] MAX_EXISTS)
	    THEN UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
	    THEN IMP_RES_TAC LESS_EQ_TRANS
	    THEN ASM_TAC 1 REWRITE1_TAC THEN STRIP_TAC
	    THEN EXISTS_TAC(--`xmax:num`--) THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
	    THEN MAP_EVERY POP_NO_TAC [7,6,5,4,3,2,1,0]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN LEFT_NO_FORALL_TAC 12 (--`xmax+p`--) THEN UNDISCH_HD_TAC
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t'=xmax+(p+1))/\(t'<=t1') ==> (xmax+p<t1')`--)))
	    THEN ASM_REWRITE_TAC[] THEN MAP_EVERY POP_NO_TAC [4,3,2,1,0]
	    THEN LEFT_NO_FORALL_TAC 5 (--`t1:num`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(x<y) = (y<=x)`--))]
	    THEN DISCH_TAC THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t1<=xmax) ==> (t1<=xmax+p)`--)))
	    THEN ASM_REWRITE_TAC[ONE,ADD_CLAUSES]
	    THEN STRIP_TAC
	    ]);





val SUNTIL_AND_PBEFORE_SEPARATE = TAC_PROOF(
	([], --`(a SUNTIL (\t. b t /\ (c PBEFORE d) t))
		=
		\t. (c PBEFORE d) t /\ ((\t. a t /\ ~NEXT d t) SUNTIL b) t \/
		    (a SUNTIL (\t. c t /\ ~d t /\
			          ((\t. a t /\ ~NEXT d t) SUNTIL b) t)) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[SUNTIL_LINORD,UPTO,PBEFORE,NEXT]
	THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    (* First, we have to show that the lhs implies the rhs, when b becomes true	*)
	    (* at time t1>=t, and d is false for all t'<= t1. We choose the first 	*)
	    (* disjunct, i.e., (c PBEFORE d) /\ ((a /\ ~NEXT c /\ ~NEXT d) SUNTIL b) to *)
	    (* prove this.								*)
	    (* ------------------------------------------------------------------------	*)
	    DISJ1_TAC THEN REPEAT STRIP_TAC
	    THENL[
		DISJ1_TAC THEN GEN_TAC THEN DISCH_TAC
		THEN IMP_RES_TAC LESS_EQ_TRANS THEN RES_TAC,
		EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		THEN GEN_TAC THEN STRIP_TAC
		THEN RES_TAC THEN ASM_REWRITE_TAC[]
		THEN POP_NO_ASSUM 6 MATCH_MP_TAC THEN UNDISCH_NO_TAC 3
		THEN CONV_TAC ARITH_CONV
		],
	    (* ------------------------------------------------------------------------	*)
	    (* Second, we have to show that the lhs implies the rhs, when b becomes 	*)
	    (* true at time t1>=t, c holds at delta<=t1, and d is false for all points	*)
	    (* of time t' with delta<=t' /\ t'<=t1. Moreover, we know that a holds for	*)
	    (*  t' with t<=t' /\ t'<t1. We must consider two cases here, depending on 	*)
	    (* (delta<=t)\/(t<delta).							*)
	    (* ------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<=t)\/(t<delta)`--)))
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* delta<=t holds, so we take the first disjunct, i.e. we must prove 	*)
		(* (c PBEFORE d) /\ ((a /\ ~NEXT d) SUNTIL b)				*)
		(* --------------------------------------------------------------------	*)
		DISJ1_TAC THEN REPEAT STRIP_TAC
		THENL[
		    (* --------- prove that (c PBEFORE d) t holds ---------------------	*)
		    DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
		    THEN GEN_TAC THEN DISCH_TAC
		    THEN POP_NO_ASSUM 3 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
		    THEN UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 5 THEN CONV_TAC ARITH_CONV,
		    (* ------- prove that ((a /\ ~NEXT d) SUNTIL b) -------------------	*)
		    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		    THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
		    THEN LEFT_NO_FORALL_TAC 9 (--`SUC(t2)`--) THEN UNDISCH_HD_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t2<t1)==>(SUC(t2)<=t1)`--)))
		    THEN IMP_RES_TAC LESS_EQ_TRANS
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(delta<=t2)==>(delta <= SUC t2)`--)))
		    THEN ASM_REWRITE_TAC[]
		    ],
		(* --------------------------------------------------------------------	*)
		(* t<delta holds, so we take the second disjunct to prove that		*)
		(* [a SUNTIL (c /\ ~d /\ ((a /\ ~NEXT d) SUNTIL b)))]			*)
		(* --------------------------------------------------------------------	*)
		DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--)
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<y)==>(x<=y)`--)))
		THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
		THENL[
		    UNDISCH_HD_TAC THEN REWRITE_TAC[]
		    THEN POP_NO_ASSUM 3 MATCH_MP_TAC
		    THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
		    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		    THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC
		    THENL[
			POP_NO_ASSUM 4 MATCH_MP_TAC THEN IMP_RES_TAC LESS_EQ_TRANS
			THEN ASM_REWRITE_TAC[],
			POP_NO_ASSUM 5 MATCH_MP_TAC
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<=y)==>(x<=SUC y)`--)))
		        THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x<y)==>(SUC x<= y)`--)))
			THEN ASM_REWRITE_TAC[]
		    ],
		    POP_NO_ASSUM 4 MATCH_MP_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t2<d)/\(d<=t1)==>(t2<t1)`--)))
		    THEN ASM_REWRITE_TAC[]
		]
	    ],
	    (* ------------------------------------------------------------------------	*)
	    (* Third, we have to show that the rhs implies the lhs, more concrete that	*)
	    (* the first disjunct implies the lhs. We first have the special case that	*)
	    (* c never holds up to the point when b holds first. This means that b is	*)
	    (* true at time t1>=t, d is false for all t<=t, and a/\~NEXT d holds for 	*)
	    (* t' with t<=t' /\ t'<t1. 							*)
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC (* proves the validity of a up to t1 *)
	    THEN MAP_EVERY POP_NO_TAC [1,0]
	    THEN DISJ1_TAC THEN GEN_TAC THEN DISCH_TAC
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t<t')\/(t'<=t)`--)))
	    THENL[
		IMP_RES_TAC LESS_ADD_1 THEN LEFT_NO_FORALL_TAC 3 (--`t+p`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ONE,ADD_CLAUSES]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
					(--`(t'=t+(p+1))/\(t'<=t1) ==> (t+p<t1)`--)))
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t<=t+p`--))]
		THEN STRIP_TAC,
		RES_TAC],
	    (* ------------------------------------------------------------------------	*)
	    (* Fourth, we have to show that the rhs implies the lhs, more concrete that	*)
	    (* the first disjunct implies the lhs. We first have the special case that	*)
	    (* c holds at delta<=t, b holds at time t1, d is false for all t' with 	*)
	    (* delta<=t' /\ t'<=t, and a/\~NEXT d holds for t' with t<=t' /\ t'<t1. 	*)
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC (* proves the validity of a up to t1 *)
	    THEN MAP_EVERY POP_NO_TAC [3,2,1,0]
	    THEN DISJ2_TAC THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC LESS_EQ_TRANS THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t<t')\/(t'<=t)`--)))
	    THENL[
		IMP_RES_TAC LESS_ADD_1 THEN LEFT_NO_FORALL_TAC 7 (--`t+p`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ONE,ADD_CLAUSES]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
					(--`(t'=t+(p+1))/\(t'<=t1) ==> (t+p<t1)`--)))
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t<=t+p`--))]
		THEN STRIP_TAC,
		RES_TAC],
	    (* ------------------------------------------------------------------------	*)
	    (* Fifth, we have to show that the rhs implies the lhs, more concrete that	*)
	    (* the second disjunct implies the lhs. This means that we have the 	*)
	    (* following assumptions:							*)
	    (*	      (--`t <= t1`--)							*)
	    (*	      (--`c t1`--)							*)
	    (*	      (--`~(d t1)`--)							*)
	    (*	      (--`t1 <= t1'`--)							*)
	    (*	      (--`b t1'`--)							*)
	    (*	      (--`!t2. t1 <= t2 /\ t2 < t1' ==> a t2 /\ ~(d (SUC t2))`--)	*)
 	    (*	      (--`!t2. t <= t2 /\ t2 < t1 ==> a t2`--)				*)
	    (*										*)
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC(--`t1':num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC
	    THENL[
		IMP_RES_TAC LESS_EQ_TRANS,
		ALL_TAC,
		LEFT_NO_FORALL_TAC 3 (--`t2:num`--) THEN UNDISCH_HD_TAC
 		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		THEN LEFT_NO_FORALL_TAC 3 (--`t2:num`--) THEN UNDISCH_HD_TAC
 		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t1<=t2)\/(t2<t1)`--)))
		THEN RES_TAC
		]
	    THEN DISJ2_TAC
	    THEN EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_OR_EQ]
	    THEN STRIP_TAC
	    THENL[
	 	IMP_RES_TAC LESS_ADD_1
		THEN LEFT_NO_FORALL_TAC 4 (--`t1+p`--) THEN UNDISCH_HD_TAC
	    	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t'=t1+(p+1))/\(t'<=t1') ==> (t1+p<t1')`--)))
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1<=t1+p`--))]
		THEN REWRITE_TAC[ONE,ADD_CLAUSES]
		THEN STRIP_TAC,
	    	POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]
		]
	    ]);







val BEFORE_AND_PSUNTIL_SEPARATE = TAC_PROOF(
	([], --`((\t. a t /\ (b PSUNTIL c) t) BEFORE d)
		=
		\t. (b PSUNTIL c) t /\ ((\t. ~d t /\ NEXT b t) SUNTIL (\t. a t /\~d t)) t \/
		    ((\t. c t /\ ((\t. ~d t /\ NEXT b t) SUNTIL (\t. a t /\ ~d t)) t) BEFORE d) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[BEFORE_AS_UNTIL1] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a/\b)/\~d = (a/\~d)/\b`--),PROP_TAC)]
	THEN REWRITE_TAC[UNTIL_AS_SUNTIL] THEN BETA_TAC
	THEN ASSUME_TAC(BETA_RULE
		 	(SPECL[(--`c:num->bool`--),
			       (--`b:num->bool`--),(--`\t:num. a t /\ ~d t`--),
			       (--`\t:num. ~d t`--)]
			     (GEN_ALL SUNTIL_AND_PSUNTIL_SEPARATE)))
	THEN POP_ASSUM SUBST1_TAC THEN BETA_TAC
	THEN REWRITE_TAC[NOT_EVENTUAL]
	THEN MATCH_MP_TAC(TAC_PROOF(([],--`!a b1 b2 c. (b1=b2)==> ((a\/b1)\/c=a\/b2\/c)`--),
				    REPEAT GEN_TAC THEN PROP_TAC))
	THEN MY_MP_TAC (--`!a1 a2 b1 b2.
				(a1=a2) /\(b1=b2) ==> ((a1 SUNTIL b1) t = (a2 SUNTIL b2) t)`--)
	THENL[
	    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[],
	    DISCH_TAC]
	THEN POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]
	THEN REWRITE_TAC[SUNTIL_SIGNAL,UPTO] THEN BETA_TAC
	THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL[
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0) \/ (0<delta)`--)))
	    THENL[
		UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		LEFT_NO_FORALL_TAC 4 (--`0`--) THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		],
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    ]);







val BEFORE_AND_PBEFORE_SEPARATE = TAC_PROOF(
	([], --`((\t. a t /\ (b PBEFORE c) t) BEFORE d)
		=
		\t. (b PBEFORE c) t /\ ((\t. ~d t /\ ~NEXT c t) SUNTIL (\t. a t /\~d t)) t \/
		    ((\t. b t /\ ~c t /\
			 ((\t. ~d t /\ ~NEXT c t) SUNTIL (\t. a t /\ ~d t)) t) BEFORE d) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[BEFORE_AS_UNTIL1] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a/\b)/\~d = (a/\~d)/\b`--),PROP_TAC)]
	THEN REWRITE_TAC[UNTIL_AS_SUNTIL] THEN BETA_TAC
	THEN ASSUME_TAC(BETA_RULE
		 	(SPECL[(--`c:num->bool`--),
			       (--`b:num->bool`--),(--`\t:num. a t /\ ~d t`--),
			       (--`\t:num. ~d t`--)]
			     (GEN_ALL SUNTIL_AND_PBEFORE_SEPARATE)))
	THEN POP_ASSUM SUBST1_TAC THEN BETA_TAC
	THEN MATCH_MP_TAC(TAC_PROOF(([],--`!a b1 b2 c. (b1=b2)==> ((a\/b1)\/c=a\/b2\/c)`--),
				    REPEAT GEN_TAC THEN PROP_TAC))
	THEN MY_MP_TAC (--`!a1 a2 b1 b2.
				(a1=a2) /\(b1=b2) ==> ((a1 SUNTIL b1) t = (a2 SUNTIL b2) t)`--)
	THENL[
	    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[],
	    DISCH_TAC]
	THEN POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]
	THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[SUNTIL_REC]
	THEN BETA_TAC THEN ASM_REWRITE_TAC[]);










val SUNTIL_OR_PSUNTIL_SEPARATE = TAC_PROOF(
	([], --`((\t. a t \/ (b PSUNTIL c) t) SUNTIL d)
		=
		 \t. ((b PSUNTIL c) t  \/  ((\t. d t \/ NEXT c t) BEFORE (\t. ~a t /\ ~d t)) t )
		     /\
	             ((\t. b t \/ c t \/ ((\t. d t \/ NEXT c t) BEFORE (\t. ~a t /\ ~d t)) t) SUNTIL d) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NOT_SUNTIL] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM]
	THEN ASSUME_TAC(BETA_RULE
		 	(SPECL[(--`d:num->bool`--),
			       (--`c:num->bool`--),(--`\t:num. ~b t`--),
			       (--`\t:num. ~a t`--)]
			     (GEN_ALL BEFORE_AND_PBEFORE_SEPARATE)))
	THEN POP_ASSUM SUBST1_TAC THEN BETA_TAC
	THEN REWRITE_TAC[NOT_BEFORE,NOT_SUNTIL] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NOT_BEFORE] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM]);



val SUNTIL_OR_PBEFORE_SEPARATE = TAC_PROOF(
	([], --`((\t. a t \/ (b PBEFORE c) t) SUNTIL d)
		=
		 \t. ((b PBEFORE c) t  \/  ((\t. d t \/ NEXT b t) BEFORE (\t. ~a t /\ ~d t)) t )
		     /\
	             ((\t. ~c t \/ ((\t. d t \/ NEXT b t) BEFORE (\t. ~a t /\ ~d t)) t) SUNTIL d) t
	`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NOT_SUNTIL,DE_MORGAN_THM] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM]
	THEN ASSUME_TAC(BETA_RULE
		 	(SPECL[(--`d:num->bool`--),
			       (--`c:num->bool`--),(--`\t:num. ~b t`--),
			       (--`\t:num. ~a t`--)]
			     (GEN_ALL BEFORE_AND_PSUNTIL_SEPARATE)))
	THEN POP_ASSUM SUBST1_TAC THEN BETA_TAC
	THEN REWRITE_TAC[NOT_BEFORE,NOT_SUNTIL] THEN BETA_TAC
	THEN REWRITE_TAC[NOT_BEFORE,DE_MORGAN_THM,NOT_NEXT] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM]);



val BEFORE_OR_LEFT_SEPARATE = TAC_PROOF(
	([],--`((\t. a t \/ b t) BEFORE c) = \t. (a BEFORE c) t \/ (b BEFORE c) t`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NOT_BEFORE,DE_MORGAN_THM] THEN BETA_TAC
	THEN ASSUME_TAC(BETA_RULE
		 	(SPECL[(--`c:num->bool`--),(--`\t:num. ~b t`--),(--`\t:num. ~a t`--)]
			(GEN_ALL SUNTIL_AND_SEPARATE)))
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN POP_ASSUM SUBST1_TAC THEN BETA_TAC THEN REWRITE_TAC[]);



val BEFORE_OR_SEPARATE = TAC_PROOF(
	([],--`(((\t. a t \/ b t) BEFORE c) = \t. (a BEFORE c) t \/ (b BEFORE c) t)
	    /\ ((c BEFORE (\t. a t \/ b t)) = \t. (c BEFORE a) t /\ (c BEFORE b) t)`--),
	REWRITE_TAC[BEFORE_OR_RIGHT_SEPARATE,BEFORE_OR_LEFT_SEPARATE]);



val BEFORE_LEFT_PNEXT_SEPARATE = TAC_PROOF(
	([],--`((\t. a t /\ PNEXT b t) BEFORE c)
		=
		\t. ~c t /\ a t /\ PNEXT b t
		    \/
		    ~c t /\ ((\t. b t /\ NEXT a t) BEFORE NEXT c) t
		`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\(b\/c) = (a/\b)\/(a/\c)`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c\/a) = (c\/b)) `--),PROP_TAC))
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c/\a) = (c/\b)) `--),PROP_TAC))
	THEN REWRITE_TAC[BEFORE_NEXT]
	THEN REWRITE_TAC[BEFORE, NEXT_AND_PNEXT_SEPARATE]
	THEN BETA_TAC THEN REWRITE_TAC[]
	);


val BEFORE_LEFT_PSNEXT_SEPARATE = TAC_PROOF(
	([],--`((\t. a t /\ PSNEXT b t) BEFORE c)
		=
		\t. ~c t /\ a t /\ PSNEXT b t
		    \/
		    ~c t /\ ((\t. b t /\ NEXT a t) BEFORE NEXT c) t
		`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\(b\/c) = (a/\b)\/(a/\c)`--),PROP_TAC)]
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c\/a) = (c\/b)) `--),PROP_TAC))
	THEN MATCH_MP_TAC(TAC_PROOF(
			([],--` (a=b) ==> ((c/\a) = (c/\b)) `--),PROP_TAC))
	THEN REWRITE_TAC[BEFORE_NEXT]
	THEN REWRITE_TAC[BEFORE, NEXT_AND_PSNEXT_SEPARATE]
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



val BEFORE_LEFT_PBEFORE_SEPARATE = BEFORE_AND_PBEFORE_SEPARATE;

val BEFORE_LEFT_PSUNTIL_SEPARATE = BEFORE_AND_PSUNTIL_SEPARATE;


val BEFORE_RIGHT_PNEXT_SEPARATE = TAC_PROOF(
	([],--`(a BEFORE (\t. b t /\ PNEXT c t))
		= \t.
		     ~(b t /\ PNEXT c t)
		     /\
		     ( a t \/ ((NEXT a) BEFORE (\t. c t /\ NEXT b t)) t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	THEN BETA_TAC THEN REWRITE_TAC[BEFORE_NEXT,SYM NEXT_AND_PNEXT_SEPARATE]);


val BEFORE_RIGHT_PSNEXT_SEPARATE = TAC_PROOF(
	([],--`(a BEFORE (\t. b t /\ PSNEXT c t))
		= \t.
		     ~(b t /\ PSNEXT c t)
		     /\
		     ( a t \/ ((NEXT a) BEFORE (\t. c t /\ NEXT b t)) t)`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t:num`--)) THEN GEN_TAC THEN BETA_TAC
	THEN CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	THEN BETA_TAC THEN REWRITE_TAC[BEFORE_NEXT,SYM NEXT_AND_PSNEXT_SEPARATE]);


val UNTIL_AND_SEPARATE = TAC_PROOF(
	([], --`((\t. a t /\ b t) UNTIL c) =
		  \t. (a UNTIL c) t /\ (b UNTIL c) t`--),
	CONV_TAC(X_FUN_EQ_CONV (--`t0:num`--)) THEN GEN_TAC
	THEN REWRITE_TAC[UNTIL_SIGNAL] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN RES_TAC THEN ASM_REWRITE_TAC[]);





val SEPARATE_NEXT_THM = TAC_PROOF(
	([], --`
	    ((NEXT (\t. a t /\ PNEXT b t)) = (\t. b t /\ NEXT a t)
	    ) /\
	    ((NEXT (\t. a t /\ PSNEXT b t)) = (\t. b t /\ NEXT a t)
	    ) /\
	    ((NEXT (\t. a t /\ (b PSUNTIL c) t)) =
		\t. NEXT(\t. a t /\ c t) t \/
		    (b PSUNTIL c) t /\ NEXT(\t. a t /\ b t) t
	    ) /\
	    ((NEXT (\t. a t /\ (b PBEFORE c) t)) =
		\t. NEXT(\t. a t /\ b t /\ ~c t) t \/
		    (b PBEFORE c) t /\ NEXT(\t. a t /\ ~c t) t
	    ) /\
	    ((NEXT (\t. a t \/ PNEXT b t)) =
		(\t. b t \/ NEXT a t)
	    ) /\
	    ((NEXT (\t. a t \/ PSNEXT b t)) =
		(\t. b t \/ NEXT a t)
	    ) /\
	    ((NEXT (\t. a t \/ (b PSUNTIL c) t)) =
		\t. NEXT(\t. a t \/ c t) t \/
		    (b PSUNTIL c) t /\ NEXT b t
	    ) /\
	    ((NEXT (\t. a t \/ (b PBEFORE c) t)) =
		\t. NEXT(\t. a t \/ ~c t) t /\
		    ((b PBEFORE c) t \/ NEXT (\t. a t \/ b t) t)
	    )
	`--),
	REWRITE_TAC[
		NEXT_AND_PNEXT_SEPARATE,
		NEXT_AND_PSNEXT_SEPARATE,
		NEXT_AND_PSUNTIL_SEPARATE,
		NEXT_AND_PBEFORE_SEPARATE,
		NEXT_OR_PNEXT_SEPARATE,
		NEXT_OR_PSNEXT_SEPARATE,
		NEXT_OR_PSUNTIL_SEPARATE,
		NEXT_OR_PBEFORE_SEPARATE]);



val SEPARATE_SUNTIL_THM = TAC_PROOF(
	([], --`
	    ( (a SUNTIL (\t. b t \/ c t)) =
		\t. (a SUNTIL b) t \/ (a SUNTIL c) t ) /\
	    ( (a SUNTIL (\t. b t /\ PNEXT c t))	=
		\t. (b t /\ PNEXT c t)
		    \/
		    (a SUNTIL (\t. a t /\ c t /\ NEXT b t)) t ) /\
	    ( (a SUNTIL (\t. b t /\ PSNEXT c t)) =
		\t. (b t /\ PSNEXT c t)
		    \/
		    (a SUNTIL (\t. a t /\ c t /\ NEXT b t)) t ) /\
	    ( (a SUNTIL (\t. b t /\ (c PSUNTIL d) t)) =
		\t. (c PSUNTIL d) t /\ ((\t. a t /\ NEXT c t) SUNTIL b) t \/
		    (a SUNTIL (\t. d t /\ ((\t. a t /\ NEXT c t) SUNTIL b) t)) t ) /\
	    ( (a SUNTIL (\t. b t /\ (c PBEFORE d) t)) =
		\t. (c PBEFORE d) t /\ ((\t. a t /\ ~NEXT d t) SUNTIL b) t \/
		    (a SUNTIL (\t. c t /\ ~d t /\
			          ((\t. a t /\ ~NEXT d t) SUNTIL b) t)) t ) /\
	    ( ((\t. a t /\ b t) SUNTIL c) = \t. (a SUNTIL c) t /\ (b SUNTIL c) t ) /\
	    ( ((\t. a t \/ PNEXT b t) SUNTIL c)	=
		\t. (c t) \/
		    (a t \/ PNEXT b t) /\ ((\t. b t \/ NEXT a t ) SUNTIL (NEXT c)) t ) /\
	    ( ((\t. a t \/ PSNEXT b t) SUNTIL c) =
		\t. (c t) \/
		    (a t \/ PSNEXT b t) /\ ((\t. b t \/ NEXT a t ) SUNTIL (NEXT c)) t ) /\
	    ( ((\t. a t \/ (b PSUNTIL c) t) SUNTIL d)
		=  \t. ((b PSUNTIL c) t  \/  ((\t. d t \/ NEXT c t) BEFORE (\t. ~a t /\ ~d t)) t )
		       /\
	               ((\t. b t \/ c t \/ ((\t. d t \/ NEXT c t) BEFORE (\t. ~a t /\ ~d t)) t)
			SUNTIL d) t
	    ) /\
	    ( ((\t. a t \/ (b PBEFORE c) t) SUNTIL d)
		= \t. ((b PBEFORE c) t  \/  ((\t. d t \/ NEXT b t) BEFORE (\t. ~a t /\ ~d t)) t )
		      /\
	              ((\t. ~c t \/ ((\t. d t \/ NEXT b t) BEFORE (\t. ~a t /\ ~d t)) t) SUNTIL d) t
	    )
	`--),
	REWRITE_TAC[
		SUNTIL_AND_SEPARATE,
		SUNTIL_AND_PNEXT_SEPARATE,
		SUNTIL_AND_PSNEXT_SEPARATE,
		SUNTIL_OR_PNEXT_SEPARATE,
		SUNTIL_OR_PSNEXT_SEPARATE,
		SUNTIL_OR_SEPARATE,
		SUNTIL_AND_PSUNTIL_SEPARATE,
		SUNTIL_AND_PBEFORE_SEPARATE,
		SUNTIL_OR_PSUNTIL_SEPARATE,
		SUNTIL_OR_PBEFORE_SEPARATE]);




val SEPARATE_BEFORE_THM = TAC_PROOF(
	([], --`
	    ( (a BEFORE (\t. b t \/ c t)) = \t. (a BEFORE b) t /\ (a BEFORE c) t ) /\
	    ( ((\t. a t \/ b t) BEFORE c) = \t. (a BEFORE c) t \/ (b BEFORE c) t ) /\
	    ( (a BEFORE (\t. b t /\ PNEXT c t))	=
		  \t.
		     ~(b t /\ PNEXT c t)
		     /\
		     ( a t \/ ((NEXT a) BEFORE (\t. c t /\ NEXT b t)) t) ) /\
	    ( (a BEFORE (\t. b t /\ PSNEXT c t)) =
		  \t.
		     ~(b t /\ PSNEXT c t)
		     /\
		     ( a t \/ ((NEXT a) BEFORE (\t. c t /\ NEXT b t)) t) ) /\
	    ( (a BEFORE (\t. b t /\ (c PSUNTIL d) t)) =
		\t. ( ((\t.~c t) PBEFORE d) t \/ ((\t. a t \/ ~NEXT c t) BEFORE b) t) /\
		    (a BEFORE (\t. d t /\ ((\t. ~a t /\ NEXT c t) SUNTIL b) t)) t ) /\
	    ( (a BEFORE (\t. b t /\ (c PBEFORE d) t)) =
		\t. (((\t.~c t) PSUNTIL d) t \/ ((\t. a t \/ NEXT d t) BEFORE b) t) /\
		    (a BEFORE (\t. c t /\ ~d t /\
			          ((\t. ~a t /\ ~NEXT d t) SUNTIL b) t)) t ) /\
	    ( ((\t. a t /\ PNEXT b t) BEFORE c)	=
		\t. ~c t /\ a t /\ PNEXT b t \/
		    ~c t /\ ((\t. b t /\ NEXT a t ) BEFORE (NEXT c)) t ) /\
	    ( ((\t. a t /\ PSNEXT b t) BEFORE c) =
		\t. ~c t /\ a t /\ PSNEXT b t \/
		    ~c t /\ ((\t. b t /\ NEXT a t ) BEFORE (NEXT c)) t ) /\
	    ( ((\t. a t /\ (b PBEFORE c) t) BEFORE d)
		=
		\t. (b PBEFORE c) t /\ ((\t. ~d t /\ ~NEXT c t) SUNTIL (\t. a t /\ ~d t)) t \/
		    ((\t. b t /\ ~c t /\ ((\t. ~d t /\ ~NEXT c t) SUNTIL (\t. a t /\ ~d t)) t)
		    BEFORE d) t ) /\
	    ( ((\t. a t /\ (b PSUNTIL c) t) BEFORE d)
		=
		\t. (b PSUNTIL c) t /\ ((\t. ~d t /\ NEXT b t) SUNTIL (\t. a t /\ ~d t)) t \/
		    ((\t. c t /\ ((\t. ~d t /\ NEXT b t) SUNTIL (\t. a t /\ ~d t)) t) BEFORE d) t )
	`--),
	REWRITE_TAC[
	    	BEFORE_AND_PSUNTIL_SEPARATE, BEFORE_AND_PBEFORE_SEPARATE,
		BEFORE_OR_LEFT_SEPARATE,BEFORE_OR_SEPARATE,
		BEFORE_LEFT_PNEXT_SEPARATE,BEFORE_LEFT_PSNEXT_SEPARATE,
		BEFORE_RIGHT_PNEXT_SEPARATE,BEFORE_RIGHT_PSNEXT_SEPARATE
		]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM,DE_MORGAN_THM,
			 CONJUNCTIVE_NORMAL_FORM,SEPARATE_SUNTIL_THM]
	THEN BETA_TAC THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN REWRITE1_TAC
		(BETA_RULE
		    (SPECL[(--`b:num->bool`--),(--`NEXT c`--),(--`\t:num. ~(a t)`--)]
			  (GEN_ALL(elem 5 (CONJUNCTS CONJUNCTIVE_NORMAL_FORM))) ))
	THEN REWRITE1_TAC
		(BETA_RULE
		    (SPECL[(--`b:num->bool`--),(--`NEXT c`--),(--`\t:num. ~(a t)`--)]
			  (GEN_ALL(elem 5 (CONJUNCTS CONJUNCTIVE_NORMAL_FORM))) ))
	THEN BETA_TAC THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN BETA_TAC THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE1_TAC
		(BETA_RULE
		    (SPECL[(--`b:num->bool`--),(--`NEXT c`--),(--`\t:num. ~(a t)`--)]
			  (GEN_ALL(elem 5 (CONJUNCTS CONJUNCTIVE_NORMAL_FORM))) ))
	THEN BETA_TAC THEN REWRITE_TAC[]
	);



(*---------------------------------------------------------------------------
     More separation theorems (this time for the past).
 ---------------------------------------------------------------------------*)

val SEPARATE_PNEXT_THM = TAC_PROOF(
	([], --`
	    ((PNEXT (\t. a t /\ NEXT b t)) = (\t. InitPoint t \/ b t /\ PNEXT a t)
	    ) /\
	    ((PNEXT (\t. a t /\ (b SUNTIL c) t)) =
		\t. PNEXT(\t. a t /\ c t) t \/
		    (b SUNTIL c) t /\ PNEXT(\t. a t /\ b t) t
	    ) /\
	    ((PNEXT (\t. a t /\ (b BEFORE c) t)) =
		\t. PNEXT(\t. a t /\ b t /\ ~c t) t \/
		    (b BEFORE c) t /\ PNEXT(\t. a t /\ ~c t) t
	    ) /\
	    ((PNEXT (\t. a t \/ NEXT b t)) =
		(\t. b t \/ PNEXT a t)
	    ) /\
	    ((PNEXT (\t. a t \/ (b SUNTIL c) t)) =
		\t. PNEXT(\t. a t \/ c t) t \/
		    (b SUNTIL c) t /\ PNEXT b t
	    ) /\
	    ((PNEXT (\t. a t \/ (b BEFORE c) t)) =
		\t. PNEXT(\t. a t \/ ~c t) t /\
		    ((b BEFORE c) t \/ PNEXT (\t. a t \/ b t) t)
	    )
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN REPEAT CONJ_TAC
	THEN REWRITE_TAC[PNEXT,InitPoint,NEXT] THEN BETA_TAC
	THEN INDUCT_TAC THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--)),PRE]
	THENL[
	    PROP_TAC,
	    CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN PROP_TAC,
	    CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN PROP_TAC,
	    PROP_TAC,
	    CONV_TAC(LHS_CONV(REWRITE_CONV[SUNTIL_REC]))
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN PROP_TAC,
	    CONV_TAC(LHS_CONV(REWRITE_CONV[BEFORE_REC]))
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN PROP_TAC
	]);



val SEPARATE_PSUNTIL_OR_THM = TAC_PROOF(
	([],--`
     	(a PSUNTIL (\t. b t \/ c t) = (\t. (a PSUNTIL b) t \/ (a PSUNTIL c) t))
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THEN REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	THENL[
	    PROP_TAC,
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN REWRITE_TAC[PSNEXT,PRE,ZERO_LEMMA]
	    THEN ASM_REWRITE_TAC[] THEN PROP_TAC
	]);


val SEPARATE_PSUNTIL_AND_THM = TAC_PROOF(
	([],--`
     	((\t. a t /\ b t) PSUNTIL c = (\t. (a PSUNTIL c) t /\ (b PSUNTIL c) t))
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THEN REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	THEN REWRITE_TAC[PSNEXT,PRE,ZERO_LEMMA]
	THEN ASM_REWRITE_TAC[] THEN PROP_TAC);



val SEPARATE_PSUNTIL_OR_NEXT_THM = TAC_PROOF(
	([],--`
     	((\t. a t \/ NEXT b t) PSUNTIL c =
      	   (\t.
        	c t \/
        	(a t \/ NEXT b t) /\ ((\t. b t \/ PNEXT a t) PSUNTIL PSNEXT c) t))
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA],
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN REWRITE_TAC[PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[PNEXT,PRE,ZERO_LEMMA,NEXT]
	    THEN BETA_TAC THEN PROP_TAC
	]);


val SEPARATE_PSUNTIL_AND_NEXT_THM = TAC_PROOF(
	([],--`
     	(a PSUNTIL (\t. b t /\ NEXT c t) =
      	   (\t.
        	b t /\ NEXT c t \/
        	(a PSUNTIL (\t. a t /\ c t /\ PSNEXT b t)) t))
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA],
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN REWRITE_TAC[PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[PSNEXT,PRE,ZERO_LEMMA,NEXT]
	    THEN BETA_TAC THEN PROP_TAC
	]);









val PSUNTIL_AND_SUNTIL_SEPARATE = TAC_PROOF(
	([], --`(a PSUNTIL (\t. b t /\ (c SUNTIL d) t))
		=
		\t. (c SUNTIL d) t /\ ((\t. a t /\ PNEXT c t) PSUNTIL b) t \/
		    (a PSUNTIL (\t. d t /\ ((\t. a t /\ PNEXT c t) PSUNTIL b) t)) t
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION,SUNTIL_REC] THEN PROP_TAC,
	    ALL_TAC]
	THEN ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN POP_ASSUM SUBST1_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT]
	    THEN DISJ_CASES_TAC(SPEC(--`(d:num->bool) n`--)BOOL_CASES_AX)
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SUNTIL_REC])
	    THEN RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[NEXT])
	    THEN RES_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[SUNTIL_REC] THEN BETA_TAC
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[SUNTIL_REC]
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[PSNEXT])
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[PRE,ZERO_LEMMA])
	    THEN POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(SPEC(--`(d:num->bool) n`--)BOOL_CASES_AX)
	    THEN ASM_REWRITE_TAC[]
	    THEN DISJ2_TAC THEN DISJ1_TAC THEN UNDISCH_NO_TAC 1
	    THEN REWRITE_TAC[PSUNTIL,SUNTIL_SIGNAL] THEN BETA_TAC
	    THEN REPEAT STRIP_TAC THEN EXISTS_TAC(--`0`--)
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(t<0)`--))]
	]);





val PSUNTIL_AND_BEFORE_SEPARATE = TAC_PROOF(
	([], --`(a PSUNTIL (\t. b t /\ (c BEFORE d) t))
		=
		\t. (c BEFORE d) t /\ ((\t. a t /\ ~PNEXT d t) PSUNTIL b) t \/
		    (a PSUNTIL (\t. c t /\ ~d t/\ ((\t. a t /\ ~PNEXT d t) PSUNTIL b) t)) t
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION,BEFORE_REC] THEN PROP_TAC,
	    ALL_TAC]
	THEN ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN POP_ASSUM SUBST1_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[BEFORE_REC])
	    THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[BEFORE_REC] THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[PSNEXT,NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[BEFORE_REC]
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[PSNEXT])
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[PRE,ZERO_LEMMA])
	    THEN POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[BEFORE_REC]
	    THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	]);




val SEPARATE_PBEFORE_LEFT_BEFORE_THM = TAC_PROOF(
	([],--`
	((\t. a t /\ (b BEFORE c) t) PBEFORE d =
      	(\t.
            (b BEFORE c) t  /\   ((\t. ~d t /\ ~PNEXT c t) PSUNTIL (\t. a t /\ ~d t)) t \/
            ((\t. b t /\ ~c t /\ ((\t. ~d t /\ ~PNEXT c t) PSUNTIL (\t. a t /\ ~d t)) t) PBEFORE d) t))
	`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION,BEFORE_REC] THEN PROP_TAC,
	    ALL_TAC]
	THEN ONCE_REWRITE_TAC[PBEFORE_REC] THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT,PNEXT]
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT,PNEXT]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[BEFORE_REC])
	    THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[NEXT]
	    THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[PBEFORE_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 2
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`(d:num->bool) n`--)BOOL_CASES_AX)
	    THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 1
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[BEFORE_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 0
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[BEFORE_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[BEFORE_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 0
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	]);





val SEPARATE_PBEFORE_LEFT_SUNTIL_THM = TAC_PROOF(
	([],--`
	(\t. a t /\ (b SUNTIL c) t) PBEFORE d =
        (\t.
            (b SUNTIL c) t /\ ((\t. ~d t /\ PNEXT b t) PSUNTIL (\t. a t /\ ~d t)) t \/
            ((\t. c t /\      ((\t. ~d t /\ PNEXT b t) PSUNTIL (\t. a t /\ ~d t)) t) PBEFORE d) t
	)`--),
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN INDUCT_TAC
	THENL[
	    REWRITE_TAC[INITIALISATION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION,SUNTIL_REC] THEN PROP_TAC,
	    ALL_TAC]
	THEN ONCE_REWRITE_TAC[PBEFORE_REC] THEN BETA_TAC
	THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	THEN POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT,PNEXT]
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[PSUNTIL_REC] THEN BETA_TAC
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[PRE,ZERO_LEMMA,PSNEXT,PNEXT]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SUNTIL_REC])
	    THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[NEXT]
	    THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[PBEFORE_REC] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 1
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`(c:num->bool) n`--)BOOL_CASES_AX)
	    THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]
	    THENL[ALL_TAC,STRIP_TAC THEN ASM_REWRITE_TAC[]]
	    THEN DISJ_CASES_TAC(SPEC(--`(d:num->bool) n`--)BOOL_CASES_AX)
	    THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0) \/ ~(n=0)/\(0<n)`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 1
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[SUNTIL_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 0
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    (* --------------------------------------------------------	*)
	    ONCE_REWRITE_TAC[SUNTIL_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[SUNTIL_REC] THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(BETA_RULE o ONCE_REWRITE_RULE[PSUNTIL_REC])
	    THEN UNDISCH_NO_TAC 0
	    THEN REWRITE_TAC[PNEXT,PSNEXT,PRE,ZERO_LEMMA] THEN BETA_TAC
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	]);



val SEPARATE_PSUNTIL_THM = TAC_PROOF(
	([], --`
	    ( (a PSUNTIL (\t. b t \/ c t)) = \t. (a PSUNTIL b) t \/ (a PSUNTIL c) t ) /\
	    ( (a PSUNTIL (\t. b t /\ NEXT c t))	=
		\t. (b t /\ NEXT c t)
		    \/
		    (a PSUNTIL (\t. a t /\ c t /\ PSNEXT b t)) t ) /\
	    ( (a PSUNTIL (\t. b t /\ (c SUNTIL d) t)) =
		\t. (c SUNTIL d) t /\ ((\t. a t /\ PNEXT c t) PSUNTIL b) t \/
		    (a PSUNTIL (\t. d t /\ ((\t. a t /\ PNEXT c t) PSUNTIL b) t)) t ) /\
	    ( (a PSUNTIL (\t. b t /\ (c BEFORE d) t)) =
		\t. (c BEFORE d) t /\ ((\t. a t /\ ~PNEXT d t) PSUNTIL b) t \/
		    (a PSUNTIL (\t. c t /\ ~d t /\
			          ((\t. a t /\ ~PNEXT d t) PSUNTIL b) t)) t ) /\
	    ( ((\t. a t /\ b t) PSUNTIL c) = \t. (a PSUNTIL c) t /\ (b PSUNTIL c) t ) /\
	    ( ((\t. a t \/ NEXT b t) PSUNTIL c)	=
		\t. (c t) \/
		    (a t \/ NEXT b t) /\ ((\t. b t \/ PNEXT a t ) PSUNTIL (PSNEXT c)) t ) /\
	    ( ((\t. a t \/ (b SUNTIL c) t) PSUNTIL d)
		=  \t. ((b SUNTIL c) t  \/  ((\t. d t \/ PNEXT c t) PBEFORE (\t. ~a t /\ ~d t)) t )
		       /\
	               ((\t. b t \/ c t \/ ((\t. d t \/ PNEXT c t) PBEFORE (\t. ~a t /\ ~d t)) t)
			PSUNTIL d) t
	    ) /\
	    ( ((\t. a t \/ (b BEFORE c) t) PSUNTIL d)
		= \t. ((b BEFORE c) t  \/  ((\t. d t \/ PSNEXT b t) PBEFORE (\t. ~a t /\ ~d t)) t )
		      /\
	              ((\t. ~c t \/ ((\t. d t \/ PSNEXT b t) PBEFORE (\t. ~a t /\ ~d t)) t) PSUNTIL d) t
	    )
	`--),
	REWRITE_TAC[
		SEPARATE_PSUNTIL_OR_THM,
		SEPARATE_PSUNTIL_AND_THM,
		SEPARATE_PSUNTIL_OR_NEXT_THM,
		SEPARATE_PSUNTIL_AND_NEXT_THM,
		PSUNTIL_AND_SUNTIL_SEPARATE,
		PSUNTIL_AND_BEFORE_SEPARATE]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM] THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`~a t = (\t. ~a t ) t`--),BETA_TAC THEN REWRITE_TAC[])]
	THEN REWRITE_TAC[SEPARATE_PBEFORE_LEFT_BEFORE_THM,SEPARATE_PBEFORE_LEFT_SUNTIL_THM]
	THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM,NEGATION_NORMAL_FORM]);


(*---------------------------------------------------------------------------
     Normal forms involving NEXT
 ---------------------------------------------------------------------------*)


val PNEXT_NEXT = TAC_PROOF(
	([],--`PNEXT(NEXT a) = \t. InitPoint t \/ a t`--),
	CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[PNEXT,NEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(n=0) = ~(0<n)`--))]
	THEN REWRITE_TAC[TAC_PROOF(([],--`~a\/b = a==>b`--),PROP_TAC)]
	THEN DISCH_TAC THEN IMP_RES_TAC LESS_ADD_1
	THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[PRE]
	);


val PSNEXT_NEXT = TAC_PROOF(
	([],--`PSNEXT(NEXT a) = \t. ~InitPoint t /\ a t`--),
	CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[PSNEXT,NEXT,InitPoint] THEN BETA_TAC
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(n=0) = ~(0<n)`--))]
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC LESS_ADD_1
	THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[PRE]
	);


val PALWAYS_NEXT = TAC_PROOF(
	([],--`(PALWAYS (NEXT a)) = NEXT (PALWAYS (\t. a t \/ InitPoint t))`--),
	CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[PALWAYS,NEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`t<=n ==> SUC t <= SUC n`--)))
	THEN RES_TAC THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ZERO_LEMMA]
	THEN DISCH_TAC
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(n=0) = ~(0<n)`--))]
	THEN REWRITE_TAC[TAC_PROOF(([],--`b\/~a = a==>b`--),PROP_TAC)]
	THEN DISCH_TAC THEN IMP_RES_TAC LESS_ADD_1
	THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	THEN ASM_TAC 0 SUBST1_TAC THEN POP_NO_ASSUM 4 MATCH_MP_TAC
	THEN UNDISCH_NO_TAC 3 THEN UNDISCH_HD_TAC
	THEN CONV_TAC ARITH_CONV
	);


val PEVENTUAL_NEXT = TAC_PROOF(
	([],--`(PEVENTUAL (NEXT a))  = NEXT (PEVENTUAL (\t. a t /\ ~InitPoint t))`--),
	CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[PEVENTUAL,NEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_NO_TAC 1 THEN CONV_TAC ARITH_CONV,
	    RULE_ASSUM_TAC(REWRITE_RULE[EQT_ELIM(ARITH_CONV(--`~(t=0) = (0<t)`--))])
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
	    THEN EXISTS_TAC(--`p:num`--) THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_NO_TAC 2 THEN CONV_TAC ARITH_CONV
	]);


val PSUNTIL_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PSUNTIL (NEXT b))  = NEXT ((PNEXT a) PSUNTIL (\t. b t /\ ~InitPoint t))`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSUNTIL,NEXT,PNEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA]
	    THEN ONCE_REWRITE_TAC[ARITH_PROVE(--`(SUC a<b) = (SUC a<b) /\ ~(b=0)`--)]
	    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1 THEN POP_NO_TAC 0
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 2
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 4 (--`SUC t`--)
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ZERO_LEMMA,PRE])
	    THEN POP_ASSUM MATCH_MP_TAC THEN MAP_EVERY POP_NO_TAC [4,3]
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);


val PSBEFORE_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PSBEFORE b) = NEXT ((\t. a t /\ ~InitPoint t) PSBEFORE (PNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSBEFORE,NEXT,PNEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA]
	    THEN ONCE_REWRITE_TAC[ARITH_PROVE(--`(SUC a<=b) = (SUC a<=b) /\ ~(b=0)`--)]
	    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 2
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 4 (--`SUC t`--)
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ZERO_LEMMA,PRE])
	    THEN POP_ASSUM MATCH_MP_TAC THEN MAP_EVERY POP_NO_TAC [4,3]
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);


val PSUNTIL_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PSUNTIL b) = NEXT (a PSUNTIL (PSNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSUNTIL,NEXT,PSNEXT] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA,PRE]
	    THEN ONCE_REWRITE_TAC[ARITH_PROVE(--`(SUC a<b) = (SUC a<b) /\ ~(b=0)`--)]
	    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1 THEN POP_NO_TAC 0
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 2
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x,PRE]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 3 (--`SUC t`--)
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ZERO_LEMMA,PRE])
	    THEN POP_ASSUM MATCH_MP_TAC THEN POP_NO_TAC 4
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);


val PSWHEN_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PSWHEN b) = NEXT (a PSWHEN (PSNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSWHEN,NEXT,PSNEXT] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA,PRE]
	    THEN ONCE_REWRITE_TAC[ARITH_PROVE(--`(SUC a<b) = (SUC a<b) /\ ~(b=0)`--)]
	    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1 THEN POP_NO_TAC 0
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 2
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x,PRE]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 3 (--`SUC t`--)
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ZERO_LEMMA,PRE])
	    THEN POP_ASSUM MATCH_MP_TAC THEN POP_NO_TAC 4
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);


val PSBEFORE_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PSBEFORE (NEXT b)) = NEXT ((PSNEXT a) PSBEFORE b)`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSBEFORE,NEXT,PSNEXT] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA,PRE]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN IMP_RES_TAC(ARITH_PROVE(--`(SUC b<=a) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1 THEN MAP_EVERY POP_NO_TAC [3,2,1]
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 4 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 2 THEN UNDISCH_NO_TAC 1
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x,PRE]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 3 (--`SUC t`--)
	    THEN POP_ASSUM MATCH_MP_TAC
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);



val PUNTIL_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PUNTIL b) = NEXT ((\t. a t \/ InitPoint t) PUNTIL (PNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSBEFORE_LEFT_NEXT] THEN BETA_TAC
	THEN REWRITE_TAC[DE_MORGAN_THM]
	);

val PWHEN_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PWHEN b) = NEXT (a PWHEN (PSNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSWHEN_LEFT_NEXT]
	);

val PBEFORE_LEFT_NEXT = TAC_PROOF(
	([],--`((NEXT a) PBEFORE b) = NEXT (a PBEFORE (PSNEXT b))`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSUNTIL_LEFT_NEXT]
	);


val PUNTIL_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PUNTIL (NEXT b)) = NEXT ((PNEXT a) PUNTIL b)`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSBEFORE_RIGHT_NEXT]
	);


val PBEFORE_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PBEFORE (NEXT b)) = NEXT ((PNEXT a) PBEFORE (\t. ~InitPoint t /\ b t))`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSUNTIL_RIGHT_NEXT]
	THEN GEN_TAC THEN REWRITE_TAC[PSUNTIL,InitPoint,PNEXT,PSNEXT,NEXT]
	THEN BETA_TAC THEN REWRITE_TAC[ARITH_PROVE(--`(n=0) = ~(0<n)`--)]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	THEN GEN_TAC THEN STRIP_TAC
	THEN LEFT_NO_FORALL_TAC 2 (--`t':num`--) THEN UNDISCH_HD_TAC
	THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC(ARITH_PROVE(--`delta<t' ==> 0<t'`--))
	THEN ASM_REWRITE_TAC[]
	);


val PSWHEN_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PSWHEN (NEXT b)) = NEXT ((PNEXT a) PSWHEN (\t. b t /\ ~InitPoint t))`--),
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[PSWHEN,NEXT,PNEXT,InitPoint] THEN BETA_TAC
	THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`SUC delta`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`a<=b ==> SUC a <= SUC b`--))
	    THEN ASM_REWRITE_TAC[ZERO_LEMMA,PRE]
	    THEN ONCE_REWRITE_TAC[ARITH_PROVE(--`(SUC a<b) = (SUC a<b) /\ ~(b=0)`--)]
	    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	    THEN IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1 THEN POP_NO_TAC 0
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[PRE]
	    THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 2
	    THEN ASM_REWRITE_TAC[] THEN ARITH_TAC,
	    IMP_RES_TAC(ARITH_PROVE(--`~(a=0) ==> (0<a)`--))
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x,PRE]))
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN IMP_RES_TAC(ARITH_PROVE(--`SUC a <= SUC b ==> a<=b`--))
	    THEN ASM_REWRITE_TAC[]
	    THEN GEN_TAC THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 4 (--`SUC t`--)
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ZERO_LEMMA,PRE])
	    THEN POP_ASSUM MATCH_MP_TAC THEN MAP_EVERY POP_NO_TAC [4,3]
	    THEN ASM_REWRITE_TAC[LESS_MONO_EQ,ARITH_PROVE(--`(SUC a<=SUC b) = (a<=b)`--)]
	]);





val PWHEN_RIGHT_NEXT = TAC_PROOF(
	([],--`(a PWHEN (NEXT b)) = NEXT ((PNEXT a) PWHEN (\t. b t /\ ~InitPoint t))`--),
	CONV_TAC FUN_EQ_CONV
	THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b) = (~a=~b)`--),PROP_TAC)]
	THEN REWRITE_TAC[NEGATION_NORMAL_FORM]
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[PSWHEN_RIGHT_NEXT]
	THEN GEN_TAC THEN REWRITE_TAC[PSWHEN,InitPoint,PNEXT,PSNEXT,NEXT]
	THEN BETA_TAC THEN REWRITE_TAC[ARITH_PROVE(--`(n=0) = ~(0<n)`--)]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	THEN RES_TAC
	);




val PRENEX_NEXT_NORMAL_FORM = TAC_PROOF(
	([],--`
	( ~NEXT a t 		= NEXT (\t. ~a t) t ) /\
	( a t /\ NEXT b t 	= NEXT(\t. PNEXT a t /\ b t) t ) /\
	( a t \/ NEXT b t 	= NEXT(\t. PNEXT a t \/ b t) t ) /\
	( (ALWAYS (NEXT a))     = NEXT (ALWAYS a) ) /\
	( (EVENTUAL (NEXT a))   = NEXT (EVENTUAL a) ) /\
	( (a SUNTIL (NEXT b))   = NEXT ((PNEXT a) SUNTIL b) ) /\
	( (a SWHEN (NEXT b))    = NEXT ((PNEXT a) SWHEN b) ) /\
	( (a SBEFORE (NEXT b))  = NEXT ((PNEXT a) SBEFORE b) ) /\
	( (a UNTIL (NEXT b))    = NEXT ((PNEXT a) UNTIL b) ) /\
	( (a WHEN (NEXT b))     = NEXT ((PNEXT a) WHEN b) ) /\
	( (a BEFORE (NEXT b))   = NEXT ((PNEXT a) BEFORE b) ) /\
	( ((NEXT a) SUNTIL b)   = NEXT (a SUNTIL (PNEXT b)) ) /\
	( ((NEXT a) SWHEN b)    = NEXT (a SWHEN (PNEXT b)) ) /\
	( ((NEXT a) SBEFORE b)  = NEXT (a SBEFORE (PNEXT b)) ) /\
	( ((NEXT a) UNTIL b)    = NEXT (a UNTIL (PNEXT b)) ) /\
	( ((NEXT a) WHEN b)     = NEXT (a WHEN (PNEXT b)) ) /\
	( ((NEXT a) BEFORE b)   = NEXT (a BEFORE (PNEXT b)) ) /\
	( PNEXT(NEXT a) 	= \t. InitPoint t \/ a t ) /\
	( PSNEXT (NEXT a) 	= \t. ~InitPoint t /\ a t ) /\
	( (PALWAYS (NEXT a))    = NEXT (PALWAYS (\t. InitPoint t \/ a t)) ) /\
	( (PEVENTUAL (NEXT a))  = NEXT (PEVENTUAL (\t. ~InitPoint t /\ a t )) ) /\
	( (a PSUNTIL (NEXT b))  = NEXT ((PNEXT a) PSUNTIL (\t. ~InitPoint t /\ b t)) ) /\
	( (a PSWHEN (NEXT b))   = NEXT ((PNEXT a) PSWHEN (\t. ~InitPoint t /\ b t)) ) /\
	( (a PSBEFORE (NEXT b)) = NEXT ((PSNEXT a) PSBEFORE b) ) /\
	( (a PUNTIL (NEXT b))   = NEXT ((PNEXT a) PUNTIL b) ) /\
	( (a PWHEN (NEXT b))    = NEXT ((PNEXT a) PWHEN (\t. ~InitPoint t /\ b t)) ) /\
	( (a PBEFORE (NEXT b))  = NEXT ((PNEXT a) PBEFORE (\t. ~InitPoint t /\ b t)) ) /\
	( ((NEXT a) PSUNTIL b)  = NEXT (a PSUNTIL (PSNEXT b)) ) /\
	( ((NEXT a) PSWHEN b)   = NEXT (a PSWHEN (PSNEXT b)) ) /\
	( ((NEXT a) PSBEFORE b) = NEXT ((\t. ~InitPoint t /\ a t) PSBEFORE (PNEXT b)) ) /\
	( ((NEXT a) PUNTIL b)   = NEXT ((\t. InitPoint t \/ a t) PUNTIL (PNEXT b)) ) /\
	( ((NEXT a) PWHEN b)    = NEXT (a PWHEN (PSNEXT b)) ) /\
	( ((NEXT a) PBEFORE b)  = NEXT (a PBEFORE (PSNEXT b)) )
	`--),
	REWRITE_TAC[
		AND_NEXT,OR_NEXT,NOT_NEXT,
		ALWAYS_NEXT,EVENTUAL_NEXT,
		SUNTIL_NEXT,UNTIL_NEXT,
		SWHEN_NEXT,WHEN_NEXT,
		SBEFORE_NEXT,BEFORE_NEXT,
		PNEXT_NEXT,PSNEXT_NEXT,
		PALWAYS_NEXT,PEVENTUAL_NEXT,
		PSUNTIL_RIGHT_NEXT,PUNTIL_RIGHT_NEXT,
		PSWHEN_RIGHT_NEXT,PWHEN_RIGHT_NEXT,
		PSBEFORE_RIGHT_NEXT,PBEFORE_RIGHT_NEXT,
		PSUNTIL_LEFT_NEXT,PUNTIL_LEFT_NEXT,
		PSWHEN_LEFT_NEXT,PWHEN_LEFT_NEXT,
		PSBEFORE_LEFT_NEXT,PBEFORE_LEFT_NEXT
		]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a t \/ InitPoint t = InitPoint t \/ a t`--),PROP_TAC)]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a t /\ ~InitPoint t = ~InitPoint t /\ a t`--),PROP_TAC)]
	THEN REWRITE_TAC[TAC_PROOF(([],--`NEXT (PNEXT a) = a`--),
			CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[PNEXT,NEXT]
			THEN BETA_TAC THEN REWRITE_TAC[PRE,ZERO_LEMMA])]
	THEN BETA_TAC THEN REWRITE_TAC[]
	);





val NEXT_INWARDS_NORMAL_FORM = TAC_PROOF(
	([],--`
	( NEXT (\t. ~a t)	= \t. ~NEXT a t  				) /\
	( NEXT (\t. a t /\ b t)	= \t. NEXT a t /\ NEXT b t 			) /\
	( NEXT (\t. a t \/ b t)	= \t. NEXT a t \/ NEXT b t 			) /\
	( NEXT (ALWAYS a)       = (ALWAYS (NEXT a))				) /\
	( NEXT (EVENTUAL a)	= (EVENTUAL (NEXT a))   			) /\
	( NEXT (a SUNTIL b)	= ((NEXT a) SUNTIL (NEXT b))   			) /\
	( NEXT (a SWHEN b)	= ((NEXT a) SWHEN (NEXT b))   			) /\
	( NEXT (a SBEFORE b)	= ((NEXT a) SBEFORE (NEXT b))  			) /\
	( NEXT (a UNTIL b)	= ((NEXT a) UNTIL (NEXT b))   			) /\
	( NEXT (a WHEN b)	= ((NEXT a) WHEN (NEXT b))   			) /\
	( NEXT (a BEFORE b)	= ((NEXT a) BEFORE (NEXT b))  			) /\
	( NEXT (PNEXT a)        = a						) /\
	( NEXT (PSNEXT a)       = a						) /\
	( NEXT (PALWAYS a)      = \t. (PALWAYS a) t /\ NEXT a t			) /\
	( NEXT (PEVENTUAL a)	= \t. (PEVENTUAL a) t \/ NEXT a t 		) /\
	( NEXT (a PSUNTIL b)	= \t. (NEXT b) t \/ (NEXT a) t /\ (a PSUNTIL b) t      ) /\
	( NEXT (a PSWHEN b)	= \t. if (NEXT b) t then (NEXT a) t else (a PSWHEN b) t        ) /\
	( NEXT (a PSBEFORE b)	= \t. ~(NEXT b) t /\ ( (NEXT a) t \/ (a PSBEFORE b) t) ) /\
	( NEXT (a PUNTIL b)	= \t. (NEXT b) t \/ (NEXT a) t /\ (a PUNTIL b) t       ) /\
	( NEXT (a PWHEN b)	= \t. if (NEXT b) t then (NEXT a) t else (a PWHEN b) t         ) /\
	( NEXT (a PBEFORE b)	= \t. ~(NEXT b) t /\ ( (NEXT a) t \/ (a PBEFORE b) t) )
	`--),
	REWRITE_TAC[AND_NEXT,OR_NEXT,NOT_NEXT,ALWAYS_NEXT,EVENTUAL_NEXT,
	      SUNTIL_NEXT,UNTIL_NEXT,SWHEN_NEXT,WHEN_NEXT,
	      SBEFORE_NEXT,BEFORE_NEXT]
	THEN ONCE_REWRITE_TAC[RECURSION]
	THEN REWRITE_TAC[AND_NEXT,OR_NEXT,NOT_NEXT]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REWRITE_TAC[NEXT,PNEXT,PSNEXT]
	THEN BETA_TAC THEN REWRITE_TAC[ZERO_LEMMA,PRE]
	THEN REPEAT CONJ_TAC THEN INDUCT_TAC
	THEN REWRITE_TAC[INITIALISATION,ZERO_LEMMA,PRE]
	THEN (PROP_TAC ORELSE ALL_TAC)
	THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	THEN REWRITE_TAC[PNEXT,PSNEXT] THEN BETA_TAC
	THEN REWRITE_TAC[PRE,ZERO_LEMMA]
	THEN PROP_TAC);





val PNEXT_INWARDS_NORMAL_FORM = TAC_PROOF(
	([],--`
	( PNEXT (\t. ~a t)	 = \t. ~PSNEXT a t  				) /\
	( PNEXT (\t. a t /\ b t) = \t. PNEXT a t /\ PNEXT b t 			) /\
	( PNEXT (\t. a t \/ b t) = \t. PNEXT a t \/ PNEXT b t 			) /\
	( PNEXT (NEXT a)         = \t. InitPoint t \/ a t 			) /\
	( PNEXT (ALWAYS a)       = \t. InitPoint t \/ (ALWAYS (PNEXT a)) t	) /\
	( PNEXT (EVENTUAL a)	 = \t. InitPoint t \/ (EVENTUAL (PNEXT a)) t	) /\
	( PNEXT (a SUNTIL b)	= ((PNEXT a) SUNTIL (PNEXT b))   		) /\
	( PNEXT (a SWHEN b)	= ((PNEXT a) SWHEN (PNEXT b))   		) /\
	( PNEXT (a SBEFORE b)	= ((PNEXT a) SBEFORE (PSNEXT b)) 		) /\
	( PNEXT (a UNTIL b)	= ((PNEXT a) UNTIL (PNEXT b)) 			) /\
	( PNEXT (a WHEN b)	= ((PNEXT a) WHEN (PNEXT b))   			) /\
	( PNEXT (a BEFORE b)	= ((PNEXT a) BEFORE (PSNEXT b))  		) /\
	( PNEXT (PALWAYS a)     = (PALWAYS (PNEXT a))				) /\
	( PNEXT (PEVENTUAL a)	= \t. InitPoint t \/ (PEVENTUAL (PSNEXT a)) t 	       ) /\
	( PNEXT (a PSUNTIL b)	= \t. InitPoint t \/ ((PNEXT a) PSUNTIL (PSNEXT b)) t  ) /\
	( PNEXT (a PSWHEN b)	= \t. InitPoint t \/ ((PNEXT a) PSWHEN (PSNEXT b)) t   ) /\
	( PNEXT (a PSBEFORE b)	= \t. InitPoint t \/ ((PSNEXT a) PSBEFORE (PNEXT b)) t ) /\
	( PNEXT (a PUNTIL b)	= ((PNEXT a) PUNTIL (PNEXT b))      		) /\
	( PNEXT (a PWHEN b)	= ((PNEXT a) PWHEN (PNEXT b))      		) /\
	( PNEXT (a PBEFORE b)	= ((PNEXT a) PBEFORE (PSNEXT b))      		)
	`--),
    let val PSNEXT_AS_PNEXT = TAC_PROOF(
	    ([],--`PSNEXT a t = ~InitPoint t /\ PNEXT a t `--),
	    REWRITE_TAC[PSNEXT,PNEXT,InitPoint] THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~a/\(a\/b) = ~a/\b`--),PROP_TAC)]
	    THEN REWRITE_TAC[ARITH_PROVE(--`~(t=0) = (0<t)`--)]
	    )
     in
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN CONV_TAC(DEPTH_CONV AND_FORALL_CONV)
	THEN INDUCT_TAC THEN REWRITE_TAC[INITIALISATION]
	THENL[
	    (* Proving the induction base *)
	    REWRITE_TAC[InitPoint] THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[RECURSION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION],
	    ALL_TAC]
	(* Proving the induction step *)
	THEN REWRITE_TAC[TAC_PROOF(([],(--`P(SUC n) = NEXT P n`--)),
		REWRITE_TAC[NEXT] THEN BETA_TAC THEN REWRITE_TAC[])]
	THEN REWRITE_TAC[NEXT_INWARDS_NORMAL_FORM]
	THEN BETA_TAC THEN REWRITE_TAC[]
	THEN REWRITE_TAC[NEXT,InitPoint] THEN BETA_TAC
	THEN REWRITE_TAC[ZERO_LEMMA]
	(* only the past operators remain here *)
	THEN REPEAT CONJ_TAC
	THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	THEN BETA_TAC THEN ASM_REWRITE_TAC[PSNEXT_AS_PNEXT]
	THEN (PROP_TAC ORELSE ALL_TAC)
	(* only the strong past operators remain here *)
	THEN POP_NO_TAC 0
	THEN ONCE_REWRITE_TAC[RECURSION]
	THEN BETA_TAC THEN REWRITE_TAC[InitPoint,PSNEXT]
	THEN BETA_TAC THEN REWRITE_TAC[ARITH_PROVE(--`(t=0) = ~(0<t)`--)]
	THEN PROP_TAC
    end);


(*

val PSNEXT_INWARDS_NORMAL_FORM = TAC_PROOF(
	([],--`
	( PSNEXT (\t. ~a t)	  = \t. ~PNEXT a t  				) /\
	( PSNEXT (\t. a t /\ b t) = \t. PSNEXT a t /\ PSNEXT b t 		) /\
	( PSNEXT (\t. a t \/ b t) = \t. PSNEXT a t \/ PSNEXT b t 		) /\
	( PSNEXT (NEXT a)         = \t. ~InitPoint t /\ a t 			) /\
	( PSNEXT (ALWAYS a)       = (ALWAYS (PSNEXT a))				) /\
	( PSNEXT (EVENTUAL a)	  = (EVENTUAL (PSNEXT a)) 			) /\
	( PSNEXT (a SUNTIL b)	  = ((PSNEXT a) SUNTIL (PSNEXT b))   		) /\
	( PSNEXT (a SWHEN b)	  = ((PSNEXT a) SWHEN (PSNEXT b))   		) /\
	( PSNEXT (a SBEFORE b)	  = ((PSNEXT a) SBEFORE (PSNEXT b)) 		) /\
	( PSNEXT (a UNTIL b)	  = ((PSNEXT a) UNTIL (PSNEXT b)) 		) /\
	( PSNEXT (a WHEN b)	  = ((PSNEXT a) WHEN (PSNEXT b))   		) /\
	( PSNEXT (a BEFORE b)	  = ((PSNEXT a) BEFORE (PSNEXT b))  		) /\

	( PSNEXT (PALWAYS a)      = (PALWAYS (PSNEXT a))			) /\
	( PSNEXT (PEVENTUAL a)	  = (PEVENTUAL (PSNEXT a))  	       ) /\
	( PSNEXT (a PSUNTIL b)	  = ((PSNEXT a) PSUNTIL (PSNEXT b))   ) /\
	( PSNEXT (a PSWHEN b)	  = ((PSNEXT a) PSWHEN (PSNEXT b))    ) /\
	( PSNEXT (a PSBEFORE b)	  = ((PSNEXT a) PSBEFORE (PSNEXT b))  ) /\
	( PSNEXT (a PUNTIL b)	  = ((PSNEXT a) PUNTIL (PSNEXT b))      		) /\
	( PSNEXT (a PWHEN b)	  = ((PSNEXT a) PWHEN (PSNEXT b))      		) /\
	( PSNEXT (a PBEFORE b)	  = ((PSNEXT a) PBEFORE (PSNEXT b))      		)
	`--),
    let val PSNEXT_AS_PNEXT = TAC_PROOF(
	    ([],--`PSNEXT a t = ~InitPoint t /\ PNEXT a t `--),
	    REWRITE_TAC[PSNEXT,PNEXT,InitPoint] THEN BETA_TAC
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~a/\(a\/b) = ~a/\b`--),PROP_TAC)]
	    THEN REWRITE_TAC[ARITH_PROVE(--`~(t=0) = (0<t)`--)]
	    )
     in
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN CONV_TAC(DEPTH_CONV AND_FORALL_CONV)
	THEN INDUCT_TAC THEN REWRITE_TAC[INITIALISATION]
	THENL[
	    (* Proving the induction base *)
	    REWRITE_TAC[InitPoint] THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN ONCE_REWRITE_TAC[RECURSION] THEN BETA_TAC
	    THEN REWRITE_TAC[INITIALISATION],
	    ALL_TAC]
	(* Proving the induction step *)
	THEN REWRITE_TAC[TAC_PROOF(([],(--`P(SUC n) = NEXT P n`--)),
		REWRITE_TAC[NEXT] THEN BETA_TAC THEN REWRITE_TAC[])]
	THEN REWRITE_TAC[NEXT_INWARDS_NORMAL_FORM]
	THEN BETA_TAC THEN REWRITE_TAC[]
	THEN REWRITE_TAC[NEXT,InitPoint] THEN BETA_TAC
	THEN REWRITE_TAC[ZERO_LEMMA]
	(* only the past operators remain here *)
	THEN REPEAT CONJ_TAC
	THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	THEN BETA_TAC THEN ASM_REWRITE_TAC[PSNEXT_AS_PNEXT]
	THEN (PROP_TAC ORELSE ALL_TAC)
	(* only the strong past operators remain here *)
	THEN POP_NO_TAC 0
	THEN ONCE_REWRITE_TAC[RECURSION]
	THEN BETA_TAC THEN REWRITE_TAC[InitPoint,PSNEXT]
	THEN BETA_TAC THEN REWRITE_TAC[ARITH_PROVE(--`(t=0) = ~(0<t)`--)]
	THEN PROP_TAC
    end);



*)


val _ = save_thm("INITIALISATION",INITIALISATION);

val _ = save_thm("RECURSION",RECURSION);

val _ = save_thm("FIXPOINTS",FIXPOINTS);

val _ = save_thm("SUNTIL_EXPRESSIVE",SUNTIL_EXPRESSIVE);
val _ = save_thm("UNTIL_EXPRESSIVE",UNTIL_EXPRESSIVE);
val _ = save_thm("WHEN_EXPRESSIVE",WHEN_EXPRESSIVE);
val _ = save_thm("SWHEN_EXPRESSIVE",SWHEN_EXPRESSIVE);
val _ = save_thm("BEFORE_EXPRESSIVE",BEFORE_EXPRESSIVE);
val _ = save_thm("SBEFORE_EXPRESSIVE",SBEFORE_EXPRESSIVE);
val _ = save_thm("PSUNTIL_EXPRESSIVE",PSUNTIL_EXPRESSIVE);
val _ = save_thm("PUNTIL_EXPRESSIVE",PUNTIL_EXPRESSIVE);
val _ = save_thm("PWHEN_EXPRESSIVE",PWHEN_EXPRESSIVE);
val _ = save_thm("PSWHEN_EXPRESSIVE",PSWHEN_EXPRESSIVE);
val _ = save_thm("PBEFORE_EXPRESSIVE",PBEFORE_EXPRESSIVE);
val _ = save_thm("PSBEFORE_EXPRESSIVE",PSBEFORE_EXPRESSIVE);

val _ = save_thm("NEGATION_NORMAL_FORM",NEGATION_NORMAL_FORM);
val _ = save_thm("CONJUNCTIVE_NORMAL_FORM",CONJUNCTIVE_NORMAL_FORM);
val _ = save_thm("DISJUNCTIVE_NORMAL_FORM",DISJUNCTIVE_NORMAL_FORM);
val _ = save_thm("PRENEX_NEXT_NORMAL_FORM",PRENEX_NEXT_NORMAL_FORM);
val _ = save_thm("NEXT_INWARDS_NORMAL_FORM",NEXT_INWARDS_NORMAL_FORM);
val _ = save_thm("PNEXT_INWARDS_NORMAL_FORM",PNEXT_INWARDS_NORMAL_FORM);

val _ = save_thm("SIMPLIFY",SIMPLIFY);
val _ = save_thm("MORE_EVENT",MORE_EVENT);
val _ = save_thm("IMMEDIATE_EVENT",IMMEDIATE_EVENT);
val _ = save_thm("NO_FUTURE_EVENT",NO_FUTURE_EVENT);
val _ = save_thm("NO_PAST_EVENT",NO_PAST_EVENT);
val _ = save_thm("SOME_FUTURE_EVENT",SOME_FUTURE_EVENT);
val _ = save_thm("SOME_PAST_EVENT",SOME_PAST_EVENT);

val _ = save_thm("SEPARATE_NEXT_THM",SEPARATE_NEXT_THM);
val _ = save_thm("SEPARATE_SUNTIL_THM",SEPARATE_SUNTIL_THM);
val _ = save_thm("SEPARATE_BEFORE_THM",SEPARATE_BEFORE_THM);

val _ = save_thm("SEPARATE_PNEXT_THM",SEPARATE_PNEXT_THM);
val _ = save_thm("SEPARATE_PSUNTIL_THM",SEPARATE_PSUNTIL_THM);

val _ = export_theory();
