(* interactive use:

quietdec := true;

loadPath :=
            (concat Globals.HOLDIR "/examples/dev/sw") ::
            (concat Globals.HOLDIR "/examples/elliptic/arm") ::
            (concat Globals.HOLDIR "/examples/elliptic/sep") ::
            !loadPath;

map load
 ["preARMTheory",
  "finite_mapTheory", "listLib", "arm_evalLib", "arm_rulesTheory",
"armLib", "wordsLib", "wordsTheory", "arithmeticTheory", "pairTheory",
"listTheory", "ILTheory", "containerTheory", "schneiderUtils",
"arm_progTheory", "set_sepLib", "arm_instTheory", "pred_setSyntax",
"rulesTheory", "bsubstTheory"];



*)
open HolKernel boolLib bossLib;
open Parse ILTheory listLib preARMTheory finite_mapTheory arm_evalLib arm_rulesTheory armLib wordsLib wordsTheory arithmeticTheory pairTheory listTheory pred_setTheory containerTheory rich_listTheory
open arm_progTheory progTheory pred_setTheory set_sepLib set_sepTheory arm_instTheory ILTheory sortingTheory;

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
show_types_verbosely := true;
show_types_verbosely := false;
quietdec := false;
*)

val _ = hide "reg";
val _ = hide "regs";
val _ = hide "mem";
val _ = hide "M";
val _ = hide "cond";



val _ = new_theory "swsep";



val UNDISCH_HD_TAC = schneiderUtils.UNDISCH_HD_TAC;
val UNDISCH_ALL_TAC = schneiderUtils.UNDISCH_ALL_TAC;
val UNDISCH_NO_TAC = schneiderUtils.UNDISCH_NO_TAC
val POP_NO_ASSUM = schneiderUtils.POP_NO_ASSUM;
val WEAKEN_HD_TAC = WEAKEN_TAC (fn f => true);


val SUBGOAL_TAC = (fn t => (t by ALL_TAC));
val REMAINS_TAC = (fn t => (Tactical.REVERSE(t by ALL_TAC)));

val FORALL_EQ_STRIP_TAC :tactic = fn (asl,t) =>

	let val (lhs,rhs) = dest_eq t
		val (lvar,LBody) = dest_forall lhs
		val (rvar,RBody) = dest_forall rhs
		val newVar = variant (free_varsl (t::asl)) lvar
		val newLBody = subst[lvar |-> newVar] LBody
		val newRBody = subst[rvar |-> newVar] RBody
		val result = mk_eq(newLBody, newRBody)
	in ([(asl, result)],
		fn thList => FORALL_EQ newVar (hd thList))
	end
	handle HOL_ERR _ => raise ERR "FORALL_EQ_STRIP_TAC" "";


val SPEC_NO_ASSUM = (fn n => fn S => POP_NO_ASSUM n (fn x=> ASSUME_TAC (SPEC S x)));
fun Q_SPEC_NO_ASSUM n = Q_TAC (SPEC_NO_ASSUM n);
fun Q_SPECL_NO_ASSUM n [] = ALL_TAC
	| Q_SPECL_NO_ASSUM n (h::l) = (Q_SPEC_NO_ASSUM n h THEN Q_SPECL_NO_ASSUM 0 l);

fun GSYM_DEF_TAC t (asl, w) =
	let
		fun is_t_eq term =
			let
				val (l, r) = dest_eq term
			in
				(l = t) orelse (r = t)
			end handle _ => false
		val m = first is_t_eq asl;
		val (ob, asl') = Lib.pluck (Lib.equal m) asl
	in
		ASSUME_TAC (GSYM (ASSUME ob)) (asl', w)
	end;

fun PROVE_CONDITION_TAC thm (asl, t) =
	let
		val (p, c) = dest_imp (concl thm);
		fun mp_thm thms =
		let
			val thm_p = el 1 thms;
			val thm_t = el 2 thms;
			val thm = MP thm thm_p;
			val result = DISCH (concl thm) thm_t;
			val result = MP result thm
		in
			result
		end
	in
		([(asl, p), (c::asl, t)], mp_thm)
	end;

fun PROVE_CONDITION_NO_ASSUM i = POP_NO_ASSUM i PROVE_CONDITION_TAC


val MREG2REG_def = Define
  `(MREG2REG reg = (n2w (index_of_reg reg)):4 word)`

val MEXP2addr_model_def = Define
  `(MEXP2addr_model (MR reg) = (Dp_shift_immediate (LSL (MREG2REG reg)) 0x0w)) /\
   (MEXP2addr_model (MC s c) = (Dp_immediate s c))`;

val IS_MEMORY_DOPER_def = Define `
  (IS_MEMORY_DOPER (MLDR dst src) = T) /\
  (IS_MEMORY_DOPER (MSTR src dst) = T) /\
  (IS_MEMORY_DOPER (MPUSH dst' srcL) = T) /\
  (IS_MEMORY_DOPER (MPOP dst' srcL) = T) /\
  (IS_MEMORY_DOPER y = F)`

val IS_WELL_FORMED_DOPER_def = Define `
  (IS_WELL_FORMED_DOPER (MMUL dst src1 src2) = ~(dst = src1)) /\
  (IS_WELL_FORMED_DOPER y = T)`

val OFFSET2addr2_def = Define `
	(OFFSET2addr2 (POS n) = Dt_immediate ((n2w (n MOD 2**11)))) /\
	(OFFSET2addr2 (NEG n) = Dt_immediate ($- (n2w (n MOD 2**11))))`;


val IS_SORTED_REG_LIST_def = Define`
    (IS_SORTED_REG_LIST [] = T) /\
	 (IS_SORTED_REG_LIST [e] = (e <= 15)) /\
	 (IS_SORTED_REG_LIST (e1::e2::l) = (e1 < e2) /\ IS_SORTED_REG_LIST (e2::l))`;

val IS_SORTED_REG_LIST___EL_SIZE = store_thm ("IS_SORTED_REG_LIST___EL_SIZE",
``!l. IS_SORTED_REG_LIST l ==> (EVERY (\n. n < 16) l)``,

Induct_on `l` THENL [
	SIMP_TAC list_ss [],

	Cases_on `l` THENL [
		SIMP_TAC list_ss [IS_SORTED_REG_LIST_def],

		FULL_SIMP_TAC list_ss [IS_SORTED_REG_LIST_def] THEN
		REPEAT STRIP_TAC THEN
		`h < 16` by RES_TAC THEN
		ASM_SIMP_TAC arith_ss []
	]
])

val IS_SORTED_REG_LIST___SORTED_WORDS =
		store_thm ("IS_SORTED_REG_LIST___SORTED_WORDS",
		``!l. IS_SORTED_REG_LIST l =
		  (SORTED $<+ (MAP (n2w:num->word4) l) /\
		  (EVERY (\n. n < 16) l))``,

		Induct_on `l` THENL [
			SIMP_TAC list_ss [SORTED_DEF, IS_SORTED_REG_LIST_def],

			Cases_on `l` THENL [
				SIMP_TAC list_ss [SORTED_DEF, IS_SORTED_REG_LIST_def],

				GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
					FULL_SIMP_TAC list_ss [SORTED_DEF, IS_SORTED_REG_LIST_def,
						WORD_LO, w2n_n2w, dimword_4] THEN
					REPEAT STRIP_TAC THEN
					IMP_RES_TAC IS_SORTED_REG_LIST___EL_SIZE THEN
					FULL_SIMP_TAC list_ss [],

					PROVE_TAC[IS_SORTED_REG_LIST___EL_SIZE],

					FULL_SIMP_TAC list_ss [SORTED_DEF, IS_SORTED_REG_LIST_def,
						WORD_LO, w2n_n2w, dimword_4]
				]
			]
		])

val REGISTER_LIST___reg_bitmap = store_thm ("REGISTER_LIST___reg_bitmap",
``!l. IS_SORTED_REG_LIST l ==> (REGISTER_LIST (reg_bitmap (MAP n2w l)) =
							     (MAP n2w l))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SORTED_LOWER_IMP_EQ THEN
FULL_SIMP_TAC std_ss [MEM_REGISTER_LIST_reg_bitmap, SORTED_REGSITER_LIST, IS_SORTED_REG_LIST___SORTED_WORDS])


val STACK_SIZE_DOPER_def = Define
	`(STACK_SIZE_DOPER (MPUSH r l) = (LENGTH l, 0, (r = 13) /\ (IS_SORTED_REG_LIST l))) /\
	 (STACK_SIZE_DOPER (MPOP r l) = (0, LENGTH l, (r = 13) /\ (IS_SORTED_REG_LIST l))) /\
	 (STACK_SIZE_DOPER (MMOV dst e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MADD dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MSUB dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MRSB dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MMUL dst reg1 reg2) = (0, 0, ~(dst = R13) /\
		~(dst = reg1))) /\
	 (STACK_SIZE_DOPER (MAND dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MORR dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MEOR dst reg1 e) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MLSL dst reg1 s) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MLSR dst reg1 s) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MASR dst reg1 s) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER (MROR dst reg1 s) = (0, 0, ~(dst = R13))) /\
	 (STACK_SIZE_DOPER _ = (0, 0, F))`;

val VALID_STACK_SIZE_DOPER___IMPLIES___WELL_FORMED =
	store_thm ("VALID_STACK_SIZE_DOPER___IMPLIES___WELL_FORMED",
``!doper p n.
  (STACK_SIZE_DOPER doper = (p, n, T)) ==> IS_WELL_FORMED_DOPER doper``,

Cases_on `doper` THEN
SIMP_TAC std_ss [IS_WELL_FORMED_DOPER_def,
					  STACK_SIZE_DOPER_def])


val NOT_MEMORY_DOPER___STACK_SIZE_DOPER =
	store_thm ("NOT_MEMORY_DOPER___STACK_SIZE_DOPER",
``!doper p n.
  ~(IS_MEMORY_DOPER doper) ==>
	?v. (STACK_SIZE_DOPER doper = (0, 0, v))``,

Cases_on `doper` THEN
SIMP_TAC std_ss [IS_MEMORY_DOPER_def,
					  STACK_SIZE_DOPER_def])


val STACK_SIZE_BLK_def = Define
	`(STACK_SIZE_BLK (max, current, valid) [] = (max, current, valid)) /\
	 (STACK_SIZE_BLK (max, current, valid) (h::l) =
	    let (p, n, v) = STACK_SIZE_DOPER h in
		 let current' = ((current + p) - n) in
		 let max' = MAX current' max in
		 let valid' = (valid /\ (v:bool) /\ ((current + p) >= n) /\ (max >= current)) in
		 STACK_SIZE_BLK (max', current', valid') l)`;


val STACK_SIZE_CTL_STRUCTURE_def = Define
	`(STACK_SIZE_CTL_STRUCTURE (max, current, valid) (BLK l) =
		 STACK_SIZE_BLK (max, current, valid) l) /\
	 (STACK_SIZE_CTL_STRUCTURE (max, current, valid) (SC ir1 ir2) =
		 let (max', current', valid') = STACK_SIZE_CTL_STRUCTURE (max, current, valid) ir1 in
			STACK_SIZE_CTL_STRUCTURE (max', current', valid') ir2) /\
	 (STACK_SIZE_CTL_STRUCTURE (max, current, valid) (CJ c ir1 ir2) =
		 let (max1, current1, valid1) = STACK_SIZE_CTL_STRUCTURE (max, current, valid) ir1 in
		 let (max2, current2, valid2) = STACK_SIZE_CTL_STRUCTURE (max, current, valid) ir2 in
			(MAX max1 max2, current1, valid1 /\ valid2 /\ (current1 = current2))) /\
	 (STACK_SIZE_CTL_STRUCTURE (max, current, valid) (TR c ir) =
		 let (max', current', valid') = STACK_SIZE_CTL_STRUCTURE (max, current, valid) ir in
			(max', current', valid' /\ (current=current')))`


val STACK_SIZE_BLK___VALID = store_thm ("STACK_SIZE_BLK___VALID",
``!max current valid l max' current'. (STACK_SIZE_BLK (max, current, valid) l = (max', current', T)) ==> valid``,

Induct_on `l` THENL [
	SIMP_TAC std_ss [STACK_SIZE_BLK_def],

	SIMP_TAC std_ss [STACK_SIZE_BLK_def, LET_THM] THEN
	REPEAT GEN_TAC THEN
	`?p n v. STACK_SIZE_DOPER h = (p, n, v)` by METIS_TAC[PAIR] THEN
	POP_ASSUM MP_TAC THEN
	SIMP_TAC std_ss [] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC
])



(*
!ir max current valid max' current'. (STACK_SIZE_CTL_STRUCTURE (max, current, valid) ir =
	  (max', current', T)) ==>

	  (!st. (read st (REG 13) + n2w (4*(current - current')) -
									  n2w (4*(current' - current))) =
			  read (run_ir ir st) (REG 13))

restart()
Induct_on `ir` THENL [
	Induct_on `l` THENL [
		SIMP_TAC std_ss [SEMANTICS_OF_IR, STACK_SIZE_CTL_STRUCTURE_def,
			STACK_SIZE_BLK_def, WORD_ADD_0, WORD_SUB_RZERO],

		SIMP_TAC std_ss [SEMANTICS_OF_IR, STACK_SIZE_CTL_STRUCTURE_def,
			STACK_SIZE_BLK_def, LET_THM] THEN
		REPEAT GEN_TAC THEN
		`?p n v. STACK_SIZE_DOPER h = (p, n, v)` by METIS_TAC[PAIR] THEN
		ASM_SIMP_TAC std_ss [] THEN
		REPEAT STRIP_TAC THEN
		FULL_SIMP_TAC std_ss [STACK_SIZE_CTL_STRUCTURE_def] THEN
		IMP_RES_TAC STACK_SIZE_BLK___VALID THEN
		RES_TAC THEN
		`!st st'. (read (run_ir (BLK l) st) (REG 13) = read (run_ir (BLK l) st') (REG 13)) = (read st (REG 13) = read st' (REG 13))` by ALL_TAC THEN1 (
			POP_ASSUM (fn thm => MP_TAC (GSYM thm)) THEN
			SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL, word_sub_def]
		) THEN
		`!st M1 v. ~(M1 = R13) ==> (read (write st (toREG M1) v) (REG 13) =
											 read st (REG 13))` by ALL_TAC THEN1 (
			REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
			Cases_on `st` THEN
			SIMP_TAC std_ss [read_thm, toREG_def, write_thm,
				FAPPLY_FUPDATE_THM, COND_RATOR, COND_RAND,
				n2w_11, dimword_4] THEN
			Cases_on `M1` THEN
			SIMP_TAC std_ss [index_of_reg_def]
		) THEN
		Q.PAT_ASSUM `STACK_SIZE_DOPER h = X` (fn thm => MP_TAC (GSYM thm)) THEN
		Cases_on `h` THEN (
			 SIMP_TAC std_ss [STACK_SIZE_DOPER_def] THEN
			 REPEAT STRIP_TAC THEN
			 FULL_SIMP_TAC std_ss [mdecode_def]
		) THENL [
			Q.PAT_ASSUM `v = X` (fn thm => ALL_TAC) THEN
			Q.PAT_ASSUM `p = LENGTH l1` (fn thm => ALL_TAC) THEN
			Q.PAT_ASSUM `IS_SORTED_REG_LIST l1` (fn thm => ALL_TAC) THEN
			Q.PAT_ASSUM `STACK_SIZE_BLK X l = X'` (fn thm => ALL_TAC) THEN
			Induct_on `l1` THENL [
				ASM_SIMP_TAC list_ss [pushL_def, WORD_SUB_RZERO] THEN
				REPEAT STRIP_TAC THEN
				Cases_on `st` THEN
				REWRITE_TAC[read_thm, write_thm, FAPPLY_FUPDATE_THM],

				ASM_SIMP_TAC list_ss [pushL_def]
		]



			FULL_SIMP_TAC std_ss [mdecode_def],
			FULL_SIMP_TAC std_ss [mdecode_def],
			FULL_SIMP_TAC std_ss [mdecode_def],

			SIMP_TAC std_ss [STACK_SIZE_DOPER_def, mdecode_def, toREG_def],
			match [] ``read )write``


			SIMP_TAC std_ss [STACK_SIZE_DOPER_def],
			SIMP_TAC std_ss [STACK_SIZE_DOPER_def],
			SIMP_TAC std_ss [STACK_SIZE_DOPER_def],


			DB.find "mdecode"



match [] ``(let a = c in b a) = d``

CTL_STRUCTURE_11
 = (max, current, valid)) /\
	 ( (h::l) =
	    let (p, n, v) = STACK_SIZE_DOPER h in
		 let current' = ((current + p) - n) in
		 let max' = MAX current' max in
		 let valid' = (valid /\ (v:bool) /\ ((current + p) >= n) /\ (max >= current)) in
		 STACK_SIZE_BLOCK (max', current', valid') l)`


val blk1 = ``[MADD R0 R0 (MR R1); MADD R0 R0 (MR R1);
                     MADD R0 R0 (MR R2)]``
val blk2 = ``[MPUSH 13 [0; 1]; MMOV R3 (MR R2); MMOV R2 (MR R1);
                     MMOV R1 (MR R3)]``
val blk3 = ``[MPOP 13 [0; 1]; MMOV R3 (MR R2); MMOV R2 (MR R1);
                     MMOV R1 (MR R3)]``

EVAL ``STACK_SIZE_BLOCK (3,3,T) ^blk3``

 ``STACK_SIZE_BLOCK (0,0,T) ^blk3 = X``

ONCE_REWRITE_TAC [STACK_SIZE_BLOCK_def] THEN
SIMP_TAC list_ss [STACK_SIZE_DOPER_def, IS_SORTED_REG_LIST_def, LET_THM] THEN
ONCE_REWRITE_TAC [STACK_SIZE_BLOCK_def] THEN
SIMP_TAC list_ss [STACK_SIZE_DOPER_def, IS_SORTED_REG_LIST_def, LET_THM]


CTL_STRUCTURE_11
BLK




val IS_SORTED_REG_LIST___SNOC = store_thm ("IS_SORTED_REG_LIST___SNOC",
	``!l x. IS_SORTED_REG_LIST (SNOC x l) =
			  (IS_SORTED_REG_LIST l /\ ((l = []) \/ (LAST l < x)) /\ (x <= 15))``,

	Induct_on `l` THENL [
		SIMP_TAC list_ss [SNOC, IS_SORTED_REG_LIST_def],

		Cases_on `l` THENL [
			SIMP_TAC list_ss [SNOC, IS_SORTED_REG_LIST_def],

			FULL_SIMP_TAC list_ss [SNOC, IS_SORTED_REG_LIST_def] THEN
			PROVE_TAC[]
		]
	])



val IS_SORTED_REG_LIST___LAST = store_thm ("IS_SORTED_REG_LIST___LAST",
``!l. IS_SORTED_REG_LIST l ==>
		(EVERY (\n. n <= (LAST l)) l)``,

  INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
		SIMP_TAC list_ss [],

		SIMP_TAC list_ss [IS_SORTED_REG_LIST___SNOC, LAST] THEN
		SIMP_TAC list_ss [SNOC_APPEND, EVERY_APPEND] THEN
		REPEAT STRIP_TAC THENL [
			ASM_SIMP_TAC list_ss [],

			RES_TAC THEN
			FULL_SIMP_TAC arith_ss [EVERY_MEM] THEN
			REPEAT STRIP_TAC THEN
			RES_TAC THEN
			DECIDE_TAC
		]
	]);




val enc_REG_LIST_def = Define `
	enc_REG_LIST l = (FCP i. (MEM i l)):word16`

EVAL ``enc_REGISTER_LIST [2; 3; 5; 14]``




GEN_TAC THEN
DISJ_CASES_TAC (ISPEC ``l:num list`` SNOC_CASES) THENL [
	ASM_SIMP_TAC list_ss [GENLIST] THEN
	REPEAT (
		CONV_TAC (DEPTH_CONV numLib.num_CONV) THEN
		SIMP_TAC list_ss [GENLIST, fcpTheory.FCP_BETA, dimindex_16, FILTER_SNOC]
	),

restart()
!l. IS_SORTED_REG_LIST l ==>
(REGISTER_LIST (enc_REG_LIST l) = (MAP n2w l))

SIMP_TAC std_ss [enc_REG_LIST_def, MEM, armTheory.REGISTER_LIST_def] THEN
REPEAT STRIP_TAC THEN
`(EVERY (\n. n < 16) l)` by PROVE_TAC[IS_SORTED_REG_LIST___EL_SIZE] THEN
Q.ABBREV_TAC `max = 16` THEN
`max <= 16` by FULL_SIMP_TAC arith_ss [] THEN
Q.PAT_ASSUM `Abbrev X` (fn thm => ALL_TAC) THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SPEC_TAC (``l:num list``,``l:num list``) THEN
Induct_on `max` THENL [
   Cases_on `l` THEN SIMP_TAC list_ss [GENLIST],

   GEN_TAC THEN
   DISJ_CASES_TAC (ISPEC ``l:num list`` SNOC_CASES) THENL [
		ASM_SIMP_TAC list_ss [] THEN
		`!x. (x <= 16) ==> (FILTER FST (GENLIST (\i. ((FCP i. F):word16 %% i,(n2w i):word4)) x) = [])` by ALL_TAC THEN1 (
			REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
			Induct_on `x` THENL [
				SIMP_TAC list_ss [GENLIST],
				ASM_SIMP_TAC list_ss [GENLIST, FILTER_SNOC, fcpTheory.FCP_BETA, dimindex_16]
			]
		) THEN
		ASM_SIMP_TAC std_ss [],

		FULL_SIMP_TAC list_ss [IS_SORTED_REG_LIST___SNOC, EVERY_APPEND, SNOC_APPEND] THEN
		REPEAT STRIP_TAC THENL [
			FULL_SIMP_TAC list_ss [] THEN
			Q.PAT_ASSUM `SUC max <= 16` MP_TAC THEN
			Q.PAT_ASSUM `x < SUC max` MP_TAC THEN
			Q.ABBREV_TAC `max' = SUC max` THEN
			REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
			SPEC_TAC (``x:num``,``x:num``) THEN
			Induct_on `max'` THENL [
				SIMP_TAC std_ss [],

				REPEAT STRIP_TAC THEN
				ASM_SIMP_TAC list_ss [GENLIST, FILTER_SNOC, fcpTheory.FCP_BETA, dimindex_16] THEN
				Cases_on `max' = x` THENL [
					ASM_SIMP_TAC list_ss [MAP_SNOC, SNOC_11, GSYM SNOC] THEN
					`!x y. ((x <= 16) /\ (x <= y)) ==> (FILTER FST (GENLIST (\i. ((FCP i. i = y):word16 %% i,(n2w i):word4)) x) = [])` by ALL_TAC THEN1 (
						REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
						Induct_on `x` THENL [
							SIMP_TAC list_ss [GENLIST],
							ASM_SIMP_TAC list_ss [GENLIST, FILTER_SNOC, fcpTheory.FCP_BETA, dimindex_16]
						]
					) THEN

					`x <= 16` by DECIDE_TAC THEN
					POP_ASSUM MP_TAC THEN
					REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
					Induct_on `x` THENL [
						SIMP_TAC list_ss [GENLIST],
						ASM_SIMP_TAC list_ss [GENLIST, FILTER_SNOC, fcpTheory.FCP_BETA, dimindex_16] THEN
						REPEAT STRIP_TAC THEN
						FULL_SIMP_TAC arith_ss []
			]


	REPEAT (
		CONV_TAC (DEPTH_CONV numLib.num_CONV) THEN
		SIMP_TAC list_ss [GENLIST, fcpTheory.FCP_BETA, dimindex_16, FILTER_SNOC]
	),



	Cases SNOC_CASES THENL SIMP_TAC list_ss [GENLIST]
	REPEAT STRIP_TAC THEN

	Cases_on `EVERY (\n. n < max) l` THEN1 (
		FULL_SIMP_TAC arith_ss [GENLIST, FILTER_SNOC, fcpTheory.FCP_BETA, dimindex_16]




ONCE_REWRITE_TAC [REDEPTH_CONV numLib.num_CONV ``16``] THEN
REWRITE_TAC[GENLIST] THEN
SIMP_TAC list_ss [fcpTheory.FCP_BETA, dimindex_16] THEN
REWRITE_TAC [SNOC] THEN

Induct_on `l` THENL [
	SIMP_TAC list_ss []


DB.find "GENLIST"
DB.find "FCP"
REGISTER_LIST



match [] ``LDM``

ARM_LDM*)

val PRE_TRANS_OPT_def = Define `PRE_TRANS_OPT = transfer_options F F F`

val DOPER2INSTRUCTION_def = Define `
  (DOPER2INSTRUCTION (MPOP base regL) =
      LDM AL T PRE_TRANS_OPT (n2w base) (reg_bitmap (MAP n2w regL))) /\
  (DOPER2INSTRUCTION (MPUSH base regL) =
      STM AL T PRE_TRANS_OPT (n2w base) (reg_bitmap (MAP n2w regL))) /\
  (DOPER2INSTRUCTION (MMOV dst src) =
      MOV AL F (MREG2REG dst) (MEXP2addr_model src)) /\
  (DOPER2INSTRUCTION (MADD dst src1 src2) =
      ADD AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MSUB dst src1 src2) =
      SUB AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MRSB dst src1 src2) =
      RSB AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MMUL dst src1 src2_reg) =
      MUL AL F (MREG2REG dst) (MREG2REG src1) (MREG2REG src2_reg)) /\
  (DOPER2INSTRUCTION (MAND dst src1 src2) =
      AND AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MORR dst src1 src2) =
      ORR AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MEOR dst src1 src2) =
      EOR AL F (MREG2REG dst) (MREG2REG src1) (MEXP2addr_model src2)) /\
  (DOPER2INSTRUCTION (MLSL dst src2_reg src2_num) =
      MOV AL F (MREG2REG dst) (Dp_shift_immediate (LSL (MREG2REG src2_reg)) src2_num)) /\
  (DOPER2INSTRUCTION (MLSR dst src2_reg src2_num) =
      if (src2_num = 0w) then
        (*avoid special case rrx*)
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (LSL (MREG2REG src2_reg)) src2_num)
      else
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (LSR (MREG2REG src2_reg)) src2_num)) /\
  (DOPER2INSTRUCTION (MASR dst src2_reg src2_num) =
      if (src2_num = 0w) then
        (*avoid special case rrx*)
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (LSL (MREG2REG src2_reg)) src2_num)
      else
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (ASR (MREG2REG src2_reg)) src2_num)) /\
  (DOPER2INSTRUCTION (MROR dst src2_reg src2_num) =
      if (src2_num = 0w) then
        (*avoid special case rrx*)
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (LSL (MREG2REG src2_reg)) src2_num)
      else
        MOV AL F (MREG2REG dst) (Dp_shift_immediate (ROR (MREG2REG src2_reg)) src2_num))
  `;



val MREG2register_def = Define
  `MREG2register m r =
		num2register (mode_reg2num m (MREG2REG r))`


val REGS_EQUIVALENT_def = Define
  `REGS_EQUIVALENT m registers regs =
    (!r. ((regs ' (MREG2REG r)) = (registers (num2register (mode_reg2num m (MREG2REG r))))))`

val mode_reg2num_11 = store_thm ("mode_reg2num_11",
``!m v w.
(mode_reg2num m v = mode_reg2num m w) = (v = w)``,

REPEAT GEN_TAC THEN EQ_TAC THENL [
	Cases_on `m` THEN
	SIMP_TAC std_ss [armTheory.mode_reg2num_def, armTheory.USER_def, LET_THM, w2n_11,
		armTheory.mode_case_def, armTheory.mode_distinct] THENL [

		Cases_on `(w2n v = 15) \/ (w2n v < 8)` THEN Cases_on `(w2n w = 15) \/ (w2n w < 8)` THEN
		FULL_SIMP_TAC arith_ss [GSYM w2n_11],

		ALL_TAC,
		ALL_TAC,
		ALL_TAC,
		ALL_TAC
	] THEN (
		Cases_on `(w2n v = 15) \/ (w2n v < 13)` THEN Cases_on `(w2n w = 15) \/ (w2n w < 13)` THEN
		FULL_SIMP_TAC arith_ss [GSYM w2n_11]
	),

	SIMP_TAC std_ss []
]);

val mode_reg2num___PC = store_thm ("mode_reg2num___PC",
``!m r. (mode_reg2num m r = 15) = (r = 15w)``,

REPEAT GEN_TAC THEN
`mode_reg2num m 15w = 15` by EVAL_TAC THEN
PROVE_TAC[mode_reg2num_11]);






val MREG_NOT_PC = store_thm ("MREG_NOT_PC",
  ``(!r. ~(MREG2REG r = 15w)) /\ (!r m. ~(MREG2register m r = r15))``,

	SIMP_TAC std_ss [GSYM FORALL_AND_THM, MREG2REG_def,
		MREG2register_def, GSYM armTheory.num2register_thm] THEN
   Cases_on `r` THEN(
		SIMP_TAC std_ss [index_of_reg_def, arm_evalTheory.mode_reg2num_lt, armTheory.num2register_11, mode_reg2num___PC] THEN
		WORDS_TAC
	));


val DECODE_MEXP_def = Define `
  (DECODE_MEXP m (MR r) regs = regs (MREG2register m r)) /\
  (DECODE_MEXP m (MC s c) regs = ((w2w c):word32 #>> (2 * w2n s)))`

val index_of_reg_lt = store_thm ("index_of_reg_lt",
  ``!r. index_of_reg r < 15``,
  Cases_on `r` THEN EVAL_TAC)

val index_of_reg_11 = store_thm ("index_or_reg_11",
  ``!r r'. ((index_of_reg r = index_of_reg r') = (r = r'))``,
  Cases_on `r` THEN Cases_on `r'` THEN EVAL_TAC);

val MREG2REG_11 = store_thm ("MREG2REG_11",
  ``!r r'. ((MREG2REG r = MREG2REG r') = (r = r'))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    ALL_TAC,
    SIMP_TAC std_ss []
  ] THEN
  SIMP_TAC std_ss [MREG2REG_def, n2w_11, dimword_4] THEN
  `(index_of_reg r < 15) /\ (index_of_reg r' < 15)` by REWRITE_TAC[index_of_reg_lt] THEN
  ASM_SIMP_TAC arith_ss [index_of_reg_11]);


val MREG2addr_model_thm = store_thm ("MREG2addr_model_thm",
``!mexp regs mode C.
  (SND (ADDR_MODE1 regs mode C
    (IS_DP_IMMEDIATE (MEXP2addr_model mexp))
    ((11 >< 0) (addr_mode1_encode (MEXP2addr_model mexp)))) = DECODE_MEXP mode mexp regs)``,

REPEAT GEN_TAC THEN
Cases_on `mexp` THENL [
  SIMP_TAC std_ss [MEXP2addr_model_def, arm_evalTheory.IS_DP_IMMEDIATE_def,
                   armTheory.ADDR_MODE1_def,
                   arm_evalTheory.shift_immediate_enc,
                   instructionTheory.shift_case_def,
                   arm_evalTheory.shift_immediate_shift_register,
                   armTheory.REG_READ_def,
                   armTheory.LSL_def, MREG_NOT_PC,
                   LET_THM,
						 MREG2register_def,
                   DECODE_MEXP_def],

  SIMP_TAC std_ss [MEXP2addr_model_def, arm_evalTheory.IS_DP_IMMEDIATE_def,
                   armTheory.ADDR_MODE1_def,
                   arm_evalTheory.immediate_enc,
                   armTheory.ROR_def, DECODE_MEXP_def] THEN
  SUBGOAL_TAC `(2w:word8 * w2w c) = n2w (2*w2n c)` THEN1 (
    REWRITE_TAC [word_mul_def] THEN
    WORDS_TAC THEN
    `w2n c < 16` by METIS_TAC [w2n_lt, dimword_4] THEN
    ASM_SIMP_TAC arith_ss[]
  ) THEN
  ASM_SIMP_TAC std_ss [w2w_def, n2w_w2n, w2n_n2w, dimword_8, dimword_5] THEN
  Cases_on `n2w (2 * w2n c) = 0w:word8` THENL [
    SUBGOAL_TAC `2* w2n c = 0` THEN1 (
      `w2n (n2w:num->word8 (2 * w2n c)) = w2n (0w:word8)` by PROVE_TAC[] THEN
      UNDISCH_HD_TAC THEN
      WORDS_TAC THEN
      `w2n c < 16` by METIS_TAC [w2n_lt, dimword_4] THEN
      ASM_SIMP_TAC arith_ss[]
    ) THEN
    ASM_SIMP_TAC std_ss [armTheory.LSL_def] THEN
    PROVE_TAC[ROR_CYCLE, MULT],

    `w2n c < 16` by METIS_TAC [w2n_lt, dimword_4] THEN
    ASM_SIMP_TAC arith_ss []
  ]
]);


val FETCH_PC___PC_WRITE = store_thm ("FETCH_PC___PC_WRITE",
	``!registers v. FETCH_PC (REG_WRITE registers usr 15w v) = v``,

	EVAL_TAC THEN
	REWRITE_TAC [armTheory.num2register_thm]);


val DECODE_SHIFT_def = Define `
  (DECODE_SHIFT m (LSL:word4->shift r) (c:word5) (regs:register->word32) = ((regs (num2register (mode_reg2num m r))) << w2n c)) /\
  (DECODE_SHIFT m (LSR r) c regs = ((regs (num2register (mode_reg2num m r))) >>> w2n c)) /\
  (DECODE_SHIFT m (ASR r) c regs = ((regs (num2register (mode_reg2num m r))) >> w2n c)) /\
  (DECODE_SHIFT m (ROR r) c regs = ((regs (num2register (mode_reg2num m r))) #>> w2n c))`;



val WELL_FORMED_SHIFT_def = Define `
  (WELL_FORMED_SHIFT (ROR:word4->shift r) c = ~(c = 0w) /\ ~(r = 15w)) /\
  (WELL_FORMED_SHIFT (ASR r) c = ~(c = 0w) /\ ~(r = 15w)) /\
  (WELL_FORMED_SHIFT (LSR r) c = ~(c = 0w) /\ ~(r = 15w)) /\
  (WELL_FORMED_SHIFT (LSL r) c = ~(r = 15w))`;


val STATE_ARM_MEM_EVAL = save_thm ("STATE_ARM_MEM_EVAL",
   let
      val def1 = (Q.ISPEC `NO_CP:'a coproc` (SIMP_RULE std_ss [Once (GSYM FORALL_AND_THM)] systemTheory.STATE_ARM_MMU_def));
      val def2 = REWRITE_RULE [GSYM systemTheory.NEXT_ARM_MEM_def, GSYM systemTheory.STATE_ARM_MEM_def] def1
   in
      def2
   end)

val STATE_ARM_MEM_SPLIT = store_thm ("STATE_ARM_MEM_SPLIT",
  ``(!t1 t2 s. STATE_ARM_MEM (t1 + t2) s = (STATE_ARM_MEM t1 (STATE_ARM_MEM t2 s)))``,

  Induct_on `t1` THENL [
    SIMP_TAC std_ss [STATE_ARM_MEM_EVAL],

    REPEAT GEN_TAC THEN
    `SUC t1 + t2 = SUC (t1 + t2)` by DECIDE_TAC THEN
    FULL_SIMP_TAC std_ss [STATE_ARM_MEM_EVAL]
  ]);



val STATE_ARM_MEM_SPLIT___SYM = store_thm ("STATE_ARM_MEM_SPLIT___SYM",
  ``(!t1 t2 s. STATE_ARM_MEM (t1 + t2) s = (STATE_ARM_MEM t2 (STATE_ARM_MEM t1 s)))``,

  SIMP_TAC arith_ss [GSYM STATE_ARM_MEM_SPLIT]);


val DECODE_SHIFT_thm = store_thm ("DECODE_SHIFT_thm",
``!s c regs mode C.
  WELL_FORMED_SHIFT s c ==>
  (SND (ADDR_MODE1 regs mode C
    (IS_DP_IMMEDIATE (Dp_shift_immediate s c))
    ((11 >< 0) (addr_mode1_encode (Dp_shift_immediate s c)))) = DECODE_SHIFT mode s c regs)``,

  REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [arm_evalTheory.IS_DP_IMMEDIATE_def,
                   armTheory.ADDR_MODE1_def,
                   arm_evalTheory.shift_immediate_enc,
                   instructionTheory.shift_case_def,
                   arm_evalTheory.shift_immediate_shift_register] THEN
  Cases_on `c = 0w` THEN ASM_REWRITE_TAC[] THENL [
    Cases_on `s` THENL [
      FULL_SIMP_TAC std_ss [instructionTheory.shift_case_def,
        armTheory.LSL_def, DECODE_SHIFT_def, WELL_FORMED_SHIFT_def] THEN
      WORDS_TAC THEN
      ASM_SIMP_TAC std_ss [SHIFT_ZERO, armTheory.REG_READ_def,
        WELL_FORMED_SHIFT_def, armTheory.mode_reg2num_def, LET_THM],

      FULL_SIMP_TAC std_ss [WELL_FORMED_SHIFT_def],
      FULL_SIMP_TAC std_ss [WELL_FORMED_SHIFT_def],
      FULL_SIMP_TAC std_ss [WELL_FORMED_SHIFT_def]
    ],

    SUBGOAL_TAC `~(w2w c = 0w:word8) /\ (w2n ((w2w c):word8) = w2n c)` THEN1 (
      WORDS_TAC THEN
      `w2n c < 32` by METIS_TAC [w2n_lt, dimword_5] THEN
      ASM_SIMP_TAC arith_ss [w2n_eq_0]
    ) THEN
    SUBGOAL_TAC `!c. ~(c = 15w) ==>
                 (REG_READ regs mode c =
                 regs (num2register (mode_reg2num mode c)))` THEN1 (
      ASM_SIMP_TAC std_ss [armTheory.REG_READ_def,
        LET_THM]
    ) THEN

    Cases_on `s` THEN (
      FULL_SIMP_TAC std_ss [instructionTheory.shift_case_def,
        armTheory.LSL_def, armTheory.LSR_def, armTheory.ASR_def,
        armTheory.ROR_def,
        DECODE_SHIFT_def, WELL_FORMED_SHIFT_def]
    )
  ]);


val DECODE_MEXP_thm = store_thm ("DECODE_MEXP_thm",
  ``!registers regs m mem M0.
  REGS_EQUIVALENT m registers regs ==>
  (read (regs,mem) (toEXP M0) = DECODE_MEXP m M0 registers)``,

  Cases_on `M0` THENL [
    SIMP_TAC std_ss [read_thm, toEXP_def, toREG_def, DECODE_MEXP_def,
      REGS_EQUIVALENT_def, MREG2register_def, MREG2REG_def] THEN
	 PROVE_TAC[index_of_reg_lt],

    SIMP_TAC std_ss [read_thm, toEXP_def, toREG_def, DECODE_MEXP_def]
  ]);


val MREG2REG_thm = store_thm ("MREG2REG_thm",
  ``!registers regs mem m M.
    (REGS_EQUIVALENT m registers regs) ==>
    (REG_READ registers m (MREG2REG M) = read (regs, mem) (toREG M))``,

    SIMP_TAC std_ss [armTheory.REG_READ_def, MREG_NOT_PC,
      LET_THM, toREG_def, read_thm,
      REGS_EQUIVALENT_def, MREG2REG_def] THEN
    PROVE_TAC[index_of_reg_lt]);

val REGS_EQUIVALENT___WRITE_PC = store_thm ("REGS_EQUIVALENT___WRITE_PC",
``!registers regs m m' v.
  REGS_EQUIVALENT m (REG_WRITE registers m' 15w v) regs =
  REGS_EQUIVALENT m registers regs``,

SIMP_TAC std_ss [REGS_EQUIVALENT_def, armTheory.REG_WRITE_def] THEN
REPEAT GEN_TAC THEN
FORALL_EQ_STRIP_TAC THEN
MATCH_MP_TAC (prove (``((b:word32) = (c:word32)) ==> ((a = b) = (a = c))``, PROVE_TAC[])) THEN
SIMP_TAC std_ss [combinTheory.UPDATE_def] THEN
`num2register (mode_reg2num m' 15w) = r15` by (EVAL_TAC THEN REWRITE_TAC[armTheory.num2register_thm]) THEN
SUBGOAL_TAC `~(r15 = num2register (mode_reg2num m (MREG2REG r)))` THEN1 (
	SIMP_TAC arith_ss [GSYM armTheory.num2register_thm, armTheory.num2register_11, arm_evalTheory.mode_reg2num_lt] THEN
	ONCE_REWRITE_TAC [prove (``15 = mode_reg2num m 15w``, EVAL_TAC)] THEN
	SIMP_TAC arith_ss [mode_reg2num_11, MREG2REG_def, n2w_11, dimword_4] THEN
	`index_of_reg r < 15` by REWRITE_TAC[index_of_reg_lt] THEN
   ASM_SIMP_TAC arith_ss []
) THEN
ASM_REWRITE_TAC[]);





val REGS_EQUIVALENT___INC_PC = store_thm ("REGS_EQUIVALENT___INC_PC",
``!registers regs m.
  REGS_EQUIVALENT m (INC_PC registers) regs =
  REGS_EQUIVALENT m registers regs``,

SIMP_TAC std_ss [arm_evalTheory.INC_PC, REGS_EQUIVALENT___WRITE_PC]);


val REGS_EQUIVALENT___UPDATE = store_thm ("REGS_EQUIVALENT___UPDATE",
``!registers regs M x.
  REGS_EQUIVALENT m registers regs ==>
  REGS_EQUIVALENT m ((MREG2register m M =+ x) registers)
                  (regs |+ (MREG2REG M, x))``,

SIMP_TAC arith_ss [REGS_EQUIVALENT_def, combinTheory.UPDATE_def, FAPPLY_FUPDATE_THM,
  MREG2register_def, MREG2REG_def, armTheory.num2register_11, arm_evalTheory.mode_reg2num_lt, mode_reg2num_11, n2w_11, dimword_4] THEN
REPEAT STRIP_TAC THEN
`index_of_reg M < 15` by PROVE_TAC[index_of_reg_lt] THEN
ASM_SIMP_TAC arith_ss [] THEN PROVE_TAC[]);


(*a very specialised tactic for data operations which get a register and an addr_mode1*)

fun doper_reg_reg_addr_mode1 thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] thm) THEN
  Q_SPECL_NO_ASSUM 0 [`state_old`, `F`, `AL:condition`, `MREG2REG M0`, `MREG2REG M'`, `(MEXP2addr_model M1)`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    FULL_SIMP_TAC std_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
      armTheory.condition_case_def]
  ) THEN
  FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds,
	 REG_OWRT_ALL] THEN WEAKEN_HD_TAC THEN

  Q.PAT_UNDISCH_TAC `(reg',mem') = mdecode (reg, mem) X` THEN
  ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, MREG2addr_model_thm,
                       LET_THM, GSYM MREG2register_def,
                       mdecode_def] THEN
  `read (reg,mem) (toEXP M1) = DECODE_MEXP m M1 state_old.registers` by
    PROVE_TAC[DECODE_MEXP_thm] THEN
  `read (reg,mem) (toREG M0) = REG_READ state_old.registers m (MREG2REG M0)` by
    PROVE_TAC[MREG2REG_thm] THEN
  ASM_SIMP_TAC std_ss [write_thm, toREG_def] THEN
  REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC std_ss [REGS_EQUIVALENT___INC_PC, REGS_EQUIVALENT___UPDATE,
		GSYM MREG2REG_def],
    SIMP_TAC std_ss [armTheory.INC_PC_def,
                     armTheory.FETCH_PC_def,
                     combinTheory.UPDATE_def,
                     MREG_NOT_PC]
  ];

(*a very specialised tactic for shift operations*)
fun doper_shift s_term =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_MOV) THEN
  Q_SPECL_NO_ASSUM 0 [`state_old`, `F`, `AL:condition`, `MREG2REG M'`, `MREG2REG M'`] THEN
  Cases_on `c = 0w` THENL [
    SPEC_NO_ASSUM 1 ``Dp_shift_immediate (LSL (MREG2REG M0)) c``,

    SPEC_NO_ASSUM 1 (list_mk_comb (``Dp_shift_immediate``,
                                   [mk_comb (s_term, ``MREG2REG M0``),
                                    ``c:word5``]))
  ] THEN (
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      FULL_SIMP_TAC std_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
        armTheory.condition_case_def]
    ) THEN
    FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds, REG_OWRT_ALL] THEN WEAKEN_HD_TAC THEN

    `read (reg,mem) (toREG M0) = REG_READ state_old.registers m (MREG2REG M0)` by
      PROVE_TAC[MREG2REG_thm] THEN
    Q.PAT_UNDISCH_TAC `(reg',mem') = mdecode (reg, mem) X` THEN
    ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, DECODE_SHIFT_thm,
                        WELL_FORMED_SHIFT_def, MREG_NOT_PC,
                        DECODE_SHIFT_def, SHIFT_ZERO, word_0_n2w,
                        LET_THM, GSYM MREG2register_def,
                        mdecode_def, toREG_def, write_thm,
                        systemTheory.arm_sys_state_accfupds,
                        armTheory.REG_READ_def,
                        REGS_EQUIVALENT___INC_PC,
                        REGS_EQUIVALENT___UPDATE,
							   GSYM MREG2REG_def] THEN
    SIMP_TAC std_ss [armTheory.INC_PC_def,
                     armTheory.FETCH_PC_def,
                     combinTheory.UPDATE_def,
                     MREG_NOT_PC]
  )



val DOPER2INSTRUCTION_NO_MEM_thm = store_thm ("DOPER2INSTRUCTION_NO_MEM_thm",
``
!oper reg mem reg' mem' m
 state_old state_new.
(~(IS_MEMORY_DOPER oper) /\ (IS_WELL_FORMED_DOPER oper) /\
 (state_old.memory ((31 >< 2) (state_old.registers r15)) =
            enc (DOPER2INSTRUCTION oper)) /\
 (~state_old.undefined) /\
 (Abbrev (m = (DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs))))) /\
 ((reg', mem') = mdecode (reg,mem) oper) /\
 (state_new = NEXT_ARM_MEM state_old) /\
 (REGS_EQUIVALENT m state_old.registers reg)) ==>

 ((REGS_EQUIVALENT m state_new.registers reg') /\
  (mem' = mem) /\ (state_new.memory = state_old.memory) /\
  (~state_new.undefined) /\
  (state_new.psrs = state_old.psrs) /\
  (state_new.cp_state = state_old.cp_state) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
  (FETCH_PC state_new.registers = FETCH_PC state_old.registers + 4w)
  )``,

SIMP_TAC std_ss [] THEN
Cases_on `oper` THEN
REWRITE_TAC[IS_MEMORY_DOPER_def, IS_WELL_FORMED_DOPER_def, DOPER2INSTRUCTION_def,
	owrt_visible_regs_def, state_mode_def] THENL [

  (*MOV*)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_MOV) THEN
  Q_SPECL_NO_ASSUM 0 [`state_old`, `F`, `AL:condition`, `MREG2REG M'`, `MREG2REG M'`, `(MEXP2addr_model M0)`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    FULL_SIMP_TAC std_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
      armTheory.condition_case_def]
  ) THEN
  FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds,systemTheory.arm_sys_state_accessors,
		REG_OWRT_ALL] THEN

  `read (reg,mem) (toEXP M0) = DECODE_MEXP m M0 state_old.registers` by
    PROVE_TAC[DECODE_MEXP_thm] THEN
  Q.PAT_UNDISCH_TAC `(reg',mem') = mdecode (reg, mem) X` THEN
  ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, MREG2addr_model_thm,
                       GSYM MREG2register_def,
                       mdecode_def, toREG_def, write_thm] THEN
  REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC std_ss [REGS_EQUIVALENT___INC_PC, REGS_EQUIVALENT___UPDATE, GSYM MREG2REG_def],
    SIMP_TAC std_ss [armTheory.INC_PC_def,
                     armTheory.FETCH_PC_def,
                     MREG_NOT_PC,
                     combinTheory.UPDATE_def]
  ],


  doper_reg_reg_addr_mode1 ARM_ADD,
  doper_reg_reg_addr_mode1 ARM_SUB,
  doper_reg_reg_addr_mode1 ARM_RSB,

  (*MUL*)
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_MUL) THEN
  Q_SPECL_NO_ASSUM 0 [`state_old`, `F`, `AL:condition`, `MREG2REG M1`, `MREG2REG M0`, `MREG2REG M'`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    FULL_SIMP_TAC arith_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
      armTheory.condition_case_def, MREG2REG_11]
  ) THEN
  FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds, REG_OWRT_ALL] THEN WEAKEN_HD_TAC THEN

  Q.PAT_UNDISCH_TAC `(reg',mem') = mdecode (reg, mem) X` THEN
  ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, MREG2addr_model_thm,
                       LET_THM, GSYM MREG2register_def,
                       mdecode_def] THEN
  `read (reg,mem) (toREG M0) = REG_READ state_old.registers m (MREG2REG M0)` by
    PROVE_TAC[MREG2REG_thm] THEN
  `read (reg,mem) (toREG M1) = REG_READ state_old.registers m (MREG2REG M1)` by
    PROVE_TAC[MREG2REG_thm] THEN
  ASM_SIMP_TAC std_ss [write_thm, toREG_def] THEN
  REPEAT STRIP_TAC THENL [
    ASM_SIMP_TAC std_ss [REGS_EQUIVALENT___INC_PC, REGS_EQUIVALENT___UPDATE, GSYM MREG2REG_def],
    SIMP_TAC std_ss [armTheory.INC_PC_def,
                     armTheory.FETCH_PC_def,
                     combinTheory.UPDATE_def,
                     MREG_NOT_PC]
  ],


  doper_reg_reg_addr_mode1 ARM_AND,
  doper_reg_reg_addr_mode1 ARM_ORR,
  doper_reg_reg_addr_mode1 ARM_EOR,

  doper_shift ``LSL:word4->shift``,
  doper_shift ``LSR:word4->shift``,
  doper_shift ``ASR:word4->shift``,
  doper_shift ``ROR:word4->shift``
]);

val DOPER2INSTRUCTION_thm = save_thm ("DOPER2INSTRUCTION_thm", DOPER2INSTRUCTION_NO_MEM_thm);

val MEMORY_SLICE_def = Define `
	MEMORY_SLICE (base, length) =
		(MAP (\off. base - n2w off) (LIST_COUNT length))`

val MEM_EQUIV_EXCEPT_SLICE_def = Define `
	MEM_EQUIV_EXCEPT_SLICE (base, length) (mem, mem') =
		!slice. (slice = (MEMORY_SLICE (base, length))) ==>
		(((FDOM mem) UNION (LIST_TO_SET slice) =
        (FDOM mem') UNION (LIST_TO_SET slice)) /\
		 (!l. ~(MEM l slice) ==> (mem ' l = mem' ' l)))`;


val REGS_EQUIVALENT_MEM_def = Define `
	REGS_EQUIVALENT_MEM m (offset, length) (registers, memory) (regs, mem) =
	REGS_EQUIVALENT m registers regs /\
	(!l. (MEM l (MEMORY_SLICE ((MEM_ADDR (regs ' 13w) + offset), length)) ==>
				  (mem ' l =  memory l)))`


val REGS_EQUIVALENT_MEM___NO_MEM =
	store_thm ("REGS_EQUIVALENT_MEM___NO_MEM",
``!m offset registers memory regs mem.
REGS_EQUIVALENT_MEM m (offset, 0) (registers, memory) (regs, mem) =
REGS_EQUIVALENT m registers regs``,

SIMP_TAC list_ss [REGS_EQUIVALENT_MEM_def, LIST_COUNT_def, MEMORY_SLICE_def]);


val REGS_EQUIVALENT___SP =
	store_thm ("REGS_EQUIVALENT___SP",
	``!m registers reg. REGS_EQUIVALENT m registers reg ==>
							  (registers (num2register (mode_reg2num m 13w)) = reg ' 13w)``,

	SIMP_TAC std_ss [REGS_EQUIVALENT_def] THEN
	REPEAT STRIP_TAC THEN
	POP_ASSUM (fn thm => MP_TAC (Q.SPEC `R13` thm)) THEN
	SIMP_TAC std_ss [MREG2REG_def, index_of_reg_def]);


val pushL_mem_def = Define `pushL_mem (reg, mem) r off l =
FST (FOLDL (\(mem',i) reg'. (mem' |+
                   (MEM_ADDR (reg ' (n2w r)) - n2w i,reg ' (n2w reg')),
                   i + 1)) (mem,off) (REVERSE l))`


val pushL_thm = store_thm ("pushL_thm",
``!l reg mem r.
pushL (reg, mem) r l = (reg |+ (n2w r, reg ' (n2w r) - n2w (4*(LENGTH l))),
								pushL_mem (reg, mem) r 0 l)``,


`!l reg mem reg' mem' r init.
(FOLDL (\(st1,i) reg''. (write st1 (MEM (r,NEG i)) (read (reg',mem') reg''),
                        i + 1)) ((reg,mem),init) (REVERSE (MAP REG l))) =
(FOLDL (\(st1,i) reg''. (write st1 (MEM (r,NEG i)) (reg' ' (n2w reg'')),
                        i + 1)) ((reg,mem),init) (REVERSE l))` by ALL_TAC THEN1
(
	INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
		SIMP_TAC list_ss [],
		ASM_SIMP_TAC list_ss [REVERSE_SNOC, MAP_SNOC, read_thm, write_thm]
	]
) THEN


`!l reg mem r init.
(FOLDL (\(st1,i) reg'. (write st1 (MEM (r,NEG i)) (read (reg,mem) reg'),
                        i + 1)) ((reg,mem),init) (REVERSE (MAP REG l))) =

let (mem, i) =
	(FOLDL (\(mem',i) reg'. (mem' |+ ((MEM_ADDR (reg ' (n2w r)) - (n2w i)), reg ' (n2w reg')), i + 1)) (mem, init) (REVERSE l)) in
((reg, mem), i)` by ALL_TAC THEN1 (
	ASM_SIMP_TAC std_ss [] THEN
	POP_ASSUM (fn thm => ALL_TAC) THEN
	INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
		SIMP_TAC list_ss [LET_THM],
		ASM_SIMP_TAC list_ss [MAP_SNOC, REVERSE_SNOC, write_thm, read_thm, LET_THM]
	]
) THEN
REWRITE_TAC[pushL_mem_def] THEN
INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
	SIMP_TAC list_ss [pushL_def, WORD_SUB_RZERO, read_thm, write_thm],

	FULL_SIMP_TAC list_ss [pushL_def, LET_THM] THEN
	PairRules.PBETA_TAC THEN
	SIMP_TAC std_ss [write_thm, read_thm]
])



val pushL_mem_thm = store_thm ("pushL_mem_thm", ``
	(!reg mem r off. (pushL_mem (reg, mem) r off [] = mem)) /\
	(!reg mem r off h l. (pushL_mem (reg, mem) r off (SNOC h l) =
							pushL_mem (reg, mem |+ ((MEM_ADDR (reg ' (n2w r)) - (n2w off)), reg ' (n2w h))) r (SUC off) l))``,

	SIMP_TAC list_ss [pushL_mem_def, FOLDL_APPEND] THEN
	REPEAT GEN_TAC THEN
	AP_TERM_TAC THEN
	Q.SPEC_TAC (`mem`, `mem`) THEN
	Q.SPEC_TAC (`reg`, `reg`) THEN
	Q.SPEC_TAC (`off`, `off`) THEN
	Q.SPEC_TAC (`h`, `h`) THEN
	Q.SPEC_TAC (`l`, `l`) THEN
	INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
		SIMP_TAC list_ss [SNOC],
		ASM_SIMP_TAC list_ss [FOLDL_APPEND, Once REVERSE_SNOC, SUC_ONE_ADD]
	])

(*
val DOPER2INSTRUCTION_thm = store_thm ("DOPER2INSTRUCTION_thm",
``
!oper reg mem reg' mem' m off stack_size
 state_old state_new sp.
(((p,n,T) = STACK_SIZE_DOPER oper) /\
 (state_old.memory ((31 >< 2) (state_old.registers r15)) =
            enc (DOPER2INSTRUCTION oper)) /\
 (~state_old.undefined) /\
 (stack_size >= n) /\
 (Abbrev (m = (DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs))))) /\
 (sp = num2register (mode_reg2num m 13w)) /\
 ((reg', mem') = mdecode (reg,mem) oper) /\
 (state_new = NEXT_ARM_MEM state_old) /\
 (REGS_EQUIVALENT_MEM m (off, stack_size) (state_old.registers, state_old.memory) (reg, mem))) ==>

 ((REGS_EQUIVALENT_MEM m (off + n2w n - n2w p, stack_size + p) (state_new.registers, state_new.memory) (reg', mem')) /\
  (MEM_EQUIV_EXCEPT_SLICE (MEM_ADDR (state_new.registers sp), p) (mem, mem')) /\
  (~state_new.undefined) /\
  (state_new.psrs = state_old.psrs) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
  (FETCH_PC state_new.registers = FETCH_PC state_old.registers + 4w)
  )``,
restart()


GEN_TAC THEN
Cases_on `~IS_MEMORY_DOPER oper` THENL [
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	IMP_RES_TAC (GSYM VALID_STACK_SIZE_DOPER___IMPLIES___WELL_FORMED) THEN
	Q.PAT_ASSUM `Y = STACK_SIZE_DOPER X` MP_TAC THEN
	IMP_RES_TAC NOT_MEMORY_DOPER___STACK_SIZE_DOPER THEN
	Q.PAT_ASSUM `(reg', mem') = X` (fn thm=> ASSUME_TAC (GSYM thm)) THEN
	ASM_SIMP_TAC std_ss [WORD_ADD_0, WORD_SUB_RZERO] THEN
	STRIP_TAC THEN
	FULL_SIMP_TAC std_ss [REGS_EQUIVALENT_MEM_def] THEN
	MP_TAC (Q.SPECL [`oper`, `reg`, `mem`, `reg'`, `mem'`, `state_old`] (SIMP_RULE std_ss [markerTheory.Abbrev_def] DOPER2INSTRUCTION_NO_MEM_thm)) THEN
	ASM_SIMP_TAC std_ss [MEM_EQUIV_EXCEPT_SLICE_def] THEN
	REPEAT STRIP_TAC THEN
	REMAINS_TAC `(reg ' 13w) = (reg' ' 13w)` THEN1 PROVE_TAC[] THEN
	Q.PAT_ASSUM `mdecode X oper = Y` (fn thm => MP_TAC (GSYM thm)) THEN
	Q.PAT_ASSUM `~(IS_MEMORY_DOPER oper)` MP_TAC THEN
	Q.PAT_ASSUM `STACK_SIZE_DOPER X = Y` MP_TAC THEN
	REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

	`!M. (M = R13) = (13w:word4 = n2w (index_of_reg M))` by ALL_TAC THEN1 (
		Cases_on `M` THEN
		SIMP_TAC std_ss [index_of_reg_def, n2w_11, dimword_4, MREG_distinct]
	) THEN

	Cases_on `oper` THEN (
		ASM_SIMP_TAC std_ss [IS_MEMORY_DOPER_def, mdecode_def, toREG_def, write_thm,
			STACK_SIZE_DOPER_def, FAPPLY_FUPDATE_THM]
	),


	UNDISCH_HD_TAC THEN
	Cases_on `oper` THEN	REWRITE_TAC[IS_MEMORY_DOPER_def] THENL [
		SIMP_TAC std_ss [STACK_SIZE_DOPER_def],
		SIMP_TAC std_ss [STACK_SIZE_DOPER_def],


		SIMP_TAC std_ss [STACK_SIZE_DOPER_def, DOPER2INSTRUCTION_def,
		WORD_ADD_0] THEN
		REPEAT GEN_TAC THEN STRIP_TAC THEN
		ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_STM) THEN
		Q_SPECL_NO_ASSUM 0 [`state_old`, `PRE_TRANS_OPT`, `(reg_bitmap (MAP n2w l))`, `AL:condition`, `13w:word4`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			FULL_SIMP_TAC arith_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
				armTheory.condition_case_def, MREG2REG_11]
		) THEN
		FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds, REG_OWRT_ALL,
			instructionTheory.transfer_options_accessors, owrt_visible_regs_def, PRE_TRANS_OPT_def] THEN WEAKEN_HD_TAC THEN
		FULL_SIMP_TAC std_ss [armTheory.ADDR_MODE4_def, REGISTER_LIST___reg_bitmap, LET_THM, LENGTH_MAP,
		armTheory.FIRST_ADDRESS_def, armTheory.WB_ADDRESS_def,
		armTheory.UP_DOWN_def] THEN
		MATCH_MP_TAC (prove (``((c /\ d) /\ (a /\ b)) ==> ((a:bool) /\ b /\ c /\ d)``, PROVE_TAC[])) THEN
		CONJ_TAC THENL [
			SIMP_TAC std_ss [armTheory.INC_PC_def,
								  armTheory.FETCH_PC_def,
								  combinTheory.UPDATE_def,
								  state_mode_def, armTheory.CPSR_READ_def,
								  systemTheory.arm_sys_state_accfupds],

			FULL_SIMP_TAC std_ss [mdecode_def, pushL_thm, REGS_EQUIVALENT_MEM_def,
				MEM_EQUIV_EXCEPT_SLICE_def],

	DB.find "pushL"

		DB.find "UP_DOWN_def"
		Q.PAT_UNDISCH_TAC `(reg',mem') = mdecode (reg, mem) X` THEN
		ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, MREG2addr_model_thm,
									LET_THM, GSYM MREG2register_def,
									mdecode_def] THEN
		`read (reg,mem) (toREG M0) = REG_READ state_old.registers m (MREG2REG M0)` by
			PROVE_TAC[MREG2REG_thm] THEN
		`read (reg,mem) (toREG M1) = REG_READ state_old.registers m (MREG2REG M1)` by
			PROVE_TAC[MREG2REG_thm] THEN
		ASM_SIMP_TAC std_ss [write_thm, toREG_def] THEN
		REPEAT STRIP_TAC THENL [
			ASM_SIMP_TAC std_ss [REGS_EQUIVALENT___INC_PC, REGS_EQUIVALENT___UPDATE, GSYM MREG2REG_def],
			SIMP_TAC std_ss [armTheory.INC_PC_def,
									armTheory.FETCH_PC_def,
									combinTheory.UPDATE_def,
									MREG_NOT_PC]
		],



*)




val DOPER2INSTRUCTION_LIST_def = Define `
  DOPER2INSTRUCTION_LIST doper =
    [DOPER2INSTRUCTION doper]`


val TRANSLATE_COND_def = Define `
  (TRANSLATE_COND (EQ:COND) = (EQ:condition)) /\
  (TRANSLATE_COND (CS:COND) = (CS:condition)) /\
  (TRANSLATE_COND (MI:COND) = (MI:condition)) /\
  (TRANSLATE_COND (VS:COND) = (VS:condition)) /\
  (TRANSLATE_COND (HI:COND) = (HI:condition)) /\
  (TRANSLATE_COND (GE:COND) = (GE:condition)) /\
  (TRANSLATE_COND (GT:COND) = (GT:condition)) /\
  (TRANSLATE_COND (AL:COND) = (AL:condition)) /\
  (TRANSLATE_COND (NE:COND) = (NE:condition)) /\
  (TRANSLATE_COND (CC:COND) = (CC:condition)) /\
  (TRANSLATE_COND (PL:COND) = (PL:condition)) /\
  (TRANSLATE_COND (VC:COND) = (VC:condition)) /\
  (TRANSLATE_COND (LS:COND) = (LS:condition)) /\
  (TRANSLATE_COND (LT:COND) = (LT:condition)) /\
  (TRANSLATE_COND (LE:COND) = (LE:condition)) /\
  (TRANSLATE_COND (NV:COND) = (NV:condition))`

val CJ2INSTRUCTION_LIST_def = Define `
    CJ2INSTRUCTION_LIST (r, c, e) j =
      [CMP AL (MREG2REG r) (MEXP2addr_model e);
       B (TRANSLATE_COND c) j]`


val CJ2INSTRUCTION_LIST_thm = store_thm ("CJ2INSTRUCTION_LIST_thm",
``
!r c e j tprog
 state_old state_new m reg mem.
((tprog = CJ2INSTRUCTION_LIST (r, c, e) j) /\
  (!e. (e < LENGTH tprog) ==>
    (state_old.memory (ADDR30 (FETCH_PC state_old.registers + n2w (e*4))) =
    (enc (EL e tprog)))) /\
 (~state_old.undefined) /\
 (REGS_EQUIVALENT m state_old.registers reg) /\

 (Abbrev (m = (DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs))))) /\
 (state_new = STATE_ARM_MEM (LENGTH tprog) state_old)) ==>

 ((state_new.memory = state_old.memory) /\
  (~state_new.undefined) /\
  (?N Z C V. state_new.psrs = CPSR_WRITE state_old.psrs (SET_NZCV (N,Z,C,V) (CPSR_READ state_old.psrs))) /\
  (state_new.cp_state = state_old.cp_state) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
  (REGS_EQUIVALENT m state_new.registers reg) /\
  (state_new.registers = if (eval_il_cond (r, c, e) (reg, mem)) then
    (REG_WRITE state_old.registers usr 15w
             (state_old.registers r15 + (n2w (4*(LENGTH tprog))) + 4w + sw2sw j << 2))
    else (REG_WRITE state_old.registers usr 15w (state_old.registers r15 + (n2w (4*(LENGTH tprog)))))))
``,

ASM_SIMP_TAC list_ss [prove (``!e1. (e1 < 2) = ((e1 = 0) \/ (e1 = 1))``, DECIDE_TAC), CJ2INSTRUCTION_LIST_def, DISJ_IMP_THM, FORALL_AND_THM, WORD_ADD_0] THEN
REWRITE_TAC[prove (``2 = SUC (SUC 0)``,DECIDE_TAC), STATE_ARM_MEM_EVAL] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_CMP) THEN
Q_SPECL_NO_ASSUM 0 [`state_old`, `AL:condition`, `MREG2REG r`,  `(MEXP2addr_model e)`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  FULL_SIMP_TAC std_ss [MREG_NOT_PC, armTheory.CONDITION_PASSED2_def, armTheory.NZCV_def,
    armTheory.condition_case_def, systemTheory.ADDR30_def, armTheory.FETCH_PC_def]
) THEN

SUBGOAL_TAC `CONDITION_PASSED2 (NZCV (CPSR_READ (NEXT_ARM_MEM state_old).psrs)) (TRANSLATE_COND c) = eval_il_cond (r,c,e) (reg,mem)` THEN1 (
  `REG_READ state_old.registers  m (MREG2REG r) = read (reg,mem) (toREG r)` by
    PROVE_TAC[MREG2REG_thm] THEN
  `DECODE_MEXP m e state_old.registers = read (reg,mem) (toEXP e)` by
    PROVE_TAC[DECODE_MEXP_thm] THEN
  ASSUME_TAC ARMCompositionTheory.eval_cond_thm THEN
  Q_SPECL_NO_ASSUM 0 [`toREG r`, `c`, `toEXP e`, `(reg, mem)`, `(CPSR_READ state_old.psrs)`] THEN

  FULL_SIMP_TAC std_ss [armTheory.CONDITION_PASSED2_def, eval_il_cond_def, translate_condition_def, TRANSLATE_COND_def,
    systemTheory.arm_sys_state_accfupds, arm_evalTheory.CPSR_WRITE_READ,
    MREG2addr_model_thm, arm_evalTheory.DECODE_NZCV_SET_NZCV,
	 armTheory.NZCV_def] THEN
  Cases_on `c` THEN
  SIMP_TAC std_ss [decode_cond_cpsr_def, TRANSLATE_COND_def,
	armTheory.condition_case_def, setNZCV_thm]
) THEN

Cases_on `eval_il_cond (r, c, e) (reg, mem)` THENL [
	ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] arm_rulesTheory.ARM_B) THEN
	Q_SPECL_NO_ASSUM 0 [`NEXT_ARM_MEM state_old`, `j`, `TRANSLATE_COND c`] THEN
	PROVE_CONDITION_NO_ASSUM 0 THEN1 (
	  FULL_SIMP_TAC std_ss [MREG_NOT_PC, systemTheory.arm_sys_state_accfupds,
		 armTheory.INC_PC_def, combinTheory.APPLY_UPDATE_THM,
		 systemTheory.ADDR30_def, armTheory.FETCH_PC_def]
	) THEN

	FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds,
		arm_evalTheory.DECODE_IFMODE_SET_NZCV,
		owrt_visible_regs_def, state_mode_def, arm_evalTheory.CPSR_WRITE_READ,
		REG_OWRT_ALL] THEN
	REPEAT STRIP_TAC THENL [
		METIS_TAC[],

		ASM_SIMP_TAC std_ss [REGS_EQUIVALENT___WRITE_PC, REGS_EQUIVALENT___INC_PC],

	   REPEAT WEAKEN_HD_TAC THEN
		SIMP_TAC std_ss [arm_evalTheory.INC_PC, arm_evalTheory.REG_WRITE_WRITE] THEN
	   AP_TERM_TAC THEN
	   AP_THM_TAC THEN AP_TERM_TAC THEN
		ASM_SIMP_TAC std_ss [armTheory.REG_WRITE_def, armTheory.mode_reg2num_def, arm_evalTheory.USER_usr, LET_THM] THEN
		WORDS_TAC THEN
		SIMP_TAC std_ss [armTheory.num2register_thm, combinTheory.APPLY_UPDATE_THM, GSYM WORD_ADD_ASSOC] THEN
		WORDS_TAC
	],



	ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] ARM_B_NOP) THEN
	Q_SPECL_NO_ASSUM 0 [`NEXT_ARM_MEM state_old`, `j`, `TRANSLATE_COND c`] THEN
	PROVE_CONDITION_NO_ASSUM 0 THEN1 (
		FULL_SIMP_TAC std_ss [MREG_NOT_PC, systemTheory.arm_sys_state_accfupds,
			armTheory.INC_PC_def, combinTheory.APPLY_UPDATE_THM,
			systemTheory.ADDR30_def, armTheory.FETCH_PC_def]
	) THEN

	FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds,
		arm_evalTheory.CPSR_WRITE_READ, REGS_EQUIVALENT___WRITE_PC,
		arm_evalTheory.INC_PC, arm_evalTheory.REG_WRITE_WRITE,
		arm_evalTheory.DECODE_IFMODE_SET_NZCV,
		owrt_visible_regs_def, state_mode_def, arm_evalTheory.CPSR_WRITE_READ,
		REG_OWRT_ALL] THEN
	REPEAT STRIP_TAC THENL [
		METIS_TAC[],

	   AP_TERM_TAC THEN
		SIMP_TAC std_ss [armTheory.REG_WRITE_def, armTheory.mode_reg2num_def, arm_evalTheory.USER_usr, LET_THM] THEN
		WORDS_TAC THEN
		SIMP_TAC std_ss [armTheory.num2register_thm, combinTheory.APPLY_UPDATE_THM, GSYM WORD_ADD_ASSOC] THEN
		WORDS_TAC
	]
]);





val CONTAINS_MEMORY_DOPER_def = Define `
  (CONTAINS_MEMORY_DOPER (BLK l) = EXISTS IS_MEMORY_DOPER l) /\
  (CONTAINS_MEMORY_DOPER (SC prog1 prog2) = ((CONTAINS_MEMORY_DOPER prog1) \/ (CONTAINS_MEMORY_DOPER prog2))) /\
  (CONTAINS_MEMORY_DOPER (CJ cond prog1 prog2) = ((CONTAINS_MEMORY_DOPER prog1) \/ (CONTAINS_MEMORY_DOPER prog2))) /\
 (CONTAINS_MEMORY_DOPER (TR cond prog1) = (CONTAINS_MEMORY_DOPER prog1))`;

val IS_WELL_FORMED_CTL_STRUCTURE_def = Define `
  (IS_WELL_FORMED_CTL_STRUCTURE (BLK l) = EVERY IS_WELL_FORMED_DOPER l) /\
  (IS_WELL_FORMED_CTL_STRUCTURE (SC prog1 prog2) = (IS_WELL_FORMED_CTL_STRUCTURE prog1 /\ IS_WELL_FORMED_CTL_STRUCTURE prog2)) /\
  (IS_WELL_FORMED_CTL_STRUCTURE (CJ cond prog1 prog2) = (IS_WELL_FORMED_CTL_STRUCTURE prog1 /\ IS_WELL_FORMED_CTL_STRUCTURE prog2)) /\
  (IS_WELL_FORMED_CTL_STRUCTURE (TR cond prog1) = (IS_WELL_FORMED_CTL_STRUCTURE prog1))`;


val CTL_STRUCTURE2INSTRUCTION_LIST_def = Define `
  (CTL_STRUCTURE2INSTRUCTION_LIST (BLK l) = FLAT ((MAP DOPER2INSTRUCTION_LIST) l)) /\
  (CTL_STRUCTURE2INSTRUCTION_LIST (SC prog1 prog2) =
   (CTL_STRUCTURE2INSTRUCTION_LIST prog1) ++ (CTL_STRUCTURE2INSTRUCTION_LIST prog2)) /\

  (CTL_STRUCTURE2INSTRUCTION_LIST (CJ cond prog1 prog2) =
	(CJ2INSTRUCTION_LIST cond (n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog2)))) ++
   (CTL_STRUCTURE2INSTRUCTION_LIST prog2) ++
   [B AL (if (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog1) = 0) then
			 ($- 1w) else
			(n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog1) - 1)))] ++
   (CTL_STRUCTURE2INSTRUCTION_LIST prog1)) /\


  (CTL_STRUCTURE2INSTRUCTION_LIST (TR cond prog1) =
	(CJ2INSTRUCTION_LIST cond (n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog1)))) ++
   (CTL_STRUCTURE2INSTRUCTION_LIST prog1) ++
   [B AL ($- (n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog1) +
		LENGTH (CJ2INSTRUCTION_LIST cond (n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog1)))) + 2)))])`;




val DOPER2INSTRUCTION_LIST_thm = store_thm ("DOPER2INSTRUCTION_LIST_thm",
``
!oper tprog reg mem reg' mem' m
 state_old state_new.
(~(IS_MEMORY_DOPER oper) /\ (IS_WELL_FORMED_DOPER oper) /\
 (tprog = DOPER2INSTRUCTION_LIST oper) /\
  (!e. (e < LENGTH tprog) ==>
    (state_old.memory (ADDR30 (FETCH_PC state_old.registers + n2w (e*4))) =
    (enc (EL e tprog)))) /\
 (~state_old.undefined) /\
 (Abbrev (m = (DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs))))) /\
 ((reg', mem') = mdecode (reg,mem) oper) /\
 (state_new = STATE_ARM_MEM (LENGTH tprog) state_old) /\
 (REGS_EQUIVALENT m state_old.registers reg)) ==>

 ((REGS_EQUIVALENT m state_new.registers reg') /\
  (mem' = mem) /\ (state_new.memory = state_old.memory) /\
  (~state_new.undefined) /\
  (state_new.psrs = state_old.psrs) /\
  (state_new.cp_state = state_old.cp_state) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
  (FETCH_PC state_new.registers = FETCH_PC state_old.registers + n2w (4 * LENGTH tprog))
  )``,

  `!e. (e < 1) = (e = 0)` by DECIDE_TAC THEN
  ASM_SIMP_TAC list_ss [DOPER2INSTRUCTION_LIST_def] THEN
  REWRITE_TAC [prove(``1 = SUC 0``, DECIDE_TAC), STATE_ARM_MEM_EVAL] THEN
  ASSUME_TAC (SIMP_RULE std_ss [] DOPER2INSTRUCTION_thm) THEN
  FULL_SIMP_TAC std_ss [WORD_ADD_0, systemTheory.ADDR30_def,
    armTheory.FETCH_PC_def] THEN
  METIS_TAC[]);



val JUMP_ADDRESS_OK_thm = store_thm ("JUMP_ADDRESS_OK_thm",
``!n. ((n < 2**(dimindex (:'a) - 1)) /\ (dimindex (:'a) <= dimindex (:'b))) ==>
(((sw2sw ((n2w:num->bool ** 'a) n)) = ((n2w:num->bool ** 'b) n)) /\
 ((sw2sw ($-((n2w:num->bool ** 'a) n))) = ($- ((n2w:num->bool ** 'b) n))))``,

REWRITE_TAC[sw2sw_def, bitTheory.SIGN_EXTEND_def,
MOD_2EXP_DIMINDEX, GSYM dimword_def, n2w_11,
GSYM word_msb_n2w, n2w_w2n, word_msb_n2w_numeric, word_2comp_n2w, w2n_n2w] THEN
REWRITE_TAC[dimword_def, INT_MIN_def] THEN
Q.ABBREV_TAC `a = dimindex (:'a)` THEN
Q.ABBREV_TAC `b = dimindex (:'b)` THEN
`(0 < a) /\ (0 < b)` by PROVE_TAC[DIMINDEX_GT_0] THEN

SIMP_TAC arith_ss [MOD_2EXP_def, LET_THM] THEN
`?pa. a = SUC pa` by ALL_TAC THEN1 (
	Cases_on `a` THENL [
		FULL_SIMP_TAC std_ss [],
		PROVE_TAC[]
	]
) THEN
REPEAT STRIP_TAC THENL [
	UNDISCH_NO_TAC 1 THEN
	FULL_SIMP_TAC arith_ss [EXP],

	UNDISCH_NO_TAC 1 THEN
	FULL_SIMP_TAC arith_ss [EXP] THEN
	REPEAT STRIP_TAC THEN
	Cases_on `n = 0` THENL [
		ASM_SIMP_TAC arith_ss [],

		`~(2 ** pa = 0)` by SIMP_TAC std_ss [EXP_EQ_0] THEN
		`(2 ** pa <= (2 * 2 ** pa - n) MOD (2 * 2 ** pa))` by FULL_SIMP_TAC arith_ss [] THEN
		ONCE_ASM_REWRITE_TAC[] THEN
		WEAKEN_HD_TAC THEN
		REWRITE_TAC[] THEN
		REMAINS_TAC `2 * 2** pa <= 2 ** b` THEN1 ASM_SIMP_TAC arith_ss [] THEN
		SIMP_TAC std_ss [GSYM EXP, EXP_BASE_LE_MONO] THEN
		PROVE_TAC[]
	]
]);


val CTL_STRUCTURE2INSTRUCTION_LIST_thm = store_thm ("CTL_STRUCTURE2INSTRUCTION_LIST_thm",
``
!prog tprog reg mem reg' mem' m state_old.

  (~(CONTAINS_MEMORY_DOPER prog) /\ (WELL_FORMED prog) /\ (IS_WELL_FORMED_CTL_STRUCTURE prog) /\
   (tprog = CTL_STRUCTURE2INSTRUCTION_LIST prog) /\
	(LENGTH tprog < 2**(dimindex (:24) - 1) -1) /\

  (!e. (e < LENGTH tprog) ==>
    (state_old.memory (ADDR30 (FETCH_PC state_old.registers + n2w (e*4))) =
    (enc (EL e tprog)))) /\

  (~state_old.undefined) /\

  (Abbrev (m = DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs)))) /\

  ((reg', mem') = run_ir prog (reg,mem)) /\
  (REGS_EQUIVALENT m state_old.registers reg)) ==>
  (?step_num. !state_new.   (state_new = STATE_ARM_MEM step_num state_old) ==>

((REGS_EQUIVALENT m state_new.registers reg') /\
 (mem' = mem) /\ (state_new.memory = state_old.memory) /\
 (~state_new.undefined) /\
  (?N Z C V. state_new.psrs = CPSR_WRITE state_old.psrs (SET_NZCV (N,Z,C,V) (CPSR_READ state_old.psrs))) /\
  (state_new.cp_state = state_old.cp_state) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
 (FETCH_PC state_new.registers = (FETCH_PC state_old.registers +
  n2w (4 * LENGTH tprog)))))``,


Induct_on `prog` THENL [
  (*BLK*)
  Induct_on `l` THENL [
	 REPEAT STRIP_TAC THEN
	 EXISTS_TAC ``0`` THEN
    FULL_SIMP_TAC list_ss [STATE_ARM_MEM_EVAL, WORD_ADD_0, CTL_STRUCTURE2INSTRUCTION_LIST_def, SEMANTICS_OF_IR] THEN
	 PROVE_TAC[arm_evalTheory.SET_NZCV_ID, arm_evalTheory.CPSR_READ_WRITE],





    FULL_SIMP_TAC list_ss [CTL_STRUCTURE2INSTRUCTION_LIST_def,
      CONTAINS_MEMORY_DOPER_def,IS_WELL_FORMED_CTL_STRUCTURE_def,
      IR_SEMANTICS_BLK,
      WELL_FORMED_thm] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    `?reg'' mem''. mdecode (reg, mem) h = (reg'', mem'')` by METIS_TAC[PAIR] THEN

    ASSUME_TAC (SIMP_RULE std_ss [] DOPER2INSTRUCTION_LIST_thm) THEN
    Q_SPECL_NO_ASSUM 0 [`h`, `reg`, `mem`, `reg''`, `mem''`, `m`, `state_old`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      FULL_SIMP_TAC list_ss [] THEN
		REWRITE_TAC[markerTheory.Abbrev_def] THEN
      REPEAT STRIP_TAC THEN
      Q_SPEC_NO_ASSUM 6 `e` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1]
    ) THEN


    SUBGOAL_TAC `!a b. (n2w (4 * (a + b))):word32 =
                         n2w (4 * a) + n2w (4 * b)` THEN1 (
      WORDS_TAC THEN
      SIMP_TAC arith_ss []
    ) THEN

    Q_SPECL_NO_ASSUM 13 [`reg''`, `mem''`, `reg'`, `mem'`, `m`, `STATE_ARM_MEM (LENGTH (DOPER2INSTRUCTION_LIST h)) state_old`] THEN
    FULL_SIMP_TAC list_ss [] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
		REWRITE_TAC[markerTheory.Abbrev_def] THEN
      FULL_SIMP_TAC arith_ss [] THEN
      REPEAT STRIP_TAC THEN
      Q_SPEC_NO_ASSUM 15 `LENGTH (DOPER2INSTRUCTION_LIST h) + e` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, WORD_ADD_ASSOC]
    ) THEN
	 FULL_SIMP_TAC std_ss [] THEN
	 EXISTS_TAC ``step_num + LENGTH (DOPER2INSTRUCTION_LIST h)`` THEN
	 SIMP_TAC std_ss [STATE_ARM_MEM_SPLIT] THEN
    FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC] THEN
	 PROVE_TAC[]
  ],


  FULL_SIMP_TAC list_ss [CTL_STRUCTURE2INSTRUCTION_LIST_def,
      CONTAINS_MEMORY_DOPER_def,IS_WELL_FORMED_CTL_STRUCTURE_def,
      IR_SEMANTICS_SC, WELL_FORMED_thm] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  `?reg'' mem''. run_ir prog (reg, mem) = (reg'', mem'')` by METIS_TAC[PAIR] THEN
  Q_SPECL_NO_ASSUM 14 [`reg`, `mem`, `reg''`, `mem''`, `m`, `state_old`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    ASM_SIMP_TAC arith_ss [markerTheory.Abbrev_def] THEN
    REPEAT STRIP_TAC THEN
    Q_SPEC_NO_ASSUM 6 `e` THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1]
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `state = (STATE_ARM_MEM step_num state_old)` THEN

  SUBGOAL_TAC `!a b. (n2w (4 * (a + b))):word32 =
                         n2w (4 * a) + n2w (4 * b)` THEN1 (
      WORDS_TAC THEN
      SIMP_TAC arith_ss []
  ) THEN
  Q_SPECL_NO_ASSUM 23 [`reg''`, `mem''`, `reg'`, `mem'`, `m`, `state`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
	 REWRITE_TAC[markerTheory.Abbrev_def] THEN
    FULL_SIMP_TAC arith_ss [arm_evalTheory.DECODE_IFMODE_SET_NZCV,
		arm_evalTheory.CPSR_WRITE_READ] THEN
    REPEAT STRIP_TAC THENL [
      Q_SPEC_NO_ASSUM 16 `LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog) + e` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2, WORD_ADD_ASSOC],

      ASM_SIMP_TAC std_ss [SEMANTICS_OF_IR]
    ]
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN
  EXISTS_TAC ``(step_num':num) + step_num`` THEN
  Q.UNABBREV_TAC `state` THEN
  FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC, STATE_ARM_MEM_SPLIT,
		arm_evalTheory.SET_NZCV_IDEM, arm_evalTheory.CPSR_WRITE_WRITE,
		arm_evalTheory.CPSR_WRITE_READ] THEN
  PROVE_TAC[],





  FULL_SIMP_TAC list_ss [CTL_STRUCTURE2INSTRUCTION_LIST_def,
      CONTAINS_MEMORY_DOPER_def,IS_WELL_FORMED_CTL_STRUCTURE_def,
      WELL_FORMED_thm] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_NO_TAC 1 (*run_ir CJ ...*) THEN
  ASM_SIMP_TAC std_ss [SEMANTICS_OF_IR] THEN
  STRIP_TAC THEN

  `?r c e. p = (r, c, e)` by METIS_TAC[PAIR] THEN
  ASSUME_TAC (SIMP_RULE std_ss [] CJ2INSTRUCTION_LIST_thm) THEN
  Q_SPECL_NO_ASSUM 0 [`r`, `c`, `e`, `(n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog'))):word24`, `state_old`, `m`, `reg`, `mem`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def] THEN
    REPEAT STRIP_TAC THEN
    Q_SPEC_NO_ASSUM 6 `e'` THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1,
		GSYM APPEND_ASSOC]
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `length_cond = (LENGTH
                   (CJ2INSTRUCTION_LIST (r,c,e)
                      (n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog')))))` THEN
  Q.ABBREV_TAC `length_false = (LENGTH
                   (CTL_STRUCTURE2INSTRUCTION_LIST prog'))` THEN
  Q.ABBREV_TAC `length_true = (LENGTH
                   (CTL_STRUCTURE2INSTRUCTION_LIST prog))` THEN
  Cases_on `eval_il_cond (r,c,e) (reg,mem)` THENL [
		FULL_SIMP_TAC std_ss [dimindex_24] THEN
		Q_SPECL_NO_ASSUM 25 [`reg`, `mem`, `reg'`, `mem'`, `m`, `STATE_ARM_MEM length_cond state_old`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			REWRITE_TAC[markerTheory.Abbrev_def] THEN
			FULL_SIMP_TAC arith_ss [arm_evalTheory.DECODE_IFMODE_SET_NZCV,
				arm_evalTheory.CPSR_WRITE_READ] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 17 `length_cond + (length_false + (1 + e'))` THEN
			UNDISCH_HD_TAC THEN
			`w2n (15w:word4) = 15` by WORDS_TAC THEN
			ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, FETCH_PC___PC_WRITE, combinTheory.APPLY_UPDATE_THM, armTheory.FETCH_PC_def] THEN
			MATCH_MP_TAC (prove (``(a = b) ==> ((a = c) ==> (b = c))``, SIMP_TAC std_ss [])) THEN

			AP_TERM_TAC THEN
			AP_TERM_TAC THEN
			SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL, GSYM WORD_ADD_ASSOC] THEN

			ASSUME_TAC (SIMP_RULE arith_ss [dimindex_32, dimindex_24] (INST_TYPE [alpha |-> ``:24``, beta |-> ``:32``] JUMP_ADDRESS_OK_thm)) THEN
			Q_SPEC_NO_ASSUM 0 `length_false` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [] THEN
			DISCH_TAC THEN WEAKEN_HD_TAC THEN

			REWRITE_TAC [prove (``2 = 1 + 1``, DECIDE_TAC), GSYM LSL_ADD, LSL_ONE,
				word_add_n2w] THEN
			AP_TERM_TAC THEN
			DECIDE_TAC
		) THEN
		FULL_SIMP_TAC std_ss [] THEN
		Q_TAC EXISTS_TAC `step_num+length_cond` THEN
		ASM_SIMP_TAC std_ss [STATE_ARM_MEM_SPLIT, FETCH_PC___PC_WRITE,   arm_evalTheory.SET_NZCV_IDEM, arm_evalTheory.CPSR_WRITE_READ,
			arm_evalTheory.CPSR_WRITE_WRITE] THEN
		REPEAT STRIP_TAC THENL [
			METIS_TAC[],

			SIMP_TAC std_ss [armTheory.FETCH_PC_def, WORD_EQ_ADD_LCANCEL, GSYM WORD_ADD_ASSOC] THEN
			ASSUME_TAC (SIMP_RULE arith_ss [dimindex_32, dimindex_24] (INST_TYPE [alpha |-> ``:24``, beta |-> ``:32``] JUMP_ADDRESS_OK_thm)) THEN
			Q_SPEC_NO_ASSUM 0 `length_false` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [] THEN
			DISCH_TAC THEN WEAKEN_HD_TAC THEN

			REWRITE_TAC [prove (``2 = 1 + 1``, DECIDE_TAC), GSYM LSL_ADD, LSL_ONE,
				word_add_n2w] THEN
			AP_TERM_TAC THEN
			DECIDE_TAC
		],










		FULL_SIMP_TAC std_ss [dimindex_24] THEN
		Q_SPECL_NO_ASSUM 24 [`reg`, `mem`, `reg'`, `mem'`, `m`, `STATE_ARM_MEM length_cond state_old`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			ASM_SIMP_TAC arith_ss [markerTheory.Abbrev_def, arm_evalTheory.DECODE_IFMODE_SET_NZCV, arm_evalTheory.CPSR_WRITE_READ] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 17 `length_cond + e'` THEN
			UNDISCH_HD_TAC THEN
			`w2n (15w:word4) = 15` by WORDS_TAC THEN
			REWRITE_TAC [GSYM APPEND_ASSOC] THEN
			ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, FETCH_PC___PC_WRITE, combinTheory.APPLY_UPDATE_THM, armTheory.FETCH_PC_def, rich_listTheory.EL_APPEND1, word_add_n2w, GSYM WORD_ADD_ASSOC] THEN
			MATCH_MP_TAC (prove (``(a = b) ==> ((a = c) ==> (b = c))``, SIMP_TAC std_ss [])) THEN

			AP_TERM_TAC THEN
			AP_TERM_TAC THEN
			REWRITE_TAC [WORD_EQ_ADD_LCANCEL] THEN
			AP_TERM_TAC THEN
			DECIDE_TAC
		) THEN
		FULL_SIMP_TAC std_ss [] THEN

		ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] arm_rulesTheory.ARM_B) THEN
		Q_SPECL_NO_ASSUM 0 [`(STATE_ARM_MEM step_num (STATE_ARM_MEM length_cond state_old))`, `if (length_true = 0) then $-1w else (n2w (length_true - 1)):word24`, `AL`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			FULL_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds, armTheory.FETCH_PC_def,
				armTheory.CONDITION_PASSED2_def, arm_evalTheory.DECODE_NZCV_SET_NZCV,
				armTheory.NZCV_def, armTheory.condition_case_def] THEN
			Q_SPEC_NO_ASSUM 24 `length_cond + length_false` THEN
			UNDISCH_HD_TAC THEN
			REWRITE_TAC [GSYM APPEND_ASSOC] THEN
			ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, systemTheory.ADDR30_def] THEN

			MATCH_MP_TAC (prove (``(a = b) ==> ((a = c) ==> (b = c))``, SIMP_TAC std_ss [])) THEN

			AP_TERM_TAC THEN
			AP_TERM_TAC THEN
			REWRITE_TAC[GSYM armTheory.FETCH_PC_def, FETCH_PC___PC_WRITE,
				GSYM WORD_ADD_ASSOC, WORD_EQ_ADD_LCANCEL, word_add_n2w] THEN
			AP_TERM_TAC THEN
			DECIDE_TAC
		) THEN


		FULL_SIMP_TAC std_ss [] THEN
		Q_TAC EXISTS_TAC `(SUC 0)+step_num+length_cond` THEN
		REWRITE_TAC[STATE_ARM_MEM_SPLIT, STATE_ARM_MEM_EVAL] THEN
		ASM_SIMP_TAC std_ss [systemTheory.arm_sys_state_accfupds, FETCH_PC___PC_WRITE,
			arm_evalTheory.SET_NZCV_IDEM,REGS_EQUIVALENT___WRITE_PC,
			arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.CPSR_WRITE_WRITE] THEN
		REPEAT STRIP_TAC THENL [
			METIS_TAC[],

			REPEAT (Q.PAT_ASSUM `owrt_visible_regs x = owrt_visible_regs y` MP_TAC) THEN
			ASM_SIMP_TAC std_ss [owrt_visible_regs_def, state_mode_def,
				systemTheory.arm_sys_state_accfupds, REG_OWRT_ALL,
				arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.DECODE_IFMODE_SET_NZCV],



			ASM_REWRITE_TAC[GSYM armTheory.FETCH_PC_def, FETCH_PC___PC_WRITE] THEN
			SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL, GSYM WORD_ADD_ASSOC] THEN
			Cases_on `length_true` THENL[
				WORDS_TAC THEN
				ASM_SIMP_TAC arith_ss [],

				ASSUME_TAC (SIMP_RULE arith_ss [dimindex_32, dimindex_24] (INST_TYPE [alpha |-> ``:24``, beta |-> ``:32``] JUMP_ADDRESS_OK_thm)) THEN
				Q_SPEC_NO_ASSUM 0 `n:num` THEN
				UNDISCH_HD_TAC THEN
				ASM_SIMP_TAC arith_ss [] THEN
				DISCH_TAC THEN WEAKEN_HD_TAC THEN

				REWRITE_TAC [prove (``2 = 1 + 1``, DECIDE_TAC), GSYM LSL_ADD, LSL_ONE,
					word_add_n2w] THEN
				AP_TERM_TAC THEN
				DECIDE_TAC
			]
		]
	],



  FULL_SIMP_TAC list_ss [CTL_STRUCTURE2INSTRUCTION_LIST_def,
      CONTAINS_MEMORY_DOPER_def,IS_WELL_FORMED_CTL_STRUCTURE_def,
      WELL_FORMED_thm] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_NO_TAC 1 (*run_ir CJ ...*) THEN
  ASM_SIMP_TAC std_ss [IR_SEMANTICS_TR___FUNPOW] THEN
  SUBGOAL_TAC `stopAt (eval_il_cond p) (run_ir prog) (reg,mem)` THEN1 (
		MATCH_MP_TAC ARMCompositionTheory.WF_LOOP_IMP_STOPAT THEN
		ASM_SIMP_TAC std_ss [GSYM WF_ir_TR_def, WF_ir_TR_thm]
  ) THEN
  UNDISCH_ALL_TAC THEN
  SPEC_TAC (``state_old:'a arm_sys_state``, ``state_old:'a arm_sys_state``) THEN
  Induct_on `(shortest (eval_il_cond p) (run_ir prog) (reg,mem))` THENL [
  		REPEAT STRIP_TAC THEN
		`?r c e. p = (r, c, e)` by METIS_TAC[PAIR] THEN
		ASSUME_TAC (SIMP_RULE std_ss [] CJ2INSTRUCTION_LIST_thm) THEN
		Q_SPECL_NO_ASSUM 0 [`r`, `c`, `e`, `(n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog))):word24`, `state_old`, `m`, `reg`, `mem`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 7 `e'` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1,
				GSYM APPEND_ASSOC]
		) THEN
		FULL_SIMP_TAC std_ss [] THEN
		Q.ABBREV_TAC `length_cond = (LENGTH
								(CJ2INSTRUCTION_LIST (r,c,e)
									(n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog)))))` THEN

		`eval_il_cond (r,c,e) (reg, mem)` by METIS_TAC[SHORTEST_LEM] THEN
		Q.PAT_ASSUM `0 = shortest P Q X` (fn thm => ASSUME_TAC (GSYM thm)) THEN
		Q_TAC EXISTS_TAC `length_cond` THEN
		FULL_SIMP_TAC std_ss [FUNPOW, FETCH_PC___PC_WRITE, dimindex_24] THEN
		REPEAT STRIP_TAC THENL [
			METIS_TAC[],

			ASM_REWRITE_TAC[GSYM armTheory.FETCH_PC_def] THEN
			SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL, GSYM WORD_ADD_ASSOC] THEN
			Q.ABBREV_TAC `n = LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog)` THEN
			ASSUME_TAC (SIMP_RULE arith_ss [dimindex_32, dimindex_24] (INST_TYPE [alpha |-> ``:24``, beta |-> ``:32``] JUMP_ADDRESS_OK_thm)) THEN
			Q_SPEC_NO_ASSUM 0 `n` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [] THEN
			DISCH_TAC THEN WEAKEN_HD_TAC THEN

			REWRITE_TAC [prove (``2 = 1 + 1``, DECIDE_TAC), GSYM LSL_ADD, LSL_ONE,
				word_add_n2w] THEN
			AP_TERM_TAC THEN
			DECIDE_TAC
		],




		REPEAT STRIP_TAC THEN
		Q.PAT_ASSUM `SUC v = shortest P Q X` (fn thm => ASSUME_TAC (GSYM thm)) THEN
		IMP_RES_TAC SHORTEST_INDUCTIVE THEN
		`?reg'' mem''. run_ir prog (reg,mem) = (reg'', mem'')` by METIS_TAC[PAIR] THEN
		Q_SPECL_NO_ASSUM 17 [`p`, `prog`, `reg''`, `mem''`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
		FULL_SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM, dimindex_24] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 METIS_TAC[] THEN
		UNDISCH_HD_TAC THEN
		ASM_REWRITE_TAC[] THEN
		STRIP_TAC THEN


		`?r c e. p = (r, c, e)` by METIS_TAC[PAIR] THEN
		ASSUME_TAC (SIMP_RULE std_ss [] CJ2INSTRUCTION_LIST_thm) THEN
		Q_SPECL_NO_ASSUM 0 [`r`, `c`, `e`, `(n2w (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog))):word24`, `state_old`, `m`, `reg`, `mem`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 13 `e'` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [rich_listTheory.EL_APPEND1,
				GSYM APPEND_ASSOC]
		) THEN
		FULL_SIMP_TAC std_ss [] THEN
		Q.ABBREV_TAC `length_prog = (LENGTH (CTL_STRUCTURE2INSTRUCTION_LIST prog))` THEN
		Q.ABBREV_TAC `length_cond = (LENGTH	(CJ2INSTRUCTION_LIST (r,c,e) (n2w length_prog)))` THEN

		Q_SPECL_NO_ASSUM 27 [`reg`, `mem`, `reg''`, `mem''`, `m`, `STATE_ARM_MEM length_cond state_old`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			ASM_SIMP_TAC arith_ss [FUNPOW, REGS_EQUIVALENT___WRITE_PC, FETCH_PC___PC_WRITE, markerTheory.Abbrev_def,
				arm_evalTheory.DECODE_IFMODE_SET_NZCV,
				arm_evalTheory.CPSR_WRITE_READ] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 22 `length_cond + e'` THEN
			UNDISCH_HD_TAC THEN
			REWRITE_TAC [GSYM APPEND_ASSOC] THEN
			ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, rich_listTheory.EL_APPEND1,
				word_add_n2w, GSYM WORD_ADD_ASSOC, LEFT_ADD_DISTRIB,
				armTheory.FETCH_PC_def]
		) THEN
		FULL_SIMP_TAC arith_ss [] THEN


		ASSUME_TAC (SIMP_RULE std_ss [markerTheory.Abbrev_def] arm_rulesTheory.ARM_B) THEN
		Q_SPECL_NO_ASSUM 0 [`(STATE_ARM_MEM step_num (STATE_ARM_MEM length_cond state_old))`, `($- (n2w (length_cond + (length_prog + 2)))):word24`, `AL`] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			ASM_SIMP_TAC std_ss [
				armTheory.CONDITION_PASSED2_def, arm_evalTheory.DECODE_NZCV_SET_NZCV,
				armTheory.NZCV_def, armTheory.condition_case_def] THEN
			ASM_REWRITE_TAC[GSYM armTheory.FETCH_PC_def, FETCH_PC___PC_WRITE] THEN
			Q_SPEC_NO_ASSUM 29 `length_cond + length_prog` THEN
			UNDISCH_HD_TAC THEN
			REWRITE_TAC [GSYM APPEND_ASSOC] THEN
			ASM_SIMP_TAC list_ss [rich_listTheory.EL_APPEND2, systemTheory.ADDR30_def,
					word_add_n2w, GSYM WORD_ADD_ASSOC, LEFT_ADD_DISTRIB]
		) THEN


		SUBGOAL_TAC `!e1. (FETCH_PC state_old.registers + n2w (4 * length_cond) +
             n2w (4 * length_prog) + 8w +
             sw2sw ($- (n2w (length_cond + (length_prog + 2))):word24) << 2 +
             n2w (4 * e1) = FETCH_PC state_old.registers + n2w (4 * e1))` THEN1 (

			GEN_TAC THEN
			ASSUME_TAC (SIMP_RULE arith_ss [dimindex_32, dimindex_24] (INST_TYPE [alpha |-> ``:24``, beta |-> ``:32``] JUMP_ADDRESS_OK_thm)) THEN
			Q_SPEC_NO_ASSUM 0 `(length_cond + (length_prog + 2))` THEN
			UNDISCH_HD_TAC THEN
			ASM_SIMP_TAC arith_ss [] THEN
			DISCH_TAC THEN WEAKEN_HD_TAC THEN

			REWRITE_TAC[WORD_EQ_ADD_RCANCEL, GSYM WORD_ADD_ASSOC,WORD_ADD_INV_0_EQ] THEN
			REWRITE_TAC [prove (``2 = 1 + 1``, DECIDE_TAC), GSYM LSL_ADD, LSL_ONE,
				word_add_n2w, GSYM WORD_NEG_ADD] THEN

			`(length_cond + (length_prog + 2) +
            (length_cond + (length_prog + 2)) +
            (length_cond + (length_prog + 2) +
             (length_cond + (length_prog + 2)))) =
			 4*length_cond + 4 * length_prog + 8` by DECIDE_TAC THEN
			ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

			SIMP_TAC std_ss [GSYM word_add_n2w, WORD_NEG_ADD] THEN
			REPEAT WEAKEN_HD_TAC THEN
			METIS_TAC[WORD_SUB_REFL, WORD_SUB, WORD_ADD_ASSOC, WORD_ADD_COMM,
				WORD_ADD_0]
		) THEN

		Q_SPEC_NO_ASSUM 20 `NEXT_ARM_MEM
             (STATE_ARM_MEM step_num (STATE_ARM_MEM length_cond state_old))` THEN
		FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN
		PROVE_CONDITION_NO_ASSUM 0 THEN1 (
			REWRITE_TAC[markerTheory.Abbrev_def] THEN
			FULL_SIMP_TAC std_ss [FUNPOW, systemTheory.arm_sys_state_accfupds,
			arm_evalTheory.DECODE_IFMODE_SET_NZCV,
			REGS_EQUIVALENT___WRITE_PC, FETCH_PC___PC_WRITE,
			arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.CPSR_WRITE_WRITE] THEN
			ASM_REWRITE_TAC[GSYM armTheory.FETCH_PC_def, FETCH_PC___PC_WRITE]
		) THEN
		FULL_SIMP_TAC std_ss [] THEN

		EXISTS_TAC ``step_num' + (SUC 0) + step_num + length_cond:num`` THEN
	   SIMP_TAC std_ss [STATE_ARM_MEM_SPLIT, STATE_ARM_MEM_EVAL] THEN
		ASM_SIMP_TAC std_ss [FUNPOW, systemTheory.arm_sys_state_accfupds, FETCH_PC___PC_WRITE,   arm_evalTheory.SET_NZCV_IDEM,
			arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.CPSR_WRITE_WRITE] THEN
		REPEAT STRIP_TAC THENL [
			METIS_TAC[],

			REPEAT (Q.PAT_ASSUM `owrt_visible_regs x = owrt_visible_regs y` MP_TAC) THEN
			ASM_SIMP_TAC std_ss [owrt_visible_regs_def, state_mode_def,
				systemTheory.arm_sys_state_accfupds, REG_OWRT_ALL,
				arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.DECODE_IFMODE_SET_NZCV],

			ASM_REWRITE_TAC[GSYM armTheory.FETCH_PC_def, FETCH_PC___PC_WRITE]
		]
	]
]);



val WORD_UNIV_IMAGE_COUNT =
	store_thm ("WORD_UNIV_IMAGE_COUNT",
``(UNIV:'a word -> bool) =
(IMAGE n2w (count (dimword (:'a))))``,

SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_IMAGE, IN_COUNT] THEN
GEN_TAC THEN
Q_TAC EXISTS_TAC `w2n x` THEN
SIMP_TAC std_ss [n2w_w2n, w2n_lt]);


val FINITE_WORD_UNIV =
	store_thm ("FINITE_WORD_UNIV",
	``FINITE (UNIV:'a word -> bool)``,
SIMP_TAC std_ss [WORD_UNIV_IMAGE_COUNT] THEN
MATCH_MP_TAC IMAGE_FINITE THEN
SIMP_TAC std_ss [FINITE_COUNT]);


val arm_mem_state2reg_fun_def = Define (`arm_mem_state2reg_fun state =
	let mode = DECODE_MODE ((4 >< 0) (CPSR_READ state.psrs)) in
   (\n:word4. if (n=15w) then 0w else state.registers (num2register (mode_reg2num mode n)))`)

val state2reg_fun_def = Define (`state2reg_fun (regs, memory) =
	(\n:word4. if (n=15w) then 0w else (regs ' n))`)


val arm_mem_state2state_def = Define (`arm_mem_state2state state =
	(let mode = DECODE_MODE ((4 >< 0) (CPSR_READ state.psrs)) in
   (FUN_FMAP (\n:word4. state.registers (num2register (mode_reg2num mode n))) UNIV),
    FUN_FMAP (\n:word30. state.memory n) UNIV)`)

val arm_mem_state2state___REGS_EQUIVALENT =
	store_thm ("arm_mem_state2state___REGS_EQUIVALENT",
``!state reg mem. ((reg, mem) = arm_mem_state2state state) ==>
			(REGS_EQUIVALENT (DECODE_MODE ((4 >< 0) (CPSR_READ state.psrs))) state.registers reg)``,

SIMP_TAC std_ss [arm_mem_state2state_def, LET_THM, REGS_EQUIVALENT_def,
	FINITE_WORD_UNIV, pred_setTheory.IN_UNIV, FUN_FMAP_DEF]);



val MREG2REG_EXISTS =
	store_thm ("MREG2REG_EXISTS",
``!w:word4. ~(w = 15w) ==> (?r. MREG2REG r = w)``,

REPEAT STRIP_TAC THEN
SUBGOAL_TAC `!r. index_of_reg r MOD 16 = index_of_reg r` THEN1 (
	GEN_TAC THEN
	`index_of_reg r < 15` by REWRITE_TAC[index_of_reg_lt] THEN
	ASM_SIMP_TAC arith_ss []
) THEN
SUBGOAL_TAC `?n. (w = n2w n) /\ n < 15` THEN1 (
	Q_TAC EXISTS_TAC `w2n w` THEN
	SIMP_TAC std_ss [n2w_w2n] THEN
	`w2n w < 16` by SIMP_TAC std_ss [w2n_lt, GSYM dimword_4] THEN
	Cases_on `w2n w = 15` THENL [
		METIS_TAC[n2w_w2n],
		DECIDE_TAC
	]
) THEN
ASM_SIMP_TAC arith_ss [MREG2REG_def,n2w_11,dimword_4] THEN
UNDISCH_HD_TAC THEN
ASSUME_TAC ((REDEPTH_CONV numLib.num_CONV) ``15``) THEN
ASM_REWRITE_TAC[prim_recTheory.LESS_THM] THEN
SIMP_TAC std_ss [DISJ_IMP_THM] THEN
REWRITE_TAC[GSYM index_of_reg_def, index_of_reg_11] THEN
SIMP_TAC std_ss []);



val REGS_EQUIVALENT___2reg_fun =
	store_thm ("REGS_EQUIVALENT___2reg_fun",
``!state regs memory. (REGS_EQUIVALENT (DECODE_MODE ((4 >< 0) (CPSR_READ state.psrs))) state.registers regs) ==>
					 (arm_mem_state2reg_fun state =
					 state2reg_fun (regs, memory))
					 ``,

SIMP_TAC std_ss [REGS_EQUIVALENT_def, arm_mem_state2reg_fun_def, state2reg_fun_def, LET_THM, FUN_EQ_THM, COND_RAND] THEN
REPEAT STRIP_TAC THEN
Cases_on `x=15w` THEN ASM_REWRITE_TAC[] THEN
METIS_TAC[MREG2REG_EXISTS]
);



val TRANSLATION_SPEC_thm = store_thm ("TRANSLATION_SPEC_thm",
``
!prog tprog P m state_old:'a arm_sys_state.

  (~(CONTAINS_MEMORY_DOPER prog) /\ (WELL_FORMED prog) /\ (IS_WELL_FORMED_CTL_STRUCTURE prog) /\
   (tprog = CTL_STRUCTURE2INSTRUCTION_LIST prog) /\
	(LENGTH tprog < 2**(dimindex (:24) - 1) -1) /\
  (!st. P (state2reg_fun st) (state2reg_fun (run_ir prog st))) /\

  (!e. (e < LENGTH tprog) ==>
    (state_old.memory (ADDR30 (FETCH_PC state_old.registers + n2w (e*4))) =
    (enc (EL e tprog)))) /\

  (~state_old.undefined)  ==>
  (?step_num. !state_new. (state_new = STATE_ARM_MEM step_num state_old) ==>

((P (arm_mem_state2reg_fun state_old) (arm_mem_state2reg_fun state_new)) /\
 (state_new.memory = state_old.memory) /\
 (~state_new.undefined) /\
  (?N Z C V. state_new.psrs = CPSR_WRITE (state_old.psrs) (SET_NZCV (N,Z,C,V) (CPSR_READ state_old.psrs))) /\
 (state_new.cp_state = state_old.cp_state) /\
  (owrt_visible_regs state_new = owrt_visible_regs state_old) /\
 (FETCH_PC state_new.registers = (FETCH_PC state_old.registers +
  n2w (4 * LENGTH tprog))))))``,


REPEAT STRIP_TAC THEN
`?m. DECODE_MODE ((4 >< 0) (CPSR_READ state_old.psrs)) = m` by METIS_TAC[] THEN

`?reg_old mem_old:(num |-> word32). REGS_EQUIVALENT m state_old.registers reg_old` by METIS_TAC[PAIR, arm_mem_state2state___REGS_EQUIVALENT] THEN
`?reg_new mem_new. (reg_new, mem_new) = run_ir prog (reg_old, mem_old)` by METIS_TAC[PAIR] THEN

ASSUME_TAC CTL_STRUCTURE2INSTRUCTION_LIST_thm THEN
Q_SPECL_NO_ASSUM 0 [`prog`, `tprog` , `reg_old`,`mem_old`, `reg_new`, `mem_new`,`m`, `state_old:'a arm_sys_state`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
	FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
) THEN
FULL_SIMP_TAC std_ss [] THEN
EXISTS_TAC ``step_num:num`` THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [
	SUBGOAL_TAC `m =  DECODE_MODE ((4 >< 0) (CPSR_READ (STATE_ARM_MEM step_num state_old).psrs))` THEN1 (
		ASM_SIMP_TAC std_ss [arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.DECODE_IFMODE_SET_NZCV]
	) THEN
	METIS_TAC[REGS_EQUIVALENT___2reg_fun],
	METIS_TAC[]
]);


val index_of_reg___from_reg_index =
	store_thm ("index_of_reg___from_reg_index",
``!n. (n < 15) ==>
	(index_of_reg (from_reg_index n) = n)``,

GEN_TAC THEN
`!n m. (n < SUC m) = ((n < m) \/ (n = m))` by DECIDE_TAC THEN
`15 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))` by DECIDE_TAC THEN
ASM_REWRITE_TAC[] THEN
REPEAT WEAKEN_HD_TAC THEN REPEAT STRIP_TAC THEN
ASM_SIMP_TAC arith_ss [from_reg_index_thm, index_of_reg_def]);


val MREG2REG_EVAL =
	store_thm ("MREG2REG_EVAL", ``
	(MREG2REG R0 = 0w) /\
	(MREG2REG R1 = 1w) /\
	(MREG2REG R2 = 2w) /\
	(MREG2REG R3 = 3w) /\
	(MREG2REG R4 = 4w) /\
	(MREG2REG R5 = 5w) /\
	(MREG2REG R6 = 6w) /\
	(MREG2REG R7 = 7w) /\
	(MREG2REG R8 = 8w) /\
	(MREG2REG R9 = 9w) /\
	(MREG2REG R10 = 10w) /\
	(MREG2REG R11 = 11w) /\
	(MREG2REG R12 = 12w) /\
	(MREG2REG R13 = 13w) /\
	(MREG2REG R14 = 14w)``, EVAL_TAC);

val state2reg_fun2mread =
	store_thm ("state2reg_fun2mread",

``!st r. (state2reg_fun st (MREG2REG r) = mread st (RR r))``,

Cases_on `st` THEN
SIMP_TAC std_ss [state2reg_fun_def, rulesTheory.mread_def, read_thm,
	toREG_def, GSYM MREG2REG_def, MREG_NOT_PC]);


val state2reg_fun2mread2 =
	store_thm ("state2reg_fun2mread2",

``!st r. (~(r = 15w)) ==> (state2reg_fun st r = mread st (RR (from_reg_index (w2n r))))``,

Cases_on `st` THEN
SIMP_TAC std_ss [state2reg_fun_def, rulesTheory.mread_def, read_thm,
	toREG_def] THEN
REPEAT STRIP_TAC THEN
`w2n r' < 16` by METIS_TAC[dimword_4, w2n_lt] THEN
Cases_on `w2n r' = 15` THEN1 PROVE_TAC[n2w_w2n] THEN
`w2n r' < 15` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss [index_of_reg___from_reg_index, n2w_w2n]);



val arm_mem_state2reg_fun2REG_READ =
	store_thm ("arm_mem_state2reg_fun2REG_READ",

``!state r. (arm_mem_state2reg_fun state (MREG2REG r) = REG_READ state.registers (DECODE_MODE ((4 >< 0) (CPSR_READ state.psrs))) (MREG2REG r))``,

SIMP_TAC std_ss [arm_mem_state2reg_fun_def, armTheory.REG_READ_def, LET_THM,
MREG_NOT_PC]);



val MEM_FST_UNZIP = store_thm ("MEM_FST_UNZIP",
``!l x. MEM x1 (FST (UNZIP l)) =
		(?x2. MEM (x1, x2) l)``,

Induct_on `l` THENL [
	ASM_SIMP_TAC list_ss [],

	ASM_SIMP_TAC list_ss [] THEN
	METIS_TAC[FST, PAIR]
]);


val ALL_DISTINCT_IMPLIES_FILTER = store_thm ("ALL_DISTINCT_IMPLIES_FILTER", ``
!l P. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)``,

Induct_on `l` THENL [
	SIMP_TAC list_ss [],
	ASM_SIMP_TAC list_ss [COND_RATOR, COND_RAND, MEM_FILTER]
])

val SUBSET_DIFF = store_thm ("SUBSET_DIFF",
``!s t u. (s SUBSET (t DIFF u)) = (s SUBSET t /\ DISJOINT s u)``,
SIMP_TAC std_ss [SUBSET_DEF, DISJOINT_DEF, IN_DIFF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN METIS_TAC[])


val PAIR_EQ_ELIM =
prove (``!x y z. ((x, y) = z) = ((x = FST z) /\ (y = SND z))``,
				METIS_TAC[PAIR, FST, SND])


val LIST_TO_FUN_def =
	Define `((LIST_TO_FUN s [] e) = s) /\
			  ((LIST_TO_FUN s ((h1, h2)::l) e) =
					if (h1 = e) then h2 else
				   (LIST_TO_FUN s l e))`;

val WORD_ADD_INV_0_EQ_SYM	= prove (``!v w. (v = v + w) = (w = 0w)``, PROVE_TAC[WORD_ADD_INV_0_EQ]);

val ELIM_PFORALL_PEXISTS = prove (
   ``((!p. P p (FST p) (SND p)) = !p1 p2. P (p1, p2) p1 p2) /\
     ((?p. P p (FST p) (SND p)) = ?p1 p2. P (p1, p2) p1 p2)``,
   METIS_TAC[PAIR, FST, SND])


(*
val TRANSLATION_SPEC_SEP_thm = store_thm ("TRANSLATION_SPEC_SEP_thm",
``!prog uregs oregs f tprog uregs_words unknown_changed_regs_list stat rv9 rv8 rv7
          rv6 rv5 rv4 rv3 rv2 rv14 rv13 rv12 rv11 rv10 rv1 rv0 regs_list
          output_regs_list oregs_words input_regs_list.

  (~(CONTAINS_MEMORY_DOPER prog) /\ (WELL_FORMED prog) /\    (IS_WELL_FORMED_CTL_STRUCTURE prog) /\ (UNCHANGED uregs prog) /\
   (CTL_STRUCTURE2INSTRUCTION_LIST prog = tprog) /\
	(LENGTH tprog < 2**(dimindex (:24) - 1) -1) /\
  (!st r. (MEM r oregs_words) ==> ((state2reg_fun (run_ir prog st) r) = ((f (state2reg_fun st)) r))) /\
  (!f1 f2. (!q. MEM q input_regs_list ==> (f1 (FST q) = f2 (FST q))) ==>
			  (!r. MEM r oregs_words ==> (f f1 r = f f2 r))) /\
  ([(0w:word4, rv0); (1w:word4, rv1); (2w:word4, rv2); (3w:word4, rv3);
	(4w:word4, rv4); (5w:word4, rv5); (6w:word4, rv6); (7w:word4, rv7);
	(8w:word4, rv8); (9w:word4, rv9); (10w:word4, rv10); (11w:word4, rv11);
	(12w:word4, rv12); (13w:word4, rv13); (14w:word4, rv14)] = regs_list) /\
  (!x. MEM x oregs ==> ~MEM x uregs) /\
  (MAP MREG2REG uregs = uregs_words) /\
  (MAP MREG2REG oregs = oregs_words) /\
  (FILTER (\x. ~ (MEM (FST x) uregs_words)) regs_list = input_regs_list) /\
  ((FILTER (\x. (MEM (FST x) oregs_words)) (MAP (\(r, v). (r, f (LIST_TO_FUN 0w regs_list) r)) regs_list)) = output_regs_list) /\
  (FILTER (\x. ~(MEM x oregs_words)) (MAP FST input_regs_list) = unknown_changed_regs_list)
	) ==>

	ARM_PROG ((reg_spec input_regs_list) * (S stat)) (MAP enc tprog) {} ((reg_spec output_regs_list)*(ereg_spec unknown_changed_regs_list) * (SEP_EXISTS stat. S stat)) {}``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [GSYM ARM_PROG_INTRO1, dimindex_24, LENGTH_MAP] THEN
GEN_TAC THEN
MATCH_MP_TAC IMP_ARM_RUN THEN
SIMP_TAC std_ss [RIGHT_EXISTS_AND_THM, Once SWAP_EXISTS_THM] THEN

Q_TAC EXISTS_TAC `((15w:word4) INSERT (LIST_TO_SET (MAP FST input_regs_list)), BIGUNION (IMAGE (\e. ({(addr32 (p + n2w e) + 0w); (addr32 (p + n2w e) + 1w); (addr32 (p + n2w e) + 2w); (addr32 (p + n2w e) + 3w)})) (count (LENGTH tprog))), T, T, F)` THEN
SUBGOAL_TAC `ALL_DISTINCT output_regs_list /\ ALL_DISTINCT input_regs_list /\ ALL_DISTINCT unknown_changed_regs_list` THEN1 (
	Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
	Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
	Q_TAC GSYM_DEF_TAC `regs_list` THEN
	Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
	ASM_SIMP_TAC std_ss [MAP]  THEN
	REPEAT STRIP_TAC THENL [
		MATCH_MP_TAC ALL_DISTINCT_IMPLIES_FILTER THEN
		REWRITE_TAC [ALL_DISTINCT, preARMTheory.word4_distinct, MEM,
			PAIR_EQ],

		MATCH_MP_TAC ALL_DISTINCT_IMPLIES_FILTER THEN
		REWRITE_TAC [ALL_DISTINCT, preARMTheory.word4_distinct, MEM,
			PAIR_EQ],

		MATCH_MP_TAC ALL_DISTINCT_IMPLIES_FILTER THEN
		`(\x:(word4 # word32). ~MEM (FST x) uregs_words) =
		  (\x. ~MEM x uregs_words) o FST` by SIMP_TAC std_ss [combinTheory.o_DEF] THEN
		ASM_SIMP_TAC std_ss [GSYM FILTER_MAP, MAP] THEN
		MATCH_MP_TAC ALL_DISTINCT_IMPLIES_FILTER THEN
		REWRITE_TAC [ALL_DISTINCT, preARMTheory.word4_distinct, MEM]
	]
) THEN

STRIP_TAC THENL [
   ASM_SIMP_TAC list_ss [GSYM STAR_ASSOC, reg_spec_thm] THEN

	ASM_SIMP_TAC arith_ss [LENGTH_MAP, ARMpc_def, ms_STAR___ZERO, R30_def, R_def, S_def, one_STAR, GSYM STAR_ASSOC, IN_DIFF, IN_DELETE, ARMel_distinct, SUBSET_DIFF, SUBSET_DELETE, ELIM_PFORALL_PEXISTS] THEN
	REPEAT STRIP_TAC THEN
	UNDISCH_HD_TAC THEN

	SUBGOAL_TAC `LIST_TO_SET (MAP (\(r,v). Reg r v) input_regs_list) SUBSET t` THEN1 (
		FULL_SIMP_TAC list_ss [SUBSET_DEF, MEM_MAP, EVERY_MEM] THEN
		REPEAT STRIP_TAC THEN
		RES_TAC THEN
		Cases_on `y` THEN
		FULL_SIMP_TAC std_ss []
	) THEN
	ASM_SIMP_TAC list_ss [arm2set'_def, one_def, DELETE_EQ_ELIM, IN_DIFF, IN_SING, ARMel_distinct, DIFF_EQ_ELIM, SUBSET_DIFF, SUBSET_DELETE, SUBSET_UNION, IN_DELETE] THEN
	SIMP_TAC std_ss [Once (EQ_SYM_EQ)] THEN

   FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, ELIM_PFORALL_PEXISTS] THEN
	REPEAT STRIP_TAC THEN
	Q.PAT_ASSUM `t SUBSET arm2set s` (fn thm => MP_TAC thm) THEN
   SIMP_TAC std_ss [Once EXTENSION] THEN
	ASM_SIMP_TAC list_ss [GSYM RIGHT_EXISTS_AND_THM, IN_UNION, GSPECIFICATION, IN_INSERT, LEFT_AND_OVER_OR, EXISTS_OR_THM, NOT_IN_EMPTY, SUBSET_DEF, DISJ_IMP_THM, FORALL_AND_THM, IN_arm2set, MEM_MAP, GSYM LEFT_FORALL_IMP_THM, MEM_ENUMERATE, IN_BIGUNION, IN_LIST_TO_SET, ELIM_PFORALL_PEXISTS, M_set_thm,
   GSYM RIGHT_EXISTS_AND_THM, IN_IMAGE, IN_COUNT, prove (``((a:bool \/ b) /\ c) = ((a /\ c) \/ (b /\ c))``, PROVE_TAC[]),
   mem_byte_addr32] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [ARMel_distinct, ARMel_11] THENL [
      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `p1` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `p1` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `p1` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `p1` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

		METIS_TAC[],
		METIS_TAC[],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `e` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `e` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `e` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set],

      SIMP_TAC std_ss [GSYM EXISTS_OR_THM] THEN
      Q.EXISTS_TAC `e` THEN
      ASM_SIMP_TAC std_ss [addr32_11, addr32_NEQ_addr32, IN_arm2set]
   ],


	ASM_SIMP_TAC list_ss [GSYM STAR_ASSOC, reg_spec_thm, ereg_spec_thm, RIGHT_EXISTS_IMP_THM, WD_ARM_arm2set', WD_ARM_DIFF] THEN
	ASM_SIMP_TAC arith_ss [ms_STAR___ZERO, LENGTH_MAP, ARMpc_def, R30_def, R_def, S_def, one_STAR, GSYM STAR_ASSOC, IN_DIFF, IN_DELETE, ARMel_distinct, SUBSET_DIFF, SUBSET_DELETE, SEP_EXISTS_ABSORB_STAR, SEP_EXISTS_THM, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
	REPEAT STRIP_TAC THEN
	UNDISCH_HD_TAC THEN

	SUBGOAL_TAC `LIST_TO_SET (MAP (\(r,v). Reg r v) input_regs_list) SUBSET
		(arm2set'
       (15w INSERT LIST_TO_SET (MAP FST input_regs_list),
        BIGUNION
           (IMAGE
              (\e.
                 {addr32 (p + n2w e) + 0w; addr32 (p + n2w e) + 1w;
                  addr32 (p + n2w e) + 2w; addr32 (p + n2w e) + 3w})
              (count (LENGTH tprog))),T,T,F) s)` THEN1 (
		FULL_SIMP_TAC list_ss [SUBSET_DEF, MEM_MAP, EVERY_MEM,
			GSYM LEFT_FORALL_IMP_THM, IN_arm2set'] THEN
		Cases_on `y` THEN
		ASM_SIMP_TAC std_ss [IN_arm2set', IN_INSERT, IN_LIST_TO_SET, MEM_MAP] THEN
		REPEAT STRIP_TAC THENL [
			RES_TAC THEN
			FULL_SIMP_TAC std_ss [],

			METIS_TAC[FST, SND, PAIR]
		]
	) THEN
	ASM_SIMP_TAC list_ss [one_def, DELETE_EQ_ELIM, IN_DIFF, IN_SING, ARMel_distinct, DIFF_EQ_ELIM, SUBSET_DIFF, SUBSET_DELETE, SUBSET_UNION, IN_DELETE] THEN
	REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `X = arm2set' Y s` (fn thm => ASSUME_TAC (GSYM thm)) THEN
   FULL_SIMP_TAC std_ss [] THEN
	ASSUME_TAC (SIMP_RULE std_ss [dimindex_24] TRANSLATION_SPEC_thm) THEN
	Q_SPECL_NO_ASSUM 0 [`prog`, `\st st'. (EVERY (\r. st' r = f st r) oregs_words /\ EVERY (\r. ~(r = 15w) ==> (st' r = st r)) uregs_words)`, `s`] THEN
	PROVE_CONDITION_NO_ASSUM 0 THEN1 (
		Q_TAC GSYM_DEF_TAC `uregs_words` THEN
		ASM_SIMP_TAC std_ss [EVERY_MEM] THEN
		FULL_SIMP_TAC std_ss [SET_EQ_SUBSET, UNCHANGED_THM, toREG_def, read_thm, EVERY_MEM, MEM_MAP, MREG2REG_def] THEN
		CONJ_TAC THENL [
			REPEAT STRIP_TAC THEN
			`?st'. (run_ir prog st) = st'` by PROVE_TAC[] THEN
			Cases_on `st` THEN Cases_on `st'` THEN
			Q_TAC GSYM_DEF_TAC `r` THEN
			ASM_SIMP_TAC std_ss [state2reg_fun_def] THEN
			`q ' r = read (run_ir prog (q,r')) (REG (index_of_reg y))` by METIS_TAC[] THEN
			ASM_REWRITE_TAC[read_thm],


			Q.PAT_ASSUM `Y SUBSET arm2set' X s` MP_TAC THEN
			SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_LIST_TO_SET, MEM_MAP, DISJ_IMP_THM,
			FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM, MEM_ENUMERATE, IN_INSERT, NOT_IN_EMPTY, IN_arm2set'] THEN
			FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, ELIM_PFORALL_PEXISTS,
            GSYM RIGHT_EXISTS_AND_THM, MEM_ENUMERATE, LENGTH_MAP,
            GSYM LEFT_FORALL_IMP_THM] THEN
         REPEAT STRIP_TAC THEN
         POP_NO_ASSUM 2 (fn thm => MP_TAC (Q.GEN `x` (Q.SPECL [`x`, `e`] thm))) THEN
         `!e'. ((e = e' MOD 1073741824) /\ e' < LENGTH tprog) = (e' = e)` by ALL_TAC THEN1 (
            GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC arith_ss []
         ) THEN
         ASM_SIMP_TAC arith_ss [M_set_thm, IN_INSERT, NOT_IN_EMPTY, DISJ_IMP_THM, FORALL_AND_THM,
            IN_arm2set', IN_BIGUNION, IN_IMAGE, IN_COUNT, GSYM RIGHT_EXISTS_AND_THM,
            addr32_NEQ_addr32, addr32_11, WORD_EQ_ADD_LCANCEL, n2w_11, dimword_30,
            GSYM mem_byte_EQ_mem, GSYM mem_def, EL_MAP] THEN
         `addr32 (p + n2w e) = addr32 (ADDR30 (FETCH_PC s.registers + n2w (4 * e)))` by ALL_TAC THENL [
            ALL_TAC,
            ASM_SIMP_TAC std_ss []
         ] THEN
         SIMP_TAC std_ss [addr32_11, armTheory.FETCH_PC_def, systemTheory.ADDR30_def, MEM_ADDR_ADD_CONST_MULT,
            GSYM MEM_ADDR_def, MULT_COMM, WORD_EQ_ADD_RCANCEL] THEN
         Q.PAT_ASSUM `addr32 p = X` (fn thm => MP_TAC (GSYM thm)) THEN
         SIMP_TAC std_ss [reg_def, MEM_ADDR_def, GSYM addr30_def, addr30_addr32]
		]
	) THEN
	FULL_SIMP_TAC std_ss [] THEN
	EXISTS_TAC ``step_num:num`` THEN
	EXISTS_TAC ``status (STATE_ARM_MEM step_num s)`` THEN
	SIMP_TAC std_ss [CONJ_ASSOC] THEN
	MATCH_MP_TAC (prove (``(a /\ (a ==> b)) ==> (a /\ b)``, PROVE_TAC[])) THEN
	REPEAT STRIP_TAC THENL [
		ASM_SIMP_TAC std_ss [arm2set''_EQ, mem_def] THEN
		CONJ_TAC THENL [
         Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
         ASM_SIMP_TAC std_ss [IN_INSERT, IN_LIST_TO_SET, MEM_MAP, MEM_FILTER,
            GSYM FORALL_AND_THM] THEN
         REPEAT STRIP_TAC THEN
         SUBGOAL_TAC `MEM r uregs_words` THEN1 (
            REMAINS_TAC `?x. MEM (r, x) regs_list` THEN1 METIS_TAC[FST, SND, PAIR] THEN
            `r IN UNIV` by REWRITE_TAC[IN_UNIV] THEN
            UNDISCH_HD_TAC THEN
            SIMP_TAC std_ss [WORD_UNIV_IMAGE_COUNT, dimword_4] THEN
            CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
            REWRITE_TAC[COUNT_SUC, COUNT_ZERO] THEN
            SIMP_TAC std_ss [IN_IMAGE, IN_INSERT, NOT_IN_EMPTY, LEFT_AND_OVER_OR,
               EXISTS_OR_THM, DISJ_IMP_THM] THEN

            Q_TAC GSYM_DEF_TAC `regs_list` THEN
            ASM_SIMP_TAC list_ss [preARMTheory.word4_distinct]
         ) THEN
         FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
         Q_SPEC_NO_ASSUM 10 `r` THEN
         UNDISCH_HD_TAC THEN
         ASM_SIMP_TAC std_ss [arm_mem_state2reg_fun_def, reg_def, LET_THM,
            armTheory.REG_READ_def, state_mode_def],


			RW_TAC std_ss [owrt_visible_def] THEN
			ASM_SIMP_TAC std_ss [set_status_def, arm_evalTheory.SET_NZCV_IDEM,
				arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.CPSR_WRITE_WRITE,
            mem_byte_def, arm_progTheory.mem_def]
		],


		Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
		ASM_SIMP_TAC std_ss [EVERY_MEM, MAP, MEM_FILTER, MEM_MAP] THEN
		Cases_on `e` THEN
		SIMP_TAC std_ss [IN_arm2set', IN_INSERT, IN_LIST_TO_SET, MEM_MAP] THEN
		STRIP_TAC THEN
		SUBGOAL_TAC `(~(q = 15w)) /\ (r = f (LIST_TO_FUN 0w regs_list) q)` THEN1 (
			NTAC 2 UNDISCH_HD_TAC THEN
			Cases_on `y` THEN
			Q_TAC GSYM_DEF_TAC `regs_list` THEN
			ASM_SIMP_TAC list_ss [DISJ_IMP_THM, preARMTheory.word4_distinct]
		) THEN
		REPEAT STRIP_TAC THENL [
			FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
			Q.PAT_ASSUM `!r. (MEM r oregs_words) ==> P r` (fn thm => MP_TAC (ISPEC ``q:word4`` thm)) THEN
			ASM_SIMP_TAC std_ss [arm_mem_state2reg_fun_def,LET_THM, reg_def, armTheory.REG_READ_def, arm_evalTheory.CPSR_WRITE_READ,
			arm_evalTheory.DECODE_IFMODE_SET_NZCV, state_mode_def] THEN
			REPEAT STRIP_TAC THEN
			Q.PAT_ASSUM `!f1 f2. P f1 f2` (fn thm => MATCH_MP_TAC
				(SIMP_RULE std_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] thm)) THEN
			FULL_SIMP_TAC std_ss [SET_EQ_SUBSET] THEN
			Q.PAT_ASSUM `Y SUBSET arm2set' X s` MP_TAC THEN
			SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_LIST_TO_SET, DISJ_IMP_THM,
				FORALL_AND_THM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
			REPEAT STRIP_TAC THEN
			Q_SPEC_NO_ASSUM 1 `q'`  THEN
			UNDISCH_HD_TAC THEN
			pairLib.GEN_BETA_TAC THEN
			UNDISCH_HD_TAC THEN
			Q_TAC GSYM_DEF_TAC `regs_list` THEN
			Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
			ASM_SIMP_TAC std_ss [IN_arm2set', MEM_FILTER, reg_def, armTheory.REG_READ_def, state_mode_def] THEN
			REPEAT STRIP_TAC THEN
			SUBGOAL_TAC `~(FST q' = 15w)` THEN1 (
				UNDISCH_NO_TAC 2 THEN
				SIMP_TAC list_ss [DISJ_IMP_THM, word4_distinct]
			) THEN
			FULL_SIMP_TAC std_ss [] THEN
			POP_NO_ASSUM 2 (fn thm => ASSUME_TAC (GSYM thm)) THEN
			ASM_REWRITE_TAC[] THEN
			UNDISCH_NO_TAC 3 THEN
			SIMP_TAC list_ss [DISJ_IMP_THM, word4_distinct,LIST_TO_FUN_def],


			ASM_REWRITE_TAC[] THEN
			SUBGOAL_TAC `~(MEM q uregs_words)` THEN1 (
				Q.PAT_ASSUM `MEM q oregs_words` MP_TAC THEN
				Q_TAC GSYM_DEF_TAC `oregs_words` THEN
				Q_TAC GSYM_DEF_TAC `uregs_words` THEN
				ASM_SIMP_TAC std_ss [MEM_MAP] THEN
				METIS_TAC[MREG2REG_11]
			) THEN
			Q_TAC EXISTS_TAC `y` THEN
			Cases_on `y` THEN
			Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
			FULL_SIMP_TAC std_ss [MEM_FILTER] THEN
			PROVE_TAC[]
		],


		Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
		ASM_SIMP_TAC std_ss [EVERY_MEM, MEM_FILTER, MEM_MAP, IN_arm2set',
			IN_INSERT, IN_LIST_TO_SET] THEN
		pairLib.GEN_BETA_TAC THEN
		SIMP_TAC std_ss [ARMel_11] THEN
		REPEAT STRIP_TAC THEN
		Cases_on `y` THEN Cases_on `y'` THEN
		FULL_SIMP_TAC std_ss [] THEN
		Cases_on `q = q'` THEN ASM_REWRITE_TAC[] THEN
		Cases_on `r'' = arm_prog$reg q' (STATE_ARM_MEM step_num s)` THEN ASM_SIMP_TAC std_ss [] THEN
		Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
		FULL_SIMP_TAC std_ss [MEM_FILTER],


		SIMP_TAC std_ss [IN_arm2set'],

		UNDISCH_HD_TAC THEN
		SIMP_TAC std_ss [MEM_MAP] THEN
		pairLib.GEN_BETA_TAC THEN
		SIMP_TAC std_ss [ARMel_distinct],

		UNDISCH_HD_TAC THEN
		SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, GSYM IMP_DISJ_THM,
			EXTENSION, IN_DEF] THEN
		METIS_TAC [ARMel_distinct],


      UNDISCH_HD_TAC THEN
      SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, MEM_ENUMERATE, ELIM_PFORALL_PEXISTS, GSYM RIGHT_FORALL_OR_THM, M_set_thm, IN_INSERT, NOT_IN_EMPTY, ARMel_distinct],



		FULL_SIMP_TAC std_ss [SET_EQ_SUBSET, UNION_SUBSET, INSERT_SUBSET, EMPTY_SUBSET] THEN
		Q.PAT_ASSUM `BIGUNION Y SUBSET arm2set' X s` MP_TAC THEN
      MATCH_MP_TAC (prove (``(!e. e IN S1 ==> (e IN S2 = e IN S3)) ==> ((S1 SUBSET S2) ==> (S1 SUBSET S3))``, PROVE_TAC[SUBSET_DEF])) THEN
      SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, MEM_ENUMERATE, ELIM_PFORALL_PEXISTS,
         GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM, LENGTH_MAP] THEN
      REPEAT GEN_TAC THEN
      Cases_on `p1 < LENGTH tprog` THEN ASM_REWRITE_TAC[] THEN
      `!e'. ((p1 = e' MOD 1073741824) /\ e' < LENGTH tprog) = (e' = p1)` by ALL_TAC THEN1 (
         GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC arith_ss []
      ) THEN
      ASM_SIMP_TAC arith_ss [M_set_thm, IN_INSERT, NOT_IN_EMPTY, DISJ_IMP_THM, IN_arm2set', IN_BIGUNION, IN_IMAGE,
         GSYM RIGHT_EXISTS_AND_THM, addr32_NEQ_addr32, addr32_11, IN_COUNT, WORD_EQ_ADD_LCANCEL,
         n2w_11, dimword_30, mem_byte_def, mem_def],


		SIMP_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY, IN_INTER, IN_LIST_TO_SET, MEM_MAP,
         IN_BIGUNION, ELIM_PFORALL_PEXISTS, MEM_ENUMERATE, LENGTH_MAP,
         GSYM RIGHT_FORALL_OR_THM, M_set_thm, IN_INSERT, ARMel_distinct],

      MATCH_MP_TAC (prove (``(!e. e IN S1 ==> ~(e IN S2)) ==> DISJOINT S1 S2``, SIMP_TAC std_ss [IN_DISJOINT] THEN PROVE_TAC[])) THEN
      SIMP_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY, IN_INTER, IN_LIST_TO_SET, MEM_MAP,
         IN_BIGUNION, ELIM_PFORALL_PEXISTS, MEM_ENUMERATE, LENGTH_MAP, M_set_thm, IN_INSERT,
         GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT GEN_TAC THEN
      Cases_on `p1 < LENGTH tprog` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [DISJ_IMP_THM, IN_DEF, ARMel_distinct],




		FULL_SIMP_TAC list_ss [IN_arm2set', IN_INSERT, reg_def, armTheory.FETCH_PC_def,
			pcINC_def, pcADD_def, wLENGTH_def, addr32_ADD, addr32_n2w] THEN
		FULL_SIMP_TAC std_ss [SET_EQ_SUBSET] THEN
		Q.PAT_ASSUM `Y SUBSET arm2set' X s` MP_TAC THEN
		SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
			DISJ_IMP_THM, FORALL_AND_THM, IN_arm2set', reg_def] THEN
		PROVE_TAC[WORD_ADD_COMM],


		UNDISCH_HD_TAC THEN
		Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
		Q_TAC GSYM_DEF_TAC `regs_list` THEN
		ASM_SIMP_TAC std_ss [MEM_MAP, MEM_FILTER] THEN
		Cases_on `y` THEN
		SIMP_TAC std_ss [ARMel_11] THEN
		Cases_on `q = 15w` THEN ASM_SIMP_TAC std_ss [] THEN
		DISJ2_TAC THEN DISJ2_TAC THEN
		Cases_on `y'` THEN
		SIMP_TAC std_ss [] THEN
		Cases_on `q' = 15w` THEN ASM_SIMP_TAC std_ss [] THEN
		DISJ2_TAC THEN
		SIMP_TAC std_ss [MEM, preARMTheory.word4_distinct],



		UNDISCH_HD_TAC THEN
		Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
		Q_TAC GSYM_DEF_TAC `regs_list` THEN
		ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, MEM_FILTER] THEN
		REPEAT STRIP_TAC THEN
		Cases_on `Reg 15w (addr32 (pcINC (MAP enc tprog) p)) IN s'` THEN ASM_REWRITE_TAC[] THEN
		GEN_TAC THEN
		Cases_on `r = 15w` THENL [
			DISJ2_TAC THEN DISJ2_TAC THEN
			Cases_on `y` THEN
			SIMP_TAC std_ss [] THEN
			Cases_on `q = r` THEN ASM_SIMP_TAC std_ss [] THEN
			Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
			ASM_REWRITE_TAC[MEM_FILTER, MEM, PAIR_EQ, word4_distinct],


			DISJ1_TAC THEN
			SIMP_TAC std_ss [EXTENSION] THEN
			Q_TAC EXISTS_TAC `Reg 15w (addr32 (pcINC (MAP enc tprog) p))` THEN
			ASM_SIMP_TAC std_ss [IN_DEF, ARMel_11]
		],


		UNDISCH_HD_TAC THEN
		SIMP_TAC std_ss [MEM_MAP, IN_BIGUNION, IN_LIST_TO_SET,
         GSYM RIGHT_FORALL_OR_THM, ELIM_PFORALL_PEXISTS, M_set_thm, IN_INSERT, ARMel_distinct,
         NOT_IN_EMPTY],


		SIMP_TAC std_ss [EXTENSION, IN_SING, IN_DELETE, IN_DIFF] THEN
      `!p1 e. (p1 < LENGTH tprog) ==>
               (((((n2w p1):word30) = n2w e) /\
                e < LENGTH tprog) = (e = p1))` by ALL_TAC THEN1 (
         REPEAT STRIP_TAC THEN
         EQ_TAC THEN
         ASM_SIMP_TAC arith_ss [n2w_11, dimword_30]
      ) THEN
      FULL_SIMP_TAC std_ss [prove (``DISJOINT S1 S2 = (!e. e IN S1 ==> (~(e IN S2)))``, SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN PROVE_TAC[]),
         IN_BIGUNION, IN_LIST_TO_SET, MEM_MAP, IN_arm2set', IN_INSERT, ELIM_PFORALL_PEXISTS,
         SUBSET_DEF, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, MEM_ENUMERATE, LENGTH_MAP,
         GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_OR_THM,
         prove (``e IN (\e. P e) = P e``, SIMP_TAC std_ss [IN_DEF]), ARMel_11, ARMel_distinct,
         M_set_thm, NOT_IN_EMPTY, DISJ_IMP_THM, IN_UNION, FORALL_AND_THM,
         RIGHT_AND_OVER_OR, IN_IMAGE, addr32_NEQ_addr32, addr32_11, WORD_EQ_ADD_LCANCEL,
         IN_COUNT] THEN
		GEN_TAC THEN
		Cases_on `x = Undef F` THENL [
			ASM_SIMP_TAC std_ss [IN_arm2set', ARMel_distinct],

         ASM_SIMP_TAC std_ss [] THEN
         REWRITE_TAC[GSYM DISJ_ASSOC] THEN
			MATCH_MP_TAC (prove (``(~a ==> b) ==> (a \/ b)``, PROVE_TAC[])) THEN
			SIMP_TAC std_ss [arm2set'_def, IN_UNION, GSPECIFICATION, IN_INSERT, IN_BIGUNION, NOT_IN_EMPTY,
            DISJ_IMP_THM, FORALL_AND_THM, ARMel_distinct, GSYM LEFT_FORALL_IMP_THM, IN_IMAGE,
            GSYM RIGHT_EXISTS_AND_THM, IN_COUNT, RIGHT_AND_OVER_OR, ARMel_11, GSYM RIGHT_EXISTS_IMP_THM,
            IN_LIST_TO_SET, MEM_MAP, ELIM_PFORALL_PEXISTS] THEN
         REPEAT CONJ_TAC THENL [
              GEN_TAC THEN
              Cases_on `a = 15w` THEN ASM_SIMP_TAC std_ss [] THEN
              Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
              Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
              Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
              Q.PAT_ASSUM `EVERY P output_regs_list` MP_TAC THEN
              ASM_SIMP_TAC std_ss [MEM_MAP, MEM_FILTER, ELIM_PFORALL_PEXISTS, EVERY_MEM] THEN
              Cases_on `MEM a oregs_words` THEN ASM_SIMP_TAC std_ss [] THEN
              METIS_TAC[],


              REPEAT GEN_TAC THEN
              Q.EXISTS_TAC `e` THEN
              Cases_on `e < LENGTH tprog` THEN ASM_SIMP_TAC std_ss [] THEN
              SIMP_TAC std_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM],


              ASM_SIMP_TAC std_ss []
          ]
      ]
	]
])


*)










val SPEC_LIST___MS_PC = prove (``
!xs ys st x y rt z cd b a w p.
(spec_list xs ys (st,x) (F,y) (rt,z) (cd,b) *
 ms a w * ARMpc p) =
(spec_list ((15w, SOME (addr32 p))::xs) (xM_seq (a, w)::ys) (st,x) (T,F) (rt,z) (cd,b))``,

SIMP_TAC (std_ss++star_ss) [spec_list_def, xR_list_def, rest_list_def, xM_list_def,
   ARMpc_def, R30_def, emp_STAR]);



val ms_sem_THM = prove (``
!p tprog s.
(ms_sem p (MAP enc tprog) s) =
(!e. (e < LENGTH tprog) ==> (s.memory (ADDR30 (addr32 p + n2w (e * 4))) = enc (EL e tprog)))``,

Induct_on `tprog` THENL [
   SIMP_TAC list_ss [ms_sem_def],

   ASM_SIMP_TAC list_ss [ms_sem_def, arm_progTheory.mem_def] THEN
   WEAKEN_HD_TAC THEN
   SUBGOAL_TAC `!p n. addr32 p + n2w (4 * SUC n) = addr32 (p + 1w) + n2w (4 * n)` THEN1 (
      REPEAT WEAKEN_HD_TAC THEN
      SIMP_TAC std_ss [addr32_def] THEN
      WORDS_TAC THEN
      SIMP_TAC arith_ss [bitTheory.TIMES_2EXP_def, word_add_def, w2n_n2w, dimword_30] THEN
      SIMP_TAC arith_ss [GSYM word_add_n2w, n2w_w2n, MOD_COMMON_FACTOR, SUC_ONE_ADD, LEFT_ADD_DISTRIB] THEN
      REPEAT GEN_TAC THEN
      CONV_TAC (LHS_CONV (SIMP_CONV std_ss [Once (GSYM MOD_PLUS)])) THEN
      CONV_TAC (RHS_CONV (SIMP_CONV std_ss [Once (GSYM MOD_PLUS)])) THEN
      REWRITE_TAC[]
   ) THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Cases_on `e` THENL [
         ASM_SIMP_TAC list_ss [WORD_ADD_0, systemTheory.ADDR30_def, GSYM arm_progTheory.addr30_def,
         addr30_addr32],

         FULL_SIMP_TAC list_ss []
      ],

      `0 < SUC (LENGTH tprog)` by SIMP_TAC list_ss [] THEN
      RES_TAC THEN
      FULL_SIMP_TAC list_ss [WORD_ADD_0, systemTheory.ADDR30_def, GSYM arm_progTheory.addr30_def,
         addr30_addr32],

      `SUC e < SUC (LENGTH tprog)` by ASM_SIMP_TAC std_ss [] THEN
      RES_TAC THEN
      FULL_SIMP_TAC list_ss [] THEN
      METIS_TAC[]
   ]
])


val xR_list_sem_APPEND = prove (
   ``!l1 l2 s. xR_list_sem (l1 ++ l2) s =
             xR_list_sem l1 s /\ xR_list_sem l2 s``,
   Induct_on `l1` THENL [
      SIMP_TAC list_ss [xR_list_sem_def],

      Cases_on `h` THEN Cases_on `r` THEN
      ASM_SIMP_TAC std_ss [APPEND, xR_list_sem_def, CONJ_ASSOC]
   ])

val xR_list_sem_NONE = prove (
   ``!l s. xR_list_sem (MAP (\x. (x, NONE)) l) s``,

   Induct_on `l` THEN
   ASM_SIMP_TAC list_ss [xR_list_sem_def])

val xR_list_sem_SOME = prove (
   ``!l s. xR_list_sem (MAP (\(x, y). (x, SOME y)) l) s =
      EVERY (\(x,y). arm_prog$reg x s = y) l``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [xR_list_sem_def],

      Cases_on `h` THEN
      ASM_SIMP_TAC list_ss [xR_list_sem_def]
   ])

val ms_sem_MEMORY = prove (
   ``!a xs s1 s2. (s1.memory = s2.memory) ==>
         (ms_sem a xs s1 = ms_sem a xs s2)``,

   Induct_on `xs` THEN (
      ASM_SIMP_TAC list_ss [ms_sem_def, arm_progTheory.mem_def] THEN
      PROVE_TAC[]
   ))


val ALL_DISTINCT_APPEND = store_thm ("ALL_DISTINCT_APPEND",
   ``!l1 l2. ALL_DISTINCT (l1++l2) =
             (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
             (!e. MEM e l1 ==> ~(MEM e l2)))``,

   Induct_on `l1` THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
      PROVE_TAC[]
   ])

val spec_list_expand_ss = rewrites
  [spec_list_def,xR_list_def,xM_list_def,rest_list_def,spec_list_sem_def,
   xR_list_sem_def,xM_list_sem_def,rest_list_sem_def,ms_sem_def,
   xM_list_addresses_def,ms_address_set_def,spec_list_select_def,
   xM_list_address_set_def,FOLDR,UNION_EMPTY,UNION_APPEND,GSYM
CONJ_ASSOC,ms_def,
   MAP,FST,STAR_ASSOC,EVAL ``SUC 0 <= 2**30``,LENGTH,blank_ms_def];

val TRANSLATION_SPEC_SEP_thm = store_thm ("TRANSLATION_SPEC_SEP_thm",
``!prog uregs oregs f tprog uregs_words unknown_changed_regs_list stat rv9 rv8 rv7
          rv6 rv5 rv4 rv3 rv2 rv14 rv13 rv12 rv11 rv10 rv1 rv0 regs_list
          output_regs_list oregs_words input_regs_list.

  (~(CONTAINS_MEMORY_DOPER prog) /\ (WELL_FORMED prog) /\    (IS_WELL_FORMED_CTL_STRUCTURE prog) /\ (UNCHANGED uregs prog) /\
   (CTL_STRUCTURE2INSTRUCTION_LIST prog = tprog) /\
   (LENGTH tprog < 2**(dimindex (:24) - 1) -1) /\
  (!st r. (MEM r oregs_words) ==> ((state2reg_fun (run_ir prog st) r) = ((f (state2reg_fun st)) r))) /\
  (!f1 f2. (!q. MEM q input_regs_list ==> (f1 (FST q) = f2 (FST q))) ==>
           (!r. MEM r oregs_words ==> (f f1 r = f f2 r))) /\
  ([(0w:word4, rv0); (1w:word4, rv1); (2w:word4, rv2); (3w:word4, rv3);
   (4w:word4, rv4); (5w:word4, rv5); (6w:word4, rv6); (7w:word4, rv7);
   (8w:word4, rv8); (9w:word4, rv9); (10w:word4, rv10); (11w:word4, rv11);
   (12w:word4, rv12); (13w:word4, rv13); (14w:word4, rv14)] = regs_list) /\
  (!x. MEM x oregs ==> ~MEM x uregs) /\
  (MAP MREG2REG uregs = uregs_words) /\
  (MAP MREG2REG oregs = oregs_words) /\
  (FILTER (\x. ~ (MEM (FST x) uregs_words)) regs_list = input_regs_list) /\
  ((FILTER (\x. (MEM (FST x) oregs_words)) (MAP (\(r, v). (r, f (LIST_TO_FUN 0w regs_list) r)) regs_list)) = output_regs_list) /\
  (FILTER (\x. ~(MEM x oregs_words)) (MAP FST input_regs_list) = unknown_changed_regs_list)
   ) ==>

   ARM_PROG (spec_list (MAP (\(x,y). (x, SOME y)) input_regs_list) [] (T, stat) (F, ir1) (F, ir2) (F, ir3)) (MAP enc tprog) {} (
      SEP_EXISTS stat. (spec_list (APPEND (MAP (\(x,y). (x, SOME y)) output_regs_list) (MAP (\x. (x, NONE)) unknown_changed_regs_list)) [] (T, stat) (F, ir1) (F,ir2) (F,ir3))) {}``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [GSYM ARM_PROG_INTRO1, dimindex_24, LENGTH_MAP, SPEC_LIST___MS_PC, SEP_EXISTS_ABSORB_STAR] THEN
SIMP_TAC std_ss [ARM_RUN_SEMANTICS, SEP_EXISTS_THM, LET_THM, spec_list_thm] THEN
SIMP_TAC (list_ss++spec_list_expand_ss) [LENGTH_MAP, arm_instTheory.ALL_DISJOINT_def,
   MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, ELIM_PFORALL_PEXISTS] THEN
`(\x. FST ((\(x:REGISTER,y:DATA). (x,SOME y)) x)) = FST` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [FUN_EQ_THM, ELIM_PFORALL_PEXISTS]
) THEN
ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN
REPEAT STRIP_TAC THEN
ASSUME_TAC (SIMP_RULE std_ss [dimindex_24] TRANSLATION_SPEC_thm) THEN
Q_SPECL_NO_ASSUM 0 [`prog`, `\st st'. (EVERY (\r. st' r = f st r) oregs_words /\ EVERY (\r. ~(r = 15w) ==> (st' r = st r)) uregs_words)`, `s`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
   Q_TAC GSYM_DEF_TAC `uregs_words` THEN
   ASM_SIMP_TAC std_ss [EVERY_MEM] THEN
   FULL_SIMP_TAC std_ss [SET_EQ_SUBSET, UNCHANGED_THM, toREG_def, read_thm, EVERY_MEM, MEM_MAP, MREG2REG_def, armTheory.FETCH_PC_def, arm_progTheory.reg_def, GSYM ms_sem_THM] THEN

   REPEAT STRIP_TAC THEN
   `?st'. (run_ir prog st) = st'` by PROVE_TAC[] THEN
   Cases_on `st` THEN Cases_on `st'` THEN
   Q_TAC GSYM_DEF_TAC `r` THEN
   ASM_SIMP_TAC std_ss [state2reg_fun_def] THEN
   `q ' r = read (run_ir prog (q,r')) (REG (index_of_reg y))` by METIS_TAC[] THEN
   ASM_REWRITE_TAC[read_thm]
) THEN
FULL_SIMP_TAC std_ss [xR_list_sem_SOME] THEN
Q.EXISTS_TAC `step_num` THEN
ASM_SIMP_TAC std_ss [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, xR_list_sem_APPEND,
   xR_list_sem_NONE, xR_list_sem_SOME] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC list_ss [arm_progTheory.reg_def, armTheory.FETCH_PC_def] THEN
   SIMP_TAC list_ss [pcINC_def,
      wLENGTH_def, pcADD_def, addr32_ADD, WORD_ADD_COMM, WORD_EQ_ADD_LCANCEL,
      addr32_n2w],

   Q.PAT_ASSUM `EVERY P oregs_words` MP_TAC THEN
   Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
   ASM_SIMP_TAC list_ss [EVERY_MEM, MEM_FILTER, MEM_MAP, ELIM_PFORALL_PEXISTS,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   Q.PAT_ASSUM `arm_mem_state2reg_fun X p1 = Y` MP_TAC THEN
   `?p1'. p1 = MREG2REG p1'` by METIS_TAC[MEM_MAP] THEN
   ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [arm_mem_state2reg_fun2REG_READ, arm_progTheory.reg_def, state_mode_def, state_mode_def, MREG_NOT_PC] THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `!f1 f2. P f1 f2` (fn thm => MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] thm)) THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `q` THEN
   `~(q' = 15w)` by PROVE_TAC[] THEN
   RES_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [arm_mem_state2reg_fun_def, LET_THM, LIST_TO_FUN_def,
      arm_progTheory.reg_def, armTheory.REG_READ_def, state_mode_def] THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `MEM (q', r) input_regs_list` MP_TAC THEN
   Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `regs_list` THEN
   ASM_SIMP_TAC std_ss [MEM_FILTER, MEM, LEFT_AND_OVER_OR, DISJ_IMP_THM, LIST_TO_FUN_def,
      n2w_11, dimword_4],


   PROVE_TAC[ms_sem_MEMORY],
   METIS_TAC[PAIR],

   POP_ASSUM MP_TAC THEN
   Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `regs_list` THEN
   ASM_SIMP_TAC std_ss [MEM_FILTER, MEM_MAP, ELIM_PFORALL_PEXISTS, MEM, n2w_11, dimword_4],

   POP_ASSUM MP_TAC THEN
   Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `regs_list` THEN
   ASM_SIMP_TAC std_ss [MEM_FILTER, MEM_MAP, ELIM_PFORALL_PEXISTS, MEM, n2w_11, dimword_4],




   SIMP_TAC std_ss [ALL_DISTINCT_APPEND] THEN
   Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `regs_list` THEN
   ASM_SIMP_TAC std_ss [] THEN

   let
      val MAP_ID = prove (``!l. MAP (\x. x) l = l``,
         Induct_on `l` THEN ASM_SIMP_TAC list_ss []);
      val MAP_FST = prove (``!l l2. (MAP FST (FILTER (\(x :REGISTER # DATA). MEM (FST x) l2) l)) =
                       FILTER (\x. MEM x l2) (MAP FST l)``,
      Induct_on `l` THEN ASM_SIMP_TAC list_ss [COND_RATOR, COND_RAND]);
      val MAP_FST2 = prove (``!l l2. (MAP FST (FILTER (\x. ~MEM (FST x) l2) l)) =
                       FILTER (\x. ~MEM x l2) (MAP FST l)``,
      Induct_on `l` THEN ASM_SIMP_TAC list_ss [COND_RATOR, COND_RAND]);
      val PAIR_BETA = prove (``(\(x, y). P x y) x = P (FST x) (SND x)``,
         Cases_on `x` THEN SIMP_TAC std_ss [])
   in
      ASM_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF, MAP_ID, MAP_FST, MAP_FST2, PAIR_BETA, FILTER_FILTER]
   end THEN

   SIMP_TAC std_ss [MAP, MEM_FILTER] THEN

   MATCH_MP_TAC (
   prove (``ALL_DISTINCT l ==> (ALL_DISTINCT (FILTER P1 l) /\
                                ALL_DISTINCT (FILTER P2 l))``, PROVE_TAC[ALL_DISTINCT_IMPLIES_FILTER])) THEN

   SIMP_TAC std_ss [ALL_DISTINCT, MEM, n2w_11, dimword_4],



   Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `output_regs_list` THEN
   Q_TAC GSYM_DEF_TAC `unknown_changed_regs_list` THEN
   ASM_SIMP_TAC list_ss [EXTENSION, IN_LIST_TO_SET, MEM_MAP, ELIM_PFORALL_PEXISTS, MEM_FILTER,
      GSYM RIGHT_EXISTS_AND_THM] THEN
   SUBGOAL_TAC `!x. MEM x oregs_words ==> ~(MEM x uregs_words)` THEN1 (
      Q_TAC GSYM_DEF_TAC `oregs_words` THEN
      Q_TAC GSYM_DEF_TAC `uregs_words` THEN
      ASM_SIMP_TAC std_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM, MREG2REG_11]
   ) THEN
   POP_ASSUM MP_TAC THEN
   REPEAT WEAKEN_HD_TAC THEN
   METIS_TAC[],



   ASM_SIMP_TAC std_ss [arm2set''_EQ, IN_LIST_TO_SET, MEM, mem_byte_def, arm_progTheory.mem_def,
      owrt_visible_def, set_status_def, arm_evalTheory.CPSR_READ_WRITE,
      arm_evalTheory.CPSR_WRITE_WRITE, arm_evalTheory.CPSR_WRITE_READ,
      arm_evalTheory.SET_NZCV_IDEM, arm_progTheory.reg_def, MEM_MAP,
      ELIM_PFORALL_PEXISTS] THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_TAC `MEM r uregs_words` THEN1 (
      CCONTR_TAC THEN
      Q.PAT_ASSUM `!p2. ~(MEM (r, p2) input_regs_list)` MP_TAC THEN
      Q_TAC GSYM_DEF_TAC `input_regs_list` THEN
      Q_TAC GSYM_DEF_TAC `regs_list` THEN
      ASM_SIMP_TAC std_ss [MEM_FILTER, MEM, EXISTS_OR_THM] THEN
      Q.PAT_ASSUM `~(r = 15w)` MP_TAC THEN
      REPEAT WEAKEN_HD_TAC  THEN
      `r IN UNIV` by REWRITE_TAC [IN_UNIV] THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC std_ss [WORD_UNIV_IMAGE_COUNT, IN_IMAGE, dimword_4] THEN
      REWRITE_TAC[COUNT_SUC, IN_INSERT, (REDEPTH_CONV numLib.num_CONV) ``16``] THEN
      SIMP_TAC std_ss [COUNT_ZERO, NOT_IN_EMPTY, LEFT_AND_OVER_OR, EXISTS_OR_THM] THEN
      SIMP_TAC std_ss [DISJ_IMP_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   RES_TAC THEN
   POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [arm_mem_state2reg_fun_def, LET_THM] THEN
   ASM_SIMP_TAC std_ss [LET_THM,
      arm_evalTheory.CPSR_WRITE_READ, arm_evalTheory.DECODE_IFMODE_SET_NZCV,
      armTheory.REG_READ_def, state_mode_def]
])





val _ = export_theory();
