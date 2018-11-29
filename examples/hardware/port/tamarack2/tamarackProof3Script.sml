(* ===================================================================== *)
(* 22 April 2018 - adapted to HOL 4                                      *)

(* ==================================================================== *)
(* 14 June 1989 - modified for HOL88                                    *)

(* ==================================================================== *)
(* Jeff Joyce, University of Cambridge, 1 November 1988                 *)
(*                                                                      *)
(* Combine results for each machine instructions to prove top-level     *)
(* correctness theorem.                                                 *)


open HolKernel boolLib bossLib Parse
open proofManagerLib

val _ = new_theory "tamarackProof3";

open arithmeticTheory stringTheory pairTheory prim_recTheory

local
  open tamarackTheory tamarackProof1Theory tamarackProof2Theory
in
end

fun definition x y = SPEC_ALL (DB.fetch x y);
fun theorem x y = DB.fetch x y;

val MicroCycles = new_definition (
        "MicroCycles",
        ``MicroCycles n (mem,pc,acc) =
          let opc = Opc n (Inst n (mem,pc)) in
          (if (opc = 0) then (if (acc = 0) then 5 else 6) else
           if (opc = 1) then 4 else
           if (opc = 2) then 8 else
           if (opc = 3) then 8 else
           if (opc = 4) then 6 else
           if (opc = 5) then 6 else
           if (opc = 6) then 6 else
                             5)``);

val REV_TimeOfCycle = new_recursive_definition
   {name = "REV_TimeOfCycle",
    rec_axiom = num_Axiom,
    def = ``(REV_TimeOfCycle 0 n mem pc acc = 0) /\
         (REV_TimeOfCycle (SUC t) n mem pc acc =
          let prev = (REV_TimeOfCycle t n mem pc acc) in
          (prev + (MicroCycles n (mem prev,pc prev,acc prev))))``};

val TimeOfCycle = new_definition (
        "TimeOfCycle",
        ``TimeOfCycle n (mem,pc,acc) t = REV_TimeOfCycle t n mem pc acc``);

val JZR_T_INST_THM = theorem "tamarackProof2" "JZR_T_INST_THM";
val JZR_F_INST_THM = theorem "tamarackProof2" "JZR_F_INST_THM";
val JMP_INST_THM = theorem "tamarackProof2" "JMP_INST_THM";
val ADD_INST_THM = theorem "tamarackProof2" "ADD_INST_THM";
val SUB_INST_THM = theorem "tamarackProof2" "SUB_INST_THM";
val LD_INST_THM = theorem "tamarackProof2" "LD_INST_THM";
val ST_INST_THM = theorem "tamarackProof2" "ST_INST_THM";
val NOP1_INST_THM = theorem "tamarackProof2" "NOP1_INST_THM";
val NOP2_INST_THM = theorem "tamarackProof2" "NOP2_INST_THM";

val Opc = definition "tamarack" "Opc";
val Inst = definition "tamarack" "Inst";
val Behaviour = definition "tamarack" "Behaviour";

val th1 = prove(``!n. 0 < (2 EXP n)``,
  GEN_TAC THEN
  MP_TAC (SPECL [``n:num``, ``1``] arithmeticTheory.ZERO_LESS_EXP) THEN
  SIMP_TAC std_ss []);

val MOD_LESS_THM = theorem "arithmetic" "MOD_LESS";

val VAL_TAC = PURE_ONCE_REWRITE_TAC [LET_DEF] THEN BETA_TAC;
val VAL_RULE = BETA_RULE o (PURE_ONCE_REWRITE_RULE [LET_DEF]);

fun HOL_IMP_RES_THEN ttac thm =
  IMP_RES_THEN (HOL_IMP_RES_THEN ttac) thm handle HOL_ERR _ => ttac thm

fun not_eq_CONV tm =
        if not (is_eq tm) then failwith "not_eq_CONV" else
        let
        val [n,m] = map numSyntax.int_of_term [rand (rator tm),rand tm] in
        if m = n then failwith "not_eq_CONV" else
        TAC_PROOF (([],``^tm = F``),
          CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
          REWRITE_TAC [INV_SUC_EQ,numTheory.NOT_SUC])
        end;

val Opc_Cases_THM = TAC_PROOF ((
        [],
        ``!n inst.
          (Opc n inst = 0) \/
          (Opc n inst = 1) \/
          (Opc n inst = 2) \/
          (Opc n inst = 3) \/
          (Opc n inst = 4) \/
          (Opc n inst = 5) \/
          (Opc n inst = 6) \/
          (Opc n inst = 7)``),
        REPEAT GEN_TAC THEN
        PURE_ONCE_REWRITE_TAC [Opc] THEN
        SPEC_TAC (``inst DIV (2 EXP n)``,``m:num``) THEN
        GEN_TAC THEN
        MP_TAC (SPEC ``m:num`` (MATCH_MP MOD_LESS_THM (SPEC ``3`` th1))) THEN
        SPEC_TAC (``m MOD (2 EXP 3)``,``p:num``) THEN
        GEN_TAC THEN
        DISCH_THEN (MP_TAC o (CONV_RULE (REDEPTH_CONV numLib.num_CONV))) THEN
        PURE_REWRITE_TAC [numLib.num_CONV ``1``,EXP,MULT_CLAUSES,ADD_CLAUSES] THEN
        PURE_REWRITE_TAC [LESS_THM,NOT_LESS_0] THEN
        CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
        STRIP_TAC THEN
        ASM_REWRITE_TAC []);

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0)
            ==>
            let m = MicroCycles n (mem t,pc t,acc t) in
            ((mpc (t+m) = 0) /\
             ((mem (t+m),pc (t+m),acc (t+m)) =
              NextState n (mem t,pc t,acc t)))``);

expandf (REPEAT STRIP_TAC THEN
        PURE_REWRITE_TAC [MicroCycles] THEN
        VAL_TAC);
expandf ((REPEAT_TCL DISJ_CASES_THEN) ASSUME_TAC
          (SPECL [``n:time``,``Inst n (mem (t:time),pc t)``] Opc_Cases_THM) THEN
        ASM_REWRITE_TAC [] THEN
        CONV_TAC (DEPTH_CONV not_eq_CONV) THEN
        REWRITE_TAC [] THENL [
          DISJ_CASES_TAC (SPEC ``acc (t:time) = 0`` EXCLUDED_MIDDLE) THEN
          IMP_RES_THEN IMP_RES_TAC JZR_T_INST_THM THEN
          IMP_RES_THEN IMP_RES_TAC JZR_F_INST_THM THEN
          ASM_REWRITE_TAC [],
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC JMP_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC ADD_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC SUB_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC LD_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC ST_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC NOP1_INST_THM,
          CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC NOP2_INST_THM]);

val EVERY_INST_THM = save_thm ("EVERY_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
          (mpc 0 = 0)
          ==>
          !t. mpc (TimeOfCycle n (mem,pc,acc) t) = 0``);

expandf (REPEAT GEN_TAC THEN
        STRIP_TAC THEN
        PURE_ONCE_REWRITE_TAC [TimeOfCycle] THEN
        numLib.INDUCT_TAC THENL [
          ASM_REWRITE_TAC [REV_TimeOfCycle],
          PURE_REWRITE_TAC [VAL_RULE REV_TimeOfCycle] THEN
          IMP_RES_TAC (VAL_RULE EVERY_INST_THM)]);

val ALWAYS_MPC_0_THM = save_thm ("ALWAYS_MPC_0_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
          (mpc 0 = 0)
          ==>
          let f = TimeOfCycle n (mem,pc,acc) in
          Behaviour n (mem o f,pc o f,acc o f)``);

expandf (PURE_REWRITE_TAC [Behaviour, combinTheory.o_DEF] THEN
        VAL_TAC THEN
        REPEAT STRIP_TAC);
expandf (PURE_REWRITE_TAC [numLib.num_CONV ``1``,ADD_CLAUSES] THEN
        PURE_REWRITE_TAC [TimeOfCycle,VAL_RULE REV_TimeOfCycle] THEN
        PURE_ONCE_REWRITE_TAC [GSYM TimeOfCycle]);
expandf (HOL_IMP_RES_THEN (ASSUME_TAC o (SPEC ``t:num``)) ALWAYS_MPC_0_THM);
expandf (IMP_RES_TAC (VAL_RULE EVERY_INST_THM));

val CORRECTNESS_THM = save_thm ("CORRECTNESS_THM",top_thm());
val _ = drop();

export_theory ();
