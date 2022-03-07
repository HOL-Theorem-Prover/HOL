(* ===================================================================== *)
(* 22 April 2018 - adapted to HOL 4                                      *)

(* ==================================================================== *)
(* 14 June 1989 - modified for HOL88                                    *)

(* ==================================================================== *)
(* Jeff Joyce, University of Cambridge, 1 November 1988                 *)
(*                                                                      *)
(* Derive results of executing microinstructions sequences implementing *)
(* machine instructions.                                                *)

open HolKernel boolLib bossLib Parse
open proofManagerLib

val _ = new_theory "tamarackProof2";

open arithmeticTheory stringTheory pairTheory prim_recTheory

local
  open tamarackTheory tamarackProof1Theory
in
end

fun definition x y = SPEC_ALL (DB.fetch x y);
fun theorem x y = DB.fetch x y;

val Bits = definition "tamarack" "Bits";
val Inst = definition "tamarack" "Inst";
val Opc = definition "tamarack" "Opc";
val Addr = definition "tamarack" "Addr";
val NextState = definition "tamarack" "NextState";
val Behaviour = definition "tamarack" "Behaviour";

val MPC_0_THM = theorem "tamarackProof1" "MPC_0_THM";
val MPC_1_THM = theorem "tamarackProof1" "MPC_1_THM";
val MPC_2_THM = theorem "tamarackProof1" "MPC_2_THM";
val MPC_3_THM = theorem "tamarackProof1" "MPC_3_THM";
val MPC_4_THM = theorem "tamarackProof1" "MPC_4_THM";
val MPC_5_THM = theorem "tamarackProof1" "MPC_5_THM";
val MPC_6_THM = theorem "tamarackProof1" "MPC_6_THM";
val MPC_7_THM = theorem "tamarackProof1" "MPC_7_THM";
val MPC_8_THM = theorem "tamarackProof1" "MPC_8_THM";
val MPC_9_THM = theorem "tamarackProof1" "MPC_9_THM";
val MPC_10_THM = theorem "tamarackProof1" "MPC_10_THM";
val MPC_11_THM = theorem "tamarackProof1" "MPC_11_THM";
val MPC_12_THM = theorem "tamarackProof1" "MPC_12_THM";
val MPC_13_THM = theorem "tamarackProof1" "MPC_13_THM";
val MPC_14_THM = theorem "tamarackProof1" "MPC_14_THM";

val DIV_THM = prove (``!m n. n < m ==> !k. (((k * m) + n) DIV m) = k``,
  ACCEPT_TAC DIV_MULT)

val PAIR_EQ_THM = theorem "tamarackProof1" "PAIR_EQ_THM";

val VAL_TAC = PURE_ONCE_REWRITE_TAC [LET_DEF] THEN BETA_TAC;
val VAL_RULE = BETA_RULE o (PURE_ONCE_REWRITE_RULE [LET_DEF]);


fun HOL_IMP_RES_THEN ttac thm =
  IMP_RES_THEN (HOL_IMP_RES_THEN ttac) thm handle HOL_ERR _ => ttac thm

fun FILTER_IMP_RES_THEN f ttac =
        HOL_IMP_RES_THEN
          (fn thm => if f (concl thm) then (ttac thm) else ALL_TAC);
fun FILTER_IMP_RES_TAC f = FILTER_IMP_RES_THEN f ASSUME_TAC;

val MATCH_GOAL_TAC : thm_tactic = fn impthm => fn (asl,tm):goal =>
        let
        val match = ((PART_MATCH (snd o dest_imp)) impthm) tm
        in
        ([(asl,fst (dest_imp (concl match)))],fn [th] => MP match th)
        end handle HOL_ERR _ => failwith "MATCH_GOAL_TAC";

fun sum_CONV tm =
        if not ((rator (rator tm)) = ``$+``) then failwith "sum_CONV" else
        let val [n,m] = map numSyntax.int_of_term [rand (rator tm),rand tm] in
        TAC_PROOF (([],``^tm = ^(numSyntax.term_of_int (n+m))``),
          CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
          REWRITE_TAC [ADD_CLAUSES])
        end;

fun not_eq_CONV tm =
        if not (is_eq tm) then failwith "not_eq_CONV" else
        let
        val [n,m] = map numSyntax.int_of_term [rand (rator tm),rand tm] in
        if m = n then failwith "not_eq_CONV" else
        TAC_PROOF (([],``^tm = F``),
          CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
          REWRITE_TAC [INV_SUC_EQ,numTheory.NOT_SUC])
        end;

val nextstate = VAL_RULE NextState;

val DIV_2_EXP_0_THM = TAC_PROOF (
        ([],``!n. n DIV (2 EXP 0) = n``),
        MP_TAC (MATCH_MP DIV_THM (REWRITE_RULE [ADD1] (SPEC ``0`` LESS_0))) THEN
        REWRITE_TAC [EXP,ADD_CLAUSES,MULT_CLAUSES]);

fun EXEC_MPC_TAC mpc_thm tm tac =
        FILTER_IMP_RES_THEN is_eq MP_TAC mpc_thm THEN
        SUBST1_TAC
          (SYM (REWRITE_RULE [ADD1,ADD_ASSOC] (DEPTH_CONV numLib.num_CONV tm))) THEN
        tac THEN
        DISCH_THEN (STRIP_ASSUME_TAC o (PURE_REWRITE_RULE [PAIR_EQ_THM]));

val EXEC_INST_FETCH_TAC =
        PURE_REWRITE_TAC [Opc,Inst] THEN
        REPEAT (FIRST [GEN_TAC,DISCH_THEN STRIP_ASSUME_TAC]) THEN
        EXEC_MPC_TAC MPC_0_THM ``t+1`` ALL_TAC THEN
        EXEC_MPC_TAC MPC_1_THM ``t+2`` ALL_TAC THEN
        EXEC_MPC_TAC MPC_2_THM ``t+3``
          (FILTER_ASM_REWRITE_TAC is_eq [Bits,DIV_2_EXP_0_THM] THEN
           CONV_TAC (DEPTH_CONV sum_CONV));

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 0) /\
            (acc t = 0)
            ==>
            (mpc (t+5) = 0) /\
            ((mem (t+5),pc (t+5),acc (t+5)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_3_THM ``t+4`` (ASM_REWRITE_TAC []));
expandf (EXEC_MPC_TAC MPC_4_THM ``t+5`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);

val JZR_T_INST_THM = save_thm ("JZR_T_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 0) /\
            ~(acc t = 0)
            ==>
            (mpc (t+6) = 0) /\
            ((mem (t+6),pc (t+6),acc (t+6)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_3_THM ``t+4`` (ASM_REWRITE_TAC []));
expandf (EXEC_MPC_TAC MPC_10_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+6`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);

val JZR_F_INST_THM = save_thm ("JZR_F_INST_THM",top_thm());
val _ = drop();


set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 1)
            ==>
            (mpc (t+4) = 0) /\
            ((mem (t+4),pc (t+4),acc (t+4)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_4_THM ``t+4`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val JMP_INST_THM = save_thm ("JMP_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 2)
            ==>
            (mpc (t+8) = 0) /\
            ((mem (t+8),pc (t+8),acc (t+8)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_5_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_12_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_14_THM ``t+6`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_10_THM ``t+7`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+8`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val ADD_INST_THM = save_thm ("ADD_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 3)
            ==>
            (mpc (t+8) = 0) /\
            ((mem (t+8),pc (t+8),acc (t+8)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_6_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_13_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_14_THM ``t+6`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_10_THM ``t+7`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+8`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val SUB_INST_THM = save_thm ("SUB_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 4)
            ==>
            (mpc (t+6) = 0) /\
            ((mem (t+6),pc (t+6),acc (t+6)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_7_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_10_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+6`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val LD_INST_THM = save_thm ("LD_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 5)
            ==>
            (mpc (t+6) = 0) /\
            ((mem (t+6),pc (t+6),acc (t+6)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_8_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_10_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+6`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val ST_INST_THM = save_thm ("ST_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 6)
            ==>
            (mpc (t+6) = 0) /\
            ((mem (t+6),pc (t+6),acc (t+6)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_9_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_10_THM ``t+5`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+6`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val NOP1_INST_THM = save_thm ("NOP1_INST_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) /\
            (Opc n (Inst n (mem t,pc t)) = 7)
            ==>
            (mpc (t+5) = 0) /\
            ((mem (t+5),pc (t+5),acc (t+5)) =
              NextState n (mem t,pc t,acc t))``);

expandf EXEC_INST_FETCH_TAC;
expandf (EXEC_MPC_TAC MPC_10_THM ``t+4`` ALL_TAC);
expandf (EXEC_MPC_TAC MPC_11_THM ``t+5`` ALL_TAC);
expandf (ASM_REWRITE_TAC [nextstate,Inst,Opc,Addr,Bits,DIV_2_EXP_0_THM]);
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));
expandf (REWRITE_TAC []);

val NOP2_INST_THM = save_thm ("NOP2_INST_THM",top_thm());
val _ = drop();

export_theory ();
