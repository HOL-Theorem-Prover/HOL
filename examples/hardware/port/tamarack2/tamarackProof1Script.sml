(* ===================================================================== *)
(* 21 April 2018 - adapted to HOL 4                                      *)

(* ===================================================================== *)
(* 14 June 1989 - modified for HOL88                                     *)

(* ===================================================================== *)
(* Jeff Joyce, University of Cambridge, 1 November 1988                  *)
(*                                                                       *)
(* Derive results of executing individual microinstructions.             *)


open HolKernel boolLib bossLib Parse
open proofManagerLib

val _ = new_theory "tamarackProof1";

open arithmeticTheory stringTheory pairTheory prim_recTheory

local
  open tamarackTheory
in
end

fun definition x y = SPEC_ALL (DB.fetch x y);

val ADDn = definition "tamarack" "ADDn";
val Bits = definition "tamarack" "Bits";
val PWR = definition "tamarack" "PWR";
val GND = definition "tamarack" "GND";
val AND = definition "tamarack" "AND";
val OR = definition "tamarack" "OR";
val MUX = definition "tamarack" "MUX";
val BITS = definition "tamarack" "BITS";
val TNZ = definition "tamarack" "TNZ";
val HWC = definition "tamarack" "HWC";
val ADDER = definition "tamarack" "ADDER";
val ALU = definition "tamarack" "ALU";
val DEL = definition "tamarack" "DEL";
val REG = definition "tamarack" "REG";
val MEM = definition "tamarack" "MEM";
val CheckCntls = definition "tamarack" "CheckCntls";
val DataPath = definition "tamarack" "DataPath";
val Cntls = definition "tamarack" "Cntls";
val NextMpc = definition "tamarack" "NextMpc";
val Microcode = definition "tamarack" "Microcode";
val ROM = definition "tamarack" "ROM";
val Decoder = definition "tamarack" "Decoder";
val MpcUnit = definition "tamarack" "MpcUnit";
val CntlUnit = definition "tamarack" "CntlUnit";
val Tamarack = definition "tamarack" "Tamarack";

val LESS_MOD_THM = DB.fetch "arithmetic" "LESS_MOD";
val LESS_LESS_MONO = DECIDE ``!m n p q. (m < p) /\ (n < q) ==> ((m + n) < (p + q))``;
val MOD_LESS_THM = DB.fetch "arithmetic" "MOD_LESS";

val MATCH_GOAL_TAC : thm_tactic = fn impthm => fn (asl,tm):goal =>
        let
        val match = ((PART_MATCH (snd o dest_imp)) impthm) tm
        in
        ([(asl,fst (dest_imp (concl match)))],fn [th] => MP match th)
        end handle HOL_ERR _ => failwith "MATCH_GOAL_TAC";

val PAIR_EQ_THM = store_thm (
        "PAIR_EQ_THM",
        ``!a:'a. !b:'b. !c:'a. !d:'b. ((a,b) = (c,d)) = ((a = c) /\ (b = d))``,
        REPEAT STRIP_TAC THEN
        EQ_TAC THENL
        [DISCH_THEN
          (fn thm =>
            REWRITE_TAC [
              PURE_REWRITE_RULE [FST,SND]
                (CONJ
                  (AP_TERM ``FST:('a # 'b)->'a`` thm)
                  (AP_TERM ``SND:('a # 'b)->'b`` thm))]),
         DISCH_TAC THEN
         ASM_REWRITE_TAC []]);

fun not_eq_CONV tm =
        if not (is_eq tm) then failwith "not_eq_CONV" else
        let
        val [n,m] = map numSyntax.int_of_term [rand (rator tm),rand tm] in
        if m = n then failwith "not_eq_CONV" else
        TAC_PROOF (([],``^tm = F``),
          CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
          REWRITE_TAC [INV_SUC_EQ,numTheory.NOT_SUC])
        end;

(* The two steps could take quite a long time ! *)

val thlist1 = map
        (fn n =>
          (REWRITE_RULE []
            (CONV_RULE (ONCE_DEPTH_CONV not_eq_CONV)
              (REWRITE_RULE []
                (SPEC (numSyntax.term_of_int n) (GEN ``n:num`` Microcode))))))
        [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15];

val Microcode_THMS = map
        ((REWRITE_RULE []) o
         (CONV_RULE (ONCE_DEPTH_CONV stringLib.string_EQ_CONV)) o
         (PURE_ONCE_REWRITE_RULE [Cntls,NextMpc]))
        thlist1;

val EXP_2_4 =
        PURE_REWRITE_RULE [MULT_CLAUSES, ADD_CLAUSES]
          (PURE_REWRITE_RULE [numLib.num_CONV ``1``, EXP]
            ((REDEPTH_CONV numLib.num_CONV) ``2 EXP 4``));

(* The following tactics correspond to the sequence of steps which take
   place when a microinstruction is executed:  tac1 - produce microcode
   ROM output; tac2 - generate next mpc state; tac3 - generate next data
   path state.  The last step, tac4, is used to simplify the mpc state. *)


val tac1 =
        PURE_REWRITE_TAC [Tamarack, CntlUnit, ROM] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_THEN (MP_TAC o (SPEC ``t:time``)) (fst (EQ_IMP_RULE Decoder)) THEN
        PURE_ASM_REWRITE_TAC [] THEN
        SUBST_TAC Microcode_THMS THEN
        DISCH_THEN (STRIP_ASSUME_TAC o (PURE_REWRITE_RULE [PAIR_EQ_THM]));

val tac2 =
        IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE MpcUnit)) THEN
        PURE_ONCE_REWRITE_TAC [AND,OR,MUX,HWC,ADDER,DEL] THEN
        DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) (fn thm => REWRITE_TAC [thm])) THEN
        ASM_REWRITE_TAC [];

val tac3 =
        IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE DataPath)) THEN
        PURE_ONCE_REWRITE_TAC [CheckCntls,MEM,REG,BITS,TNZ,ALU,PWR,GND] THEN
        DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) MP_TAC) THEN
        DISCH_THEN (MP_TAC o LIST_CONJ o (map (SPEC ``t:time``)) o CONJUNCTS) THEN
        ASM_REWRITE_TAC [PAIR_EQ_THM] THEN
        DISCH_THEN
          (fn thm => MP_TAC (REWRITE_RULE [CONJUNCT1 thm] (CONJUNCT2 thm))) THEN
        STRIP_TAC THEN
        ASM_REWRITE_TAC [];

val tac4 =
        REWRITE_TAC [ADDn] THEN
        SUBST1_TAC EXP_2_4 THEN
        CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
        PURE_REWRITE_TAC [ADD_CLAUSES] THEN
        MATCH_GOAL_TAC LESS_MOD_THM THEN
        REWRITE_TAC [LESS_MONO_EQ,LESS_0];

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 0) ==>
            ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1)) =
             (1,mem t,pc t,pc t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_0_THM = save_thm ("MPC_0_THM",top_thm ());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 1) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
             (2,mem t,pc t,acc t,mem t (Bits (0,n) (mar t))))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_1_THM = save_thm ("MPC_1_THM",top_thm());

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 2) ==>
            ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),ir (t+1)) =
             ((Bits (n,3) (ir t)) + 3,mem t,ir t,pc t,acc t,ir t))``);

expandf (tac1 THEN tac2 THEN tac3);

val th1 = prove (``!n. 0 < (2 EXP n)``,
  GEN_TAC >>
  MP_TAC (SPECL [``n:num``, ``1``] ZERO_LESS_EXP) >>
  SIMP_TAC arith_ss []
);

val th2 = TAC_PROOF (([],``3 < (2 EXP 3)``),
        CONV_TAC (REDEPTH_CONV numLib.num_CONV) THEN
        PURE_REWRITE_TAC [numLib.num_CONV ``1``,EXP] THEN
        PURE_REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES] THEN
        REWRITE_TAC [LESS_MONO_EQ,LESS_0]);

expandf (PURE_REWRITE_TAC [ADDn,Bits] THEN
        MATCH_GOAL_TAC LESS_MOD_THM THEN
        SUBST1_TAC (DEPTH_CONV numLib.num_CONV ``2 EXP 4``) THEN
        PURE_REWRITE_TAC [EXP,MULT_CLAUSES,ADD_CLAUSES] THEN
        SUBST1_TAC (SYM (numLib.num_CONV ``2``)) THEN
        ASSUME_TAC
          (SPEC ``(((ir:bus) t) DIV (2 EXP n))``
            (MATCH_MP MOD_LESS_THM (SPEC ``3`` th1))) THEN
        ASSUME_TAC th2 THEN
        PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
        IMP_RES_TAC LESS_LESS_MONO);

val MPC_2_THM = save_thm ("MPC_2_THM",top_thm());

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 3) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
             (((if ((acc t) = 0) then 4 else 10),mem t,pc t,acc t,ir t)))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf (BOOL_CASES_TAC ``(acc:bus) t = 0`` THEN
        tac4);

val MPC_3_THM = save_thm ("MPC_3_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 4) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (0,mem t,ir t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_4_THM = save_thm ("MPC_4_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 5) ==>
            ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
             (12,mem t,mar t,pc t,acc t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_5_THM = save_thm ("MPC_5_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 6) ==>
            ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
             (13,mem t,mar t,pc t,acc t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_6_THM = save_thm ("MPC_6_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 7) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (10,mem t,pc t,mem t (Bits (0,n) (mar t))))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_7_THM = save_thm ("MPC_7_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 8) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (10,Update (mem t,Bits (0,n) (mar t),acc t),pc t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_8_THM = save_thm ("MPC_8_THM",top_thm ());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 9) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (10,mem t,pc t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_9_THM = save_thm ("MPC_9_THM",top_thm ());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 10) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
             (11,mem t,pc t,acc t,INCn (n+3) (pc t)))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_10_THM = save_thm ("MPC_10_THM",top_thm ());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 11) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (0,mem t,buf t,acc t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_11_THM = save_thm ("MPC_11_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 12) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
             (14,mem t,pc t,acc t,
              ADDn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_12_THM = save_thm ("MPC_12_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 13) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
             (14,mem t,pc t,acc t,
              SUBn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_13_THM = save_thm ("MPC_13_THM",top_thm());
val _ = drop();

set_goal ([],
        ``!n mpc mem mar pc acc ir arg buf.
          Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
          ==>
          !t.
            (mpc t = 14) ==>
            ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
             (10,mem t,pc t,buf t))``);

expandf (tac1 THEN tac2 THEN tac3);
expandf tac4;

val MPC_14_THM = save_thm ("MPC_14_THM",top_thm());
val _ = drop();

val _ = export_theory ();
